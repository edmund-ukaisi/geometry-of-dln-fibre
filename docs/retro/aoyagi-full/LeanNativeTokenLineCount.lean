import Lean

open Lean
open Lean.Parser

def countLines (input : String) : Nat :=
  input.foldl (fun acc c => if c == '\n' then acc + 1 else acc) 1

def markLineRange (marks : Array Bool) (firstLine lastLine : Nat) : Array Bool := Id.run do
  let mut marks := marks
  for line in [firstLine:lastLine + 1] do
    if h : line < marks.size then
      marks := marks.set line true
  return marks

def markSyntaxRange (inputCtx : InputContext) (marks : Array Bool) (stx : Syntax) : Array Bool :=
  match stx.getRange? with
  | none => marks
  | some range =>
      if range.start == range.stop then
        marks
      else
        let stopPrev := inputCtx.prev range.stop
        let firstLine := (inputCtx.fileMap.toPosition range.start).line
        let lastLine := (inputCtx.fileMap.toPosition stopPrev).line
        markLineRange marks firstLine lastLine

def parserSucceededPast (startPos : String.Pos.Raw) (state : ParserState) : Bool :=
  !state.hasError && startPos < state.pos

def resetStateAt (state : ParserState) (pos : String.Pos.Raw) : ParserState :=
  { cache := state.cache, pos := pos }

def trySkipDocComment
    (inputCtx : InputContext) (pmctx : ParserModuleContext) (tokens : TokenTable)
    (state : ParserState) : Option ParserState :=
  let startPos := state.pos
  let moduleDocState := Command.moduleDoc.fn.run inputCtx pmctx tokens state
  if parserSucceededPast startPos moduleDocState then
    some (resetStateAt moduleDocState moduleDocState.pos)
  else
    let docState := Command.docComment.fn.run inputCtx pmctx tokens state
    if parserSucceededPast startPos docState then
      some (resetStateAt docState docState.pos)
    else
      none

partial def scanNativeTokens
    (inputCtx : InputContext) (pmctx : ParserModuleContext) (tokens : TokenTable)
    (state : ParserState) (marks : Array Bool) (errors : Nat) : Array Bool × Nat := Id.run do
  let state := whitespace.run inputCtx pmctx tokens state
  if inputCtx.atEnd state.pos then
    return (marks, errors)
  if let some state := trySkipDocComment inputCtx pmctx tokens state then
    return scanNativeTokens inputCtx pmctx tokens state marks errors
  let startPos := state.pos
  let parsed := tokenFn [] |>.run inputCtx pmctx tokens state
  if parsed.hasError || parsed.stxStack.size == 0 then
    let line := (inputCtx.fileMap.toPosition startPos).line
    let marks := markLineRange marks line line
    let nextPos := if h : inputCtx.atEnd startPos then startPos else inputCtx.next' startPos h
    let nextState : ParserState := { cache := parsed.cache, pos := nextPos }
    scanNativeTokens inputCtx pmctx tokens nextState marks (errors + 1)
  else
    let stx := parsed.stxStack.back
    let marks := markSyntaxRange inputCtx marks stx
    let nextState : ParserState := { cache := parsed.cache, pos := parsed.pos }
    scanNativeTokens inputCtx pmctx tokens nextState marks errors

def countNativeTokenLinesInString (env : Environment) (fileName input : String) : Nat × Nat :=
  let inputCtx := mkInputContext input fileName
  let pmctx : ParserModuleContext := { env := env, options := {} }
  let tokens := getTokenTable env
  let marks := Array.replicate (countLines input) false
  let state : ParserState := { cache := initCacheForInput input }
  let (marks, errors) := scanNativeTokens inputCtx pmctx tokens state marks 0
  (marks.foldl (fun acc marked => if marked then acc + 1 else acc) 0, errors)

def escapeField (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\t" "\\t" |>.replace "\n" "\\n"

def countFile (env : Environment) (path : String) : IO Unit := do
  let input ← IO.FS.readFile path
  let (lines, errors) := countNativeTokenLinesInString env path input
  IO.println s!"{escapeField path}\t{lines}\t{errors}"

def readPathList (path : String) : IO (List String) := do
  let input ← IO.FS.readFile path
  pure <| input.splitOn "\n" |>.filter (fun s => !s.isEmpty)

def nameFromString (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part => acc.str part) .anonymous

partial def parseArgs (moduleName : Name) (args : List String) : IO (Name × Option (List String)) := do
  match args with
  | [] => pure (moduleName, none)
  | "--module" :: moduleString :: rest =>
      parseArgs (nameFromString moduleString) rest
  | "--file-list" :: path :: [] =>
      pure (moduleName, some (← readPathList path))
  | "--file-list" :: _ :: _ =>
      throw <| IO.userError "--file-list must be the final argument pair"
  | paths =>
      pure (moduleName, some paths)

def main (args : List String) : IO UInt32 := do
  let (moduleName, paths?) ← parseArgs `Lean args
  match paths? with
  | none =>
      IO.eprintln "usage: lean --run LeanNativeTokenLineCount.lean [--module MOD] FILE..."
      IO.eprintln "   or: lean --run LeanNativeTokenLineCount.lean [--module MOD] --file-list FILELIST"
      pure 2
  | some paths =>
      let env ← importModules #[{ module := moduleName }] {} (loadExts := true)
      IO.println "path\tnative_token_loc\ttoken_errors"
      for path in paths do
        countFile env path
      pure 0

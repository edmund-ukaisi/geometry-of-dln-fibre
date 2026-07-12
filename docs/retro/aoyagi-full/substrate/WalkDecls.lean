import Lean

/-!
# WalkDecls — environment-walking decl dumper for the retro instrument

Walks the compiled Lean environment and emits one JSON file describing every declaration
whose defining module name starts with a given prefix (default `DLNFibre`). No theorem
proving: this is pure environment introspection (kind, module, file:line, pretty-printed
type, binder count, type/proof constant dependencies, transitive axioms).

Run from the `lean/` directory:

    lake env lean --run docs/retro/aoyagi-full/substrate/WalkDecls.lean \
      --module DLNFibre --prefix DLNFibre \
      --out ../docs/retro/aoyagi-full/substrate/decls.json \
      --generated "$(date -u +%Y-%m-%dT%H:%M:%SZ)"

Prototype against a small Mathlib namespace without building DLNFibre:

    lake env lean --run docs/retro/aoyagi-full/substrate/WalkDecls.lean \
      --module Mathlib.Analysis.MeanInequalities \
      --prefix Mathlib.Analysis.MeanInequalities --out /tmp/walk-test.json
-/

open Lean Meta

namespace WalkDecls

/-- Truncate a string to at most `n` characters, returning a `String`. -/
def truncStr (n : Nat) (s : String) : String := String.ofList (s.toList.take n)

/-- Escape a string for embedding inside a JSON string literal. -/
def jsonEscape (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    match c with
    | '"'  => out := out ++ "\\\""
    | '\\' => out := out ++ "\\\\"
    | '\n' => out := out ++ "\\n"
    | '\r' => out := out ++ "\\r"
    | '\t' => out := out ++ "\\t"
    | _ =>
      if c.val < 0x20 then
        let hex := String.ofList (Nat.toDigits 16 c.val.toNat)
        let padded := String.ofList (List.replicate (4 - hex.length) '0') ++ hex
        out := out ++ "\\u" ++ padded
      else
        out := out.push c
  return out

/-- A JSON string literal. -/
def jstr (s : String) : String := "\"" ++ jsonEscape s ++ "\""

/-- A JSON array of strings from `Name`s. -/
def jarrN (xs : Array Name) : String :=
  "[" ++ String.intercalate "," (xs.toList.map (fun n => jstr n.toString)) ++ "]"

/-- Count the leading `∀`/`Π` binders of a type (a hypothesis-count proxy). -/
partial def countForalls : Expr → Nat → Nat
  | .forallE _ _ b _, acc => countForalls b (acc + 1)
  | _, acc => acc

/-- Last-component name suffixes of compiler-generated declarations to skip
(those not already caught by `Name.isInternalDetail`). -/
def genSuffixes : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "binductionOn",
   "injEq", "sizeOf_spec", "noConfusion", "noConfusionType", "eq_def",
   "toCtorIdx", "fromArrays"]

/-- Is this an auto-generated declaration we should skip? -/
def isGenerated (n : Name) : Bool :=
  n.isInternalDetail ||
  (match n with
   | .str _ s => genSuffixes.contains s
   | _ => false)

/-- Convert a module name to its source path relative to the repo root. -/
def moduleToFile (n : Name) : String :=
  "lean/" ++ String.intercalate "/" (n.components.map toString) ++ ".lean"

/-- Convert a dotted string to a `Name`. -/
def strToName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part => acc.str part) .anonymous

/-- Build the JSON object for one declaration, or `none` if it should be skipped. -/
def processDecl (pfx : Name) (modName : Name) (fileRel : String)
    (n : Name) (ci : ConstantInfo) : MetaM (Option String) := do
  if isGenerated n then return none
  let env ← getEnv
  let kind? : Option String :=
    match ci with
    | .axiomInfo _  => some "axiom"
    | .thmInfo _    => some "theorem"
    | .opaqueInfo _ => some "opaque"
    | .defnInfo v   =>
        if Meta.isInstanceCore env n then some "instance"
        else if v.hints matches .abbrev then some "abbrev"
        else some "def"
    | .inductInfo _ => some (if isStructure env n then "structure" else "inductive")
    | _ => none
  let some kind := kind? | return none
  let stmt ← (do
      let f ← ppExpr ci.type
      pure (truncStr 2000 f.pretty))
    <|> pure (truncStr 2000 (toString ci.type))
  let nBinders := countForalls ci.type 0
  let depsType := ci.type.getUsedConstants.filter (fun d => pfx.isPrefixOf d && d != n)
  let depsProof := match ci.value? (allowOpaque := true) with
    | some val => val.getUsedConstants.filter (fun d => pfx.isPrefixOf d && d != n)
    | none => #[]
  let axs ← (do collectAxioms n) <|> pure #[]
  let line ← match (← findDeclarationRanges? n) with
    | some r => pure r.range.pos.line
    | none => pure 0
  let obj :=
    "{" ++
    "\"name\":" ++ jstr n.toString ++
    ",\"kind\":" ++ jstr kind ++
    ",\"module\":" ++ jstr modName.toString ++
    ",\"file\":" ++ jstr fileRel ++
    ",\"line\":" ++ toString line ++
    ",\"statement\":" ++ jstr stmt ++
    ",\"n_binders\":" ++ toString nBinders ++
    ",\"deps_type\":" ++ jarrN depsType ++
    ",\"deps_proof\":" ++ jarrN depsProof ++
    ",\"axioms\":" ++ jarrN axs ++
    "}"
  return some obj

/-- Walk every in-prefix module's declarations and assemble the full JSON document. -/
def walk (pfx : Name) (generated : String) : MetaM String := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modData := env.header.moduleData
  let mut objs : Array String := #[]
  for i in [0:modData.size] do
    let modName := mods[i]!
    if !pfx.isPrefixOf modName then continue
    let data := modData[i]!
    let fileRel := moduleToFile modName
    for (n, ci) in data.constNames.zip data.constants do
      match ← processDecl pfx modName fileRel n ci with
      | some obj => objs := objs.push obj
      | none => pure ()
  let metaObj :=
    "{\"generated\":" ++ jstr generated ++
    ",\"root_prefix\":" ++ jstr pfx.toString ++
    ",\"n\":" ++ toString objs.size ++ "}"
  let body := String.intercalate ",\n" objs.toList
  pure ("{\"_meta\":" ++ metaObj ++ ",\n\"decls\":[\n" ++ body ++ "\n]}\n")

partial def parseArgs (args : List String) (root pfx : Name) (out gen : String) :
    Name × Name × String × String :=
  match args with
  | [] => (root, pfx, out, gen)
  | "--module" :: v :: r    => parseArgs r (strToName v) pfx out gen
  | "--prefix" :: v :: r    => parseArgs r root (strToName v) out gen
  | "--out" :: v :: r       => parseArgs r root pfx v gen
  | "--generated" :: v :: r => parseArgs r root pfx out v
  | _ :: r                  => parseArgs r root pfx out gen

end WalkDecls

open WalkDecls in
/-- `unsafe` + `enableInitializersExecution`: `importModules (loadExts := true)` runs the imported
modules' `initialize` code through the interpreter, so notation/delab extensions fire and types
pretty-print idiomatically. Without it the pp falls back to raw `instHMul.hMul` forms. -/
unsafe def main (args : List String) : IO UInt32 := do
  let (root, pfx, out, gen) :=
    parseArgs args `DLNFibre `DLNFibre
      "../docs/retro/aoyagi-full/substrate/decls.json" "unknown"
  IO.eprintln s!"walk: import {root} | prefix {pfx} | out {out}"
  Lean.enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (loadExts := true)
  let opts : Options := ({} : Options).setBool `pp.universes false
  let coreCtx : Core.Context :=
    { fileName := "WalkDecls", fileMap := default, options := opts, maxHeartbeats := 0 }
  let coreState : Core.State := { env := env }
  let (json, _) ← ((walk pfx gen).run' {} {}).toIO coreCtx coreState
  IO.FS.writeFile out json
  IO.eprintln s!"walk: wrote {out} ({json.length} bytes)"
  pure 0

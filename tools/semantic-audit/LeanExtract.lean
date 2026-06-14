import Lean

open Lean

namespace SemanticAudit

def projectPrefix : Name := `DLNFibre

def isProjectName (name : Name) : Bool :=
  projectPrefix.isPrefixOf name

def isProjectModule (name : Name) : Bool :=
  isProjectName name

def moduleFor? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none =>
      if env.constants.map₂.contains declName then
        env.header.mainModule
      else
        none

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def constantValue? : ConstantInfo → Option Expr
  | .defnInfo info => some info.value
  | .thmInfo info => some info.value
  | .opaqueInfo info => some info.value
  | _ => none

def uniqueSortedNames (names : Array Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  for name in names do
    unless seen.contains name do
      seen := seen.insert name
      out := out.push name
  return out.qsort (fun a b => toString a < toString b)

def projectDepsOf (self : Name) (expr : Expr) : Array Name :=
  uniqueSortedNames <|
    expr.getUsedConstants.filter fun dep =>
      dep != self && isProjectName dep && !dep.isInternal

def namesJson (names : Array Name) : Json :=
  Json.arr <| names.map (fun name => Json.str (toString name))

def positionJson (pos : Position) : Json :=
  Json.mkObj [
    ("line", pos.line),
    ("column", pos.column)
  ]

def declarationRangeJson (range : DeclarationRange) : Json :=
  Json.mkObj [
    ("start", positionJson range.pos),
    ("end", positionJson range.endPos),
    ("start_utf16_column", range.charUtf16),
    ("end_utf16_column", range.endCharUtf16)
  ]

def declarationRangesJson : Option DeclarationRanges → Json
  | none => Json.null
  | some ranges =>
      Json.mkObj [
        ("range", declarationRangeJson ranges.range),
        ("selection_range", declarationRangeJson ranges.selectionRange)
      ]

def ppExprString (expr : Expr) : CoreM String := do
  let fmt ← Meta.MetaM.run' <| PrettyPrinter.ppExpr expr
  return fmt.pretty

def declarationJson (env : Environment) (name : Name) (info : ConstantInfo) : CoreM Json := do
  let typeString ← ppExprString info.toConstantVal.type
  let doc? ← findDocString? env name
  let ranges? ← findDeclarationRanges? name
  let moduleName := (moduleFor? env name).map toString |>.getD ""
  let typeDeps := projectDepsOf name info.toConstantVal.type
  let valueDeps :=
    match constantValue? info with
    | none => #[]
    | some value => projectDepsOf name value
  return Json.mkObj [
    ("name", toString name),
    ("kind", constantKind info),
    ("module", moduleName),
    ("is_internal", name.isInternal),
    ("type", typeString),
    ("doc", doc?.getD ""),
    ("source_range", declarationRangesJson ranges?),
    ("deps_type", namesJson typeDeps),
    ("deps_value", namesJson valueDeps),
    ("has_value", (constantValue? info).isSome)
  ]

def collectDeclarations : CoreM String := do
  let env ← getEnv
  let mut constants : Array (Name × ConstantInfo) := #[]
  for hMod : modIdx in *...env.header.moduleData.size do
    let moduleName := env.header.moduleNames[modIdx]!
    if isProjectModule moduleName then
      let moduleData := env.header.moduleData[modIdx]
      for hConst : constIdx in *...moduleData.constNames.size do
        let name := moduleData.constNames[constIdx]
        let info := moduleData.constants[constIdx]!
        if isProjectName name && !name.isInternal then
          constants := constants.push (name, info)
  constants := constants.qsort fun a b => toString a.1 < toString b.1
  let mut lines : Array String := #[]
  for (name, info) in constants do
    let json ← declarationJson env name info
    lines := lines.push (Json.compress json ++ "\n")
  return String.join lines.toList

end SemanticAudit

unsafe def withProjectEnv {α : Type} (f : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules #[{ module := `DLNFibre }] {} (trustLevel := 1024) fun env =>
    Prod.fst <$> Core.CoreM.toIO
      (ctx := { fileName := "<semantic-audit>", fileMap := default })
      (s := { env := env }) f

unsafe def main (args : List String) : IO UInt32 := do
  let outPath := args.headD ".semantic-audit/declarations.jsonl"
  let content ← withProjectEnv SemanticAudit.collectDeclarations
  IO.FS.writeFile outPath content
  IO.println s!"Wrote Lean declaration inventory to {outPath}"
  return 0

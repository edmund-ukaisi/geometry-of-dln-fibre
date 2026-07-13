import Lean

/-!
# WalkDecls — environment-walking decl dumper for the retro instrument

Walks the compiled Lean environment and emits one JSON file describing every declaration
whose defining module name starts with a given prefix (default `DLNFibre`). No theorem
proving: this is pure environment introspection (kind, module, file:line, pretty-printed
type, binder count, type/proof constant dependencies, transitive axioms).

Run from the `lean/` directory (paths are relative to `lean/`):

    lake env lean --run ../docs/retro/aoyagi-full/substrate/WalkDecls.lean \
      --module DLNFibre --prefix DLNFibre \
      --out ../docs/retro/aoyagi-full/substrate/decls.json \
      --generated "$(date -u +%Y-%m-%dT%H:%M:%SZ)"

Prototype against a small Mathlib namespace without building DLNFibre:

    lake env lean --run ../docs/retro/aoyagi-full/substrate/WalkDecls.lean \
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
   "injEq", "inj", "sizeOf_spec", "noConfusion", "noConfusionType", "eq_def",
   "toCtorIdx", "ctorIdx", "ctorElimType", "fromArrays", "congr_simp", "congr"]

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

/-- The dependency edges `Lean.collectAxioms` follows (type/value per constant kind). -/
def axEdges (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v  => v.type.getUsedConstants
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _   => #[]
  | .ctorInfo v   => v.type.getUsedConstants
  | .recInfo v    => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- Memoized transitive-axiom collector matching `Lean.collectAxioms` reachability.
The shared `cache` makes the whole walk near-linear instead of re-walking each decl's
(deep) closure per call. Cycles — every inductive ↔ its constructors form one — break to
`#[]`, and the node is still cached: the axioms of interest (`propext`, `Classical.choice`,
`Quot.sound`, `sorryAx`) are reached through proof-term DAG paths, and `sorryAx` sits
directly in a sorry-using decl's own value, so caching through a cycle does not drop them. -/
partial def reachAxioms (env : Environment) (cache : IO.Ref (Std.HashMap Name (Array Name)))
    (stack : NameSet) (c : Name) : IO (Array Name) := do
  if let some r := (← cache.get).get? c then return r
  if stack.contains c then return #[]
  let some ci := env.find? c | return #[]
  let stack := stack.insert c
  let mut seen : NameSet := {}
  let mut acc : Array Name := #[]
  if ci matches .axiomInfo _ then
    seen := seen.insert c
    acc := acc.push c
  for d in axEdges ci do
    if d != c then
      for a in (← reachAxioms env cache stack d) do
        unless seen.contains a do
          seen := seen.insert a
          acc := acc.push a
  cache.modify (·.insert c acc)
  return acc

/-- Build the JSON object for one declaration, or `none` if it should be skipped. -/
def processDecl (pfx : Name) (modName : Name) (fileRel : String)
    (cache : IO.Ref (Std.HashMap Name (Array Name)))
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
  let axs ← reachAxioms env cache {} n
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
  IO.eprintln s!"walk: env loaded ({modData.size} modules); scanning prefix {pfx}"
  let t0 ← IO.monoMsNow
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let mut objs : Array String := #[]
  let mut nSeen : Nat := 0
  for i in [0:modData.size] do
    let modName := mods[i]!
    if !pfx.isPrefixOf modName then continue
    let data := modData[i]!
    let fileRel := moduleToFile modName
    for (n, ci) in data.constNames.zip data.constants do
      -- Emit each constant only from its owning module. A name defined in two closure modules
      -- (e.g. the same short lemma name in two files) otherwise appears twice, and the
      -- name-keyed `findDeclarationRanges?` gives the phantom row the survivor's line.
      if let some j := env.getModuleIdxFor? n then
        if j.toNat != i then continue
      nSeen := nSeen + 1
      match ← processDecl pfx modName fileRel cache n ci with
      | some obj =>
        objs := objs.push obj
        if objs.size % 250 == 0 then
          IO.eprintln s!"walk: {objs.size} emitted / {nSeen} scanned ({(← IO.monoMsNow) - t0} ms)"
      | none => pure ()
  IO.eprintln s!"walk: finished — {objs.size} decls from {nSeen} scanned ({(← IO.monoMsNow) - t0} ms)"
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
  let tImp ← IO.monoMsNow
  let env ← importModules #[{ module := root }] {} (loadExts := true)
  IO.eprintln s!"walk: import+init done ({(← IO.monoMsNow) - tImp} ms)"
  let opts : Options := ({} : Options).setBool `pp.universes false
  let coreCtx : Core.Context :=
    { fileName := "WalkDecls", fileMap := default, options := opts, maxHeartbeats := 0 }
  let coreState : Core.State := { env := env }
  let (json, _) ← ((walk pfx gen).run' {} {}).toIO coreCtx coreState
  IO.FS.writeFile out json
  IO.eprintln s!"walk: wrote {out} ({json.length} bytes)"
  pure 0

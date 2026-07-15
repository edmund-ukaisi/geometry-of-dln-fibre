import Meta.Cordon

/-!
# `Meta.CordonAudit` — the env-reading cordon gate (used by `lake exe cordon-audit`)

The repo-gate frontend over the reusable core (`Meta.Cordon`). Loads a compiled Lean environment (the
imported `.olean`s of the library, with env-extensions — so `@[cited]` params and `@[blueprint]` tags
are readable) and runs four independent, deterministic checks over a chosen scope:

1. **UNACCOUNTED = ∅** — no public declaration rests on an untagged, non-foundational axiom.
2. **LOCATION + TAG** — every `axiom` in scope is `@[cited]` *and* declared in a located `…Cited` file.
3. **BLUEPRINT-LEAK = ∅** — no banked (non-`@[blueprint]`) declaration transitively rests on a
   `@[blueprint]` forecast (*banked never consumes a forecast*).
4. **MANIFEST** (`--manifest`) — the per-headline cite map, derived from the same `@[cited]` sources.

**Scoping is by module provenance.** DLNFibre's decls all live under the `DLNFibre` namespace and (its
source modules) under `lean/DLNFibre/**`, so a decl/axiom is in scope **iff its source module's name
has one of the scope prefixes as a prefix** — default `DLNFibre`. Module provenance (not decl
namespace) is used so the scope is robust to any bare-namespace helper authored under `DLNFibre/**`,
and never sweeps in Mathlib (whose source modules are `Mathlib.*`).

Emits a one-line machine-parseable summary (`UNACCOUNTED=n CITED=n LOCATION=n LEAKS=n`) + a human
listing, and signals violations to `main` (which sets a nonzero exit code). The `main` entry point +
`enableInitializersExecution`/`importModules` glue live in `scripts/CordonGate.lean` (the `lean_exe`
root); this module is the pure, importable analysis. NB: the cordon tooling lives in `lean/Meta/`,
OUTSIDE the audited scope (`DLNFibre/**`) and unscanned by `scripts/sorries`, so it does not audit
itself — the tooling is trusted, exercised by `scripts/cordon-test`.

Policy: `docs/policies/citation-cordon.md`.
-/

open Lean
open Meta.Cordon

namespace Meta.CordonAudit

/-- A located/tagging violation for a single axiom. -/
inductive AxiomViolation where
  /-- The axiom is not `@[cited]`-tagged. -/
  | untagged (ax : Name) (mod : Name)
  /-- The axiom is `@[cited]` but not declared in a located `…Cited` file. -/
  | misplaced (ax : Name) (mod : Name) (src : String)
  deriving Inhabited

/-- The full report of a cordon run over a scope. -/
structure CordonReport where
  /-- The **module-name** prefixes audited (module provenance, e.g. `#[DLNFibre]`). -/
  nsPrefixes : Array Name
  /-- Number of public declarations scanned. -/
  scanned : Nat
  /-- The in-scope declaration names scanned (the audit roots, sorted). -/
  roots : Array Name
  /-- The flat, sorted set of **unaccounted** axiom names across the scope (for the JSON report). -/
  unaccountedAxioms : Array Name
  /-- Declarations with a non-empty UNACCOUNTED set (decl, its unaccounted axioms). -/
  unaccounted : Array (Name × Array Name)
  /-- All distinct `@[cited]` axioms used across the scope, with sources (sorted). -/
  citedUsed : Array (Name × String)
  /-- Axiom location/tagging violations (sorted by axiom name). -/
  locationViolations : Array AxiomViolation
  /-- Banked (non-`@[blueprint]`) decls that LEAK: (decl, `@[blueprint]` forecasts in its deps). -/
  blueprintLeaks : Array (Name × Array Name)
  /-- All distinct `@[blueprint]`-tagged declarations in scope (informational, sorted). -/
  blueprintTagged : Array Name
  deriving Inhabited

/-- Does `n` live in a module whose name has one of the scope prefixes as a prefix, and is it a real
(non-internal) decl? Scoping is by **module provenance** (`sourceModule?`); `nsPrefixes` entries are
matched against the *module* name. -/
def inScope (env : Environment) (nsPrefixes : Array Name) (n : Name) : Bool :=
  (match sourceModule? env n with
    | some m => nsPrefixes.any (·.isPrefixOf m)
    | none => false) && !n.isInternalDetail

/-- Enumerate the in-scope declaration names of the environment (deterministic order: sorted). -/
def scopedDecls (env : Environment) (nsPrefixes : Array Name) : Array Name := Id.run do
  let mut r : Array Name := #[]
  for (n, _) in env.constants.toList do
    if inScope env nsPrefixes n then
      r := r.push n
  r.qsort Name.lt

/-- Enumerate **every** in-scope `axiom` declaration (sorted). Unlike `scopedDecls` this does NOT
filter internal/generated names — the location+tag check must see *every* axiom whose source module is
in scope (a compiler-generated axiom, e.g. from a sneaked-in `native_decide`, is exactly what should
surface). Scope is by module provenance, matching `scopedDecls`. -/
def scopedAxioms (env : Environment) (nsPrefixes : Array Name) : Array Name := Id.run do
  let mut r : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isAxiom then
      match sourceModule? env n with
      | some m => if nsPrefixes.any (·.isPrefixOf m) then r := r.push n
      | none => pure ()
  r.qsort Name.lt

/-- **Build the cordon report** over the scope. Runs the four checks. The UNACCOUNTED check uses the
**batched** collector (`collectAxiomsBatch`, one shared traversal over all in-scope roots — O(reachable
constants), not O(decls × depth)) to get the *union* of axioms the public API rests on; per-decl
attribution of an unaccounted axiom is a targeted second pass, taken **only** when the union has an
unaccounted axiom (a red gate — rare). The BLUEPRINT-LEAK check is symmetric: a batched union over the
*banked* roots first (fast path), per-root attribution only when the union is non-empty. The LOCATION +
TAG check is a direct axiom scan. -/
def buildReport (nsPrefixes : Array Name) : CoreM CordonReport := do
  let env ← getEnv
  let decls := scopedDecls env nsPrefixes
  -- Check 1 (fast path): the UNION of transitive axioms of all in-scope decls, one shared traversal.
  let unionAxioms := collectAxiomsBatch env decls
  let mut citedSet : Std.HashMap Name String := {}
  let mut unaccountedAx : Array Name := #[]
  for a in unionAxioms do
    if !isFoundational a then
      match getCitedSource? env a with
      | some src => citedSet := citedSet.insert a src
      | none => unaccountedAx := unaccountedAx.push a
  let citedUsed := (citedSet.toList.toArray.qsort (fun a b => Name.lt a.1 b.1))
  -- Per-decl attribution ONLY if the union has an unaccounted axiom (red gate).
  let mut unaccounted : Array (Name × Array Name) := #[]
  unless unaccountedAx.isEmpty do
    let badSet := unaccountedAx.foldl (·.insert ·) (∅ : Std.HashSet Name)
    for d in decls do
      let dax ← collectAxioms d
      let hits := (dax.filter badSet.contains).qsort Name.lt
      unless hits.isEmpty do
        unaccounted := unaccounted.push (d, hits)
  -- Check 2: LOCATION + TAG over every in-scope axiom.
  let mut locationViolations : Array AxiomViolation := #[]
  for a in scopedAxioms env nsPrefixes do
    let mod := (sourceModule? env a).getD Name.anonymous
    match getCitedSource? env a with
    | none =>
      -- an in-scope axiom that isn't foundational and isn't @[cited] is a bare/untagged cite.
      if !isFoundational a then
        locationViolations := locationViolations.push (.untagged a mod)
    | some src =>
      unless isInCitedFile env a do
        locationViolations := locationViolations.push (.misplaced a mod src)
  -- Check 3: BLUEPRINT-LEAK. Banked roots = in-scope decls NOT themselves `@[blueprint]`.
  let blueprintTagged := decls.filter (fun d => isBlueprint env d)
  let bankedRoots := decls.filter (fun d => !isBlueprint env d)
  let leakUnion := collectBlueprintBatch env bankedRoots
  let mut blueprintLeaks : Array (Name × Array Name) := #[]
  unless leakUnion.isEmpty do
    for d in bankedRoots do
      let hits := blueprintDepsOf env d
      unless hits.isEmpty do
        blueprintLeaks := blueprintLeaks.push (d, hits)
  pure { nsPrefixes, scanned := decls.size, roots := decls,
         unaccountedAxioms := unaccountedAx.qsort Name.lt,
         unaccounted, citedUsed, locationViolations, blueprintLeaks, blueprintTagged }

/-- The reusable core invariants (UNACCOUNTED + LOCATION). Blueprint-leak and cite-ceiling gating are
applied by the exe (`--allow-blueprint` / `--max-cites`), so `ok` is the always-on cited-cordon floor. -/
def CordonReport.ok (r : CordonReport) : Bool :=
  r.unaccounted.isEmpty && r.locationViolations.isEmpty

/-- The one-line machine-parseable summary: `UNACCOUNTED=n CITED=n LOCATION=n LEAKS=n`. -/
def CordonReport.summaryLine (r : CordonReport) : String :=
  s!"UNACCOUNTED={r.unaccounted.size} CITED={r.citedUsed.size} LOCATION={r.locationViolations.size} LEAKS={r.blueprintLeaks.size}"

/-- Render one axiom violation as an actionable line. -/
def AxiomViolation.toString : AxiomViolation → String
  | .untagged ax mod =>
    s!"  UNTAGGED axiom `{ax}` (in `{mod}`) — prove it, or `@[cited \"…\"]` it and move to a `…Cited.lean` file."
  | .misplaced ax mod src =>
    s!"  MISPLACED cited axiom `{ax}` [{src}] (in `{mod}`) — move it to a located `…Cited.lean` file."

end Meta.CordonAudit

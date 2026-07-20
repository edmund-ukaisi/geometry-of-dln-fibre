import DLNFibre.Core.Meta.Cited

/-!
# `DLNFibre.Core.Meta.CordonAudit` — the env-reading cordon gate (used by `lake exe cited-audit`)

The repo-gate frontend over the reusable core (`DLNFibre.Core.Meta.Cited.auditDecl`). Loads a compiled
Lean environment (the imported `.olean`s of the library, with env-extensions — so `@[cited]` params are
readable) and runs three independent, deterministic checks over a chosen namespace:

1. **UNACCOUNTED = ∅** — no public declaration rests on an untagged, non-foundational axiom.
2. **LOCATION + TAG** — every `axiom` in the namespace is `@[cited]` *and* declared in a located
   `…Cited` file.
3. **MANIFEST** (`--manifest`) — the per-headline cite map, derived from the same `@[cited]` sources.

Emits a one-line machine-parseable summary (`UNACCOUNTED=n CITED=n LOCATION=n`) + a human listing, and
signals violations to `main` (which sets a nonzero exit code). The `main` entry point +
`enableInitializersExecution`/`importModules` glue live in `scripts/cited_audit.lean` (the `lean_exe`
root); this module is the pure, importable analysis so it is itself covered by the sorry/axiom gates.

Policy + workflow: `docs/policies/citation-cordon.md`.
-/

open Lean
open DLNFibre.Meta.Cited

namespace DLNFibre.Meta.CordonAudit

/-- A located/tagging violation for a single axiom. -/
inductive AxiomViolation where
  /-- The axiom is not `@[cited]`-tagged. -/
  | untagged (ax : Name) (mod : Name)
  /-- The axiom is `@[cited]` but not declared in a located `…Cited` file. -/
  | misplaced (ax : Name) (mod : Name) (src : String)
  deriving Inhabited

/-- The full report of a cordon run over a namespace. -/
structure CordonReport where
  /-- The namespace prefixes audited (the first-party allowlist, e.g. `#[DLNFibre, RLCT]`). -/
  nsPrefixes : Array Name
  /-- Number of public declarations scanned. -/
  scanned : Nat
  /-- Declarations with a non-empty UNACCOUNTED set (decl, its unaccounted axioms). -/
  unaccounted : Array (Name × Array Name)
  /-- All distinct `@[cited]` axioms used across the namespace, with sources (sorted). -/
  citedUsed : Array (Name × String)
  /-- Axiom location/tagging violations (sorted by axiom name). -/
  locationViolations : Array AxiomViolation
  deriving Inhabited

/-- Does a name lie under **any** audited namespace prefix and is it a real (non-internal) decl?
(The scope is a first-party allowlist — `#[DLNFibre, RLCT]` by default — so bare-namespace first-party
modules like `RLCT` are covered, not just the `DLNFibre` namespace.) -/
def inScope (nsPrefixes : Array Name) (n : Name) : Bool :=
  nsPrefixes.any (·.isPrefixOf n) && !n.isInternalDetail

/-- Enumerate the in-scope declaration names of the environment (deterministic order: sorted). -/
def scopedDecls (env : Environment) (nsPrefixes : Array Name) : Array Name := Id.run do
  let mut r : Array Name := #[]
  for (n, _) in env.constants.toList do
    if inScope nsPrefixes n then
      r := r.push n
  r.qsort Name.lt

/-- Enumerate **every** in-scope `axiom` declaration (sorted). Unlike `scopedDecls` this does NOT
filter internal/generated names — the location+tag check must see *every* axiom under the namespace
(a compiler-generated axiom, e.g. from a sneaked-in `native_decide`, is exactly what should surface). -/
def scopedAxioms (env : Environment) (nsPrefixes : Array Name) : Array Name := Id.run do
  let mut r : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if nsPrefixes.any (·.isPrefixOf n) && ci.isAxiom then
      r := r.push n
  r.qsort Name.lt

/-- **Build the cordon report** over `nsPrefix`. Runs the three checks. The UNACCOUNTED check uses the
**batched** collector (`collectAxiomsBatch`, one shared traversal over all in-scope roots — O(reachable
constants), not O(decls × depth)) to get the *union* of axioms the public API rests on; per-decl
attribution of an unaccounted axiom is a targeted second pass, taken **only** when the union has an
unaccounted axiom (a red gate — rare), so the common (green) path is a single traversal. The LOCATION +
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
  pure { nsPrefixes, scanned := decls.size, unaccounted, citedUsed, locationViolations }

/-- Is the report clean (all three checks pass)? -/
def CordonReport.ok (r : CordonReport) : Bool :=
  r.unaccounted.isEmpty && r.locationViolations.isEmpty

/-- The one-line machine-parseable summary: `UNACCOUNTED=n CITED=n LOCATION=n`. -/
def CordonReport.summaryLine (r : CordonReport) : String :=
  s!"UNACCOUNTED={r.unaccounted.size} CITED={r.citedUsed.size} LOCATION={r.locationViolations.size}"

/-- Render one axiom violation as an actionable line. -/
def AxiomViolation.toString : AxiomViolation → String
  | .untagged ax mod =>
    s!"  UNTAGGED axiom `{ax}` (in `{mod}`) — prove it, or `@[cited \"…\"]` it and move to a `…Cited.lean` file."
  | .misplaced ax mod src =>
    s!"  MISPLACED cited axiom `{ax}` [{src}] (in `{mod}`) — move it to a located `…Cited.lean` file."

end DLNFibre.Meta.CordonAudit

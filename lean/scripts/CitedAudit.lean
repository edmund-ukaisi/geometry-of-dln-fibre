import DLNFibre.Core.Meta.CordonAudit

/-!
# `cited-audit` — the citation-cordon repo gate (`lake exe cited-audit`)

Loads a compiled Lean environment (the library's `.olean`s, with env-extensions so `@[cited]`
sources are readable) and runs the three cordon checks (`DLNFibre.Core.Meta.CordonAudit`) over a
namespace. **Enforcing:** nonzero exit on any UNACCOUNTED or LOCATION violation. See
`docs/policies/citation-cordon.md`; the wrapper is `scripts/cited`.

Usage:
```
cited-audit [--manifest] [--ns <Prefix>] [--import <Module>]...
```
* default import `DLNFibre` (the aggregator), default namespace `DLNFibre`;
* `--manifest` prints the per-headline / per-source cite manifest and exits 0 (informational);
* `--import M` (repeatable) chooses the module(s) to load — the test harness points this at the
  adversarial fixture module in isolation so its intentional violations don't touch the real gate.
-/

open Lean
open DLNFibre.Meta.Cited
open DLNFibre.Meta.CordonAudit

/-- Parsed command-line configuration. -/
structure Config where
  imports : Array Name := #[]
  nsPrefixes : Array Name := #[]
  manifest : Bool := false

/-- Parse argv into a `Config` (simple, order-independent flags). -/
def parseArgs (args : List String) : Except String Config := do
  let rec go (c : Config) : List String → Except String Config
    | [] => .ok c
    | "--manifest" :: rest => go { c with manifest := true } rest
    | "--ns" :: v :: rest => go { c with nsPrefixes := c.nsPrefixes.push v.toName } rest
    | "--import" :: v :: rest => go { c with imports := c.imports.push v.toName } rest
    | a :: _ => .error s!"unknown argument `{a}`"
  let c ← go {} args
  -- Default namespace scope: the **first-party allowlist** — `DLNFibre` (main) + `RLCT` (the bare-
  -- namespace analysis modules, no Mathlib overlap). A first-party bare namespace must be listed here
  -- to be gate-covered: its modules live under `DLNFibre/**` but its decls are in a bare namespace, so
  -- a `--ns DLNFibre` scan alone would miss them (where the cited continuation axiom will land). `--ns`
  -- overrides (appends), so the harness's `--ns CordonFixtures` still targets the fixtures in isolation.
  let c := if c.nsPrefixes.isEmpty then { c with nsPrefixes := #[`DLNFibre, `RLCT] } else c
  -- Default import set: the aggregator `DLNFibre` + the cite file `AoyagiCited` (which the
  -- single-writer aggregator does not yet import), so the gate sees the whole library AND its cites.
  .ok (if c.imports.isEmpty then
        { c with imports := #[`DLNFibre, `DLNFibre.DLN.RLCT.AoyagiCited] } else c)

/-- The per-source manifest: for each `@[cited]` source, the axioms carrying it (sorted). -/
def printManifest (r : CordonReport) : IO Unit := do
  let nsStr := String.intercalate ", " (r.nsPrefixes.toList.map (·.toString))
  IO.println s!"-- cite manifest for namespaces {nsStr} --"
  if r.citedUsed.isEmpty then
    IO.println "  (no @[cited] axioms in use)"
  else
    -- group axioms by source string
    let mut bySrc : Std.HashMap String (Array Name) := {}
    for (ax, src) in r.citedUsed do
      bySrc := bySrc.insert src ((bySrc.getD src #[]).push ax)
    let srcs := (bySrc.toList.toArray.map (·.1)).qsort (· < ·)
    for src in srcs do
      let axs := (bySrc.getD src #[]).qsort Name.lt
      IO.println s!"  [{src}]"
      for a in axs do
        IO.println s!"    - {a}"

/-- Print the human-readable listing of violations (deterministic order). -/
def printListing (r : CordonReport) : IO Unit := do
  unless r.unaccounted.isEmpty do
    IO.eprintln s!"UNACCOUNTED axioms ({r.unaccounted.size} declaration(s) rest on an untagged, non-foundational axiom):"
    for (d, axs) in r.unaccounted do
      let axsStr := String.intercalate ", " (axs.toList.map toString)
      IO.eprintln s!"  `{d}` → {axsStr}"
    IO.eprintln "  → prove each axiom, or `@[cited \"…\"]` it and move to a `…Cited.lean` file."
  unless r.locationViolations.isEmpty do
    IO.eprintln s!"LOCATION/TAG violations ({r.locationViolations.size}):"
    for v in r.locationViolations do
      IO.eprintln v.toString

unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"cited-audit: {e}"; return (2 : UInt32)
  -- Load the environment WITH extensions (so `@[cited]` params are readable).
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let imports := cfg.imports.map (fun m => { module := m : Import })
  let env ← Lean.importModules imports (opts := {}) (trustLevel := 0) (loadExts := true)
  try
    let (report, _) ← (buildReport cfg.nsPrefixes).toIO
      { fileName := "<cited-audit>", fileMap := default } { env }
    -- One-line machine-parseable summary (always, to stdout).
    IO.println report.summaryLine
    if cfg.manifest then
      printManifest report
      return (0 : UInt32)
    printListing report
    if report.ok then
      IO.println s!"cited-audit: OK — {report.scanned} decls scanned, no unaccounted axioms, all cites located."
      return (0 : UInt32)
    else
      IO.eprintln "cited-audit: FAIL — the cordon is red (see violations above)."
      return (1 : UInt32)
  finally
    env.freeRegions

import Meta.CordonAudit

/-!
# `cordon-audit` — the citation-cordon repo gate (`lake exe cordon-audit`)

Loads a compiled Lean environment (the library's `.olean`s, with env-extensions so `@[cited]` sources
and `@[blueprint]` tags are readable) and runs the four cordon checks (`Meta.CordonAudit`) over a
scope. **Enforcing:** nonzero exit on any UNACCOUNTED axiom, any LOCATION violation, or any
BLUEPRINT-LEAK (unless `--allow-blueprint`). The wrapper is `scripts/cordon`; policy in
`docs/policies/citation-cordon.md`.

Usage:
```
cordon-audit [--manifest] [--allow-blueprint] [--max-cites N] [--json <outfile>] [--generated <sha>]
             [--ns <ModulePrefix>] [--import <Module>]...
```
* default import `DLNFibre` (the aggregator), default scope module-provenance `DLNFibre`;
* `--manifest` prints the per-headline / per-source cite manifest and exits 0 (informational);
* `--allow-blueprint` treats the scope as blueprint-internal: blueprint leaks are *reported* but do
  NOT fail the gate (for auditing a scope that is itself the forecast layer);
* `--max-cites N` FAILS if more than `N` cites are present (default: cite-permissive — DLNFibre's DoD
  is proved-modulo-declared-cites, NOT zero-cite; the Aoyagi RLCT interface is a legitimate cite);
* `--json <outfile>` additionally writes the machine-readable report (schema below) to `<outfile>`;
  the human output and the exit code are unchanged (the file is written on green AND red gates so the
  map validator always gets the report). Schema:
  `{"roots":[…], "unaccounted":["axiomName",…], "cited":[{"axiom":"…","source":"…"}],
    "leaks":[{"decl":"…","via":"blueprintConstant"}], "generated":"<git HEAD sha>", "scope":"<args>"}`
  — one `leaks` entry per (banked decl, blueprint dep) pair;
* `--generated <sha>` overrides the `generated` field (default: `git rev-parse HEAD`, else `"unknown"`);
* `--ns M` (repeatable) appends a **module-name** prefix to the scope;
* `--import M` (repeatable) chooses the module(s) to load — the test harness points this at the
  adversarial fixture modules in isolation so their intentional violations don't touch the real gate.

**Scope = module provenance.** A `--ns` entry is a *module-name* prefix, not a decl-namespace prefix:
a decl/axiom is in scope iff its source module has that prefix. Default scope `DLNFibre` covers all of
`lean/DLNFibre/**` without sweeping in Mathlib.
-/

open Lean
open Meta.Cordon
open Meta.CordonAudit

/-- Parsed command-line configuration. -/
structure Config where
  imports : Array Name := #[]
  nsPrefixes : Array Name := #[]
  manifest : Bool := false
  /-- Blueprint-internal scope: leaks reported but not gating. -/
  allowBlueprint : Bool := false
  /-- Cite ceiling: `none` = cite-permissive (DLNFibre's default — cites are a legitimate DoD); `some n`
  = FAIL if `CITED > n`. (The sibling `qs` harness passes `--max-cites 0` for its zero-cite DoD; here
  the default is permissive.) -/
  maxCites : Option Nat := none
  /-- If `some path`, additionally write the JSON report to `path` (human output + exit code unchanged). -/
  json : Option String := none
  /-- Override for the `generated` field of the JSON report; `none` = auto-detect `git rev-parse HEAD`. -/
  generated : Option String := none

/-- Parse argv into a `Config` (simple, order-independent flags). -/
def parseArgs (args : List String) : Except String Config := do
  let rec go (c : Config) : List String → Except String Config
    | [] => .ok c
    | "--manifest" :: rest => go { c with manifest := true } rest
    | "--allow-blueprint" :: rest => go { c with allowBlueprint := true } rest
    | "--json" :: v :: rest => go { c with json := some v } rest
    | "--generated" :: v :: rest => go { c with generated := some v } rest
    | "--ns" :: v :: rest => go { c with nsPrefixes := c.nsPrefixes.push v.toName } rest
    | "--import" :: v :: rest => go { c with imports := c.imports.push v.toName } rest
    | "--max-cites" :: v :: rest =>
        match v.toNat? with
        | some n => go { c with maxCites := some n } rest
        | none => .error s!"--max-cites expects a natural number, got `{v}`"
    | a :: _ => .error s!"unknown argument `{a}`"
  let c ← go {} args
  -- Default scope: module-provenance `DLNFibre` — every decl whose source module lives under
  -- `lean/DLNFibre/**`. `--ns` overrides (appends), so the harness's `--ns CordonFixtures` targets the
  -- fixtures in isolation.
  let c := if c.nsPrefixes.isEmpty then { c with nsPrefixes := #[`DLNFibre] } else c
  -- Default import set: just the aggregator `DLNFibre` (the math lib, which does NOT depend on the
  -- cordon). The exe itself links `Meta.Cordon` (via `Meta.CordonAudit`), so the `@[cited]` /
  -- `@[blueprint]` attributes are registered and readable in the imported env.
  .ok (if c.imports.isEmpty then { c with imports := #[`DLNFibre] } else c)

/-- The per-source manifest: for each `@[cited]` source, the axioms carrying it (sorted). -/
def printManifest (r : CordonReport) : IO Unit := do
  let nsStr := String.intercalate ", " (r.nsPrefixes.toList.map (·.toString))
  IO.println s!"-- cite manifest for module scope {nsStr} --"
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
  unless r.blueprintTagged.isEmpty do
    IO.println s!"-- @[blueprint] forecasts in scope ({r.blueprintTagged.size}) --"
    for b in r.blueprintTagged do
      IO.println s!"    - {b}"

/-- Print the human-readable listing of violations (deterministic order). -/
def printListing (r : CordonReport) (allowBlueprint : Bool) : IO Unit := do
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
  unless r.blueprintLeaks.isEmpty do
    let label := if allowBlueprint then "BLUEPRINT-LEAKS (allowed: --allow-blueprint)" else "BLUEPRINT-LEAKS"
    IO.eprintln s!"{label} ({r.blueprintLeaks.size} banked declaration(s) rest on a @[blueprint] forecast):"
    for (d, bs) in r.blueprintLeaks do
      let bsStr := String.intercalate ", " (bs.toList.map toString)
      IO.eprintln s!"  `{d}` → {bsStr}"
    unless allowBlueprint do
      IO.eprintln "  → banked never consumes a forecast: prove/ban the forecast, or `@[blueprint]` the consumer."

/-! ## The JSON report (consumed by the map validator) -/

/-- Escape a string for embedding inside a JSON string literal (matches `WalkDecls.jsonEscape`). -/
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

/-- The git HEAD sha of the invocation's cwd, best-effort (`"unknown"` if git is unavailable / not a
repo). -/
def gitHeadSha : IO String := do
  try
    let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
    -- git prints `<sha>\n`; take the first line (avoids the deprecated `String.trim`).
    if out.exitCode == 0 then pure (out.stdout.takeWhile (· != '\n')).toString else pure "unknown"
  catch _ => pure "unknown"

/-- Serialise the report to the map-validator schema. `leaks` is flattened to one entry per (banked
decl, blueprint dependency) pair. -/
def reportToJson (r : CordonReport) (generated scope : String) : String := Id.run do
  let citedJson := "[" ++ String.intercalate ","
    (r.citedUsed.toList.map (fun (n, src) =>
      "{\"axiom\":" ++ jstr n.toString ++ ",\"source\":" ++ jstr src ++ "}")) ++ "]"
  let mut leakItems : Array String := #[]
  for (d, vias) in r.blueprintLeaks do
    for v in vias do
      leakItems := leakItems.push
        ("{\"decl\":" ++ jstr d.toString ++ ",\"via\":" ++ jstr v.toString ++ "}")
  let leaksJson := "[" ++ String.intercalate "," leakItems.toList ++ "]"
  return "{" ++
    "\"roots\":" ++ jarrN r.roots ++
    ",\"unaccounted\":" ++ jarrN r.unaccountedAxioms ++
    ",\"cited\":" ++ citedJson ++
    ",\"leaks\":" ++ leaksJson ++
    ",\"generated\":" ++ jstr generated ++
    ",\"scope\":" ++ jstr scope ++
    "}\n"

/-- The effective scope, as a reproducible CLI-arg string (for the JSON `scope` field). -/
def scopeString (cfg : Config) : String :=
  String.intercalate " " (
    (cfg.imports.toList.map (fun m => s!"--import {m}")) ++
    (cfg.nsPrefixes.toList.map (fun m => s!"--ns {m}")))

unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"cordon-audit: {e}"; return (2 : UInt32)
  -- Load the environment WITH extensions (so `@[cited]` params + `@[blueprint]` tags are readable).
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let imports := cfg.imports.map (fun m => { module := m : Import })
  let env ← Lean.importModules imports (opts := {}) (trustLevel := 0) (loadExts := true)
  try
    let (report, _) ← (buildReport cfg.nsPrefixes).toIO
      { fileName := "<cordon-audit>", fileMap := default } { env }
    -- One-line machine-parseable summary (always, to stdout).
    IO.println report.summaryLine
    -- `--json`: write the machine-readable report (human output + exit code unchanged), on green AND red.
    match cfg.json with
    | some path =>
      let sha ← match cfg.generated with
        | some g => pure g
        | none   => gitHeadSha
      IO.FS.writeFile path (reportToJson report sha (scopeString cfg))
      IO.eprintln s!"cordon-audit: wrote JSON report to {path}"
    | none => pure ()
    if cfg.manifest then
      printManifest report
      return (0 : UInt32)
    printListing report cfg.allowBlueprint
    -- `--max-cites n` enforces a cite ceiling (the default is cite-permissive).
    let citeOverflow : Bool := match cfg.maxCites with
      | some n => report.citedUsed.size > n
      | none   => false
    if citeOverflow then
      let nc := report.citedUsed.size
      let mx := cfg.maxCites.getD 0
      IO.eprintln s!"cordon-audit: FAIL — {nc} cite(s) present, but --max-cites={mx}."
      for (ax, src) in report.citedUsed do
        IO.eprintln s!"    CITED `{ax}` [{src}]"
    -- Blueprint leaks fail the gate UNLESS the scope is declared blueprint-internal.
    let leakFail : Bool := !cfg.allowBlueprint && !report.blueprintLeaks.isEmpty
    if report.ok && !citeOverflow && !leakFail then
      let citeNote := if report.citedUsed.isEmpty then "no cites" else s!"{report.citedUsed.size} declared cite(s)"
      let leakNote := if report.blueprintLeaks.isEmpty then "no blueprint leaks"
                      else s!"{report.blueprintLeaks.size} blueprint leak(s) allowed (--allow-blueprint)"
      IO.println s!"cordon-audit: OK — {report.scanned} decls scanned, no unaccounted axioms, {citeNote} located, {leakNote}."
      return (0 : UInt32)
    else
      unless citeOverflow do
        IO.eprintln "cordon-audit: FAIL — the cordon is red (see violations above)."
      return (1 : UInt32)
  finally
    env.freeRegions

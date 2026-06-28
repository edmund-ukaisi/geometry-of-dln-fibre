# Aggregation-readiness audit — carving lineage → `DLNFibre.lean` (R1-UPPER)

**Auditor:** genm-carve2 (read-only; no edits to genm-firing's files, no build of its moving branch).
**Against:** `origin/genm-firing` HEAD `7681b120` (the canonical-cover carving branch; `schurRatioResidGen_mid`
still the single open sorry) vs that branch's aggregator `DLNFibre.lean` (234 imports).
**Method:** computed `RouteMSchurFiring`'s full import sub-closure, split into already-imported vs new, and
intersected the NEW modules' top-level decl names against the existing aggregator closure (Item-113 style
"environment already contains" check). Names extracted Unicode-aware (`grep -P`), top-level decls only.

## Headline

**ONE real name-clash to deconflict before `lake build DLNFibre` will pass; otherwise clean.**
`scripts/lb`/`lake build <Module>` builds the import-closure only and does **not** catch this (per
`lean/CLAUDE.md`); it surfaces **only** at the full-aggregator `lake build DLNFibre`. So green-in-isolation
on genm-firing does NOT imply aggregation-green.

## The clash (Item-113 "environment already contains")

`def e2`, namespace `DLNFibre.DLN.RLCT`, declared in BOTH:
- **NEW** (carving sub-closure): `RouteMSchurDepth2.lean:583` — `noncomputable def e2 : Fin 2 × Fin 2 ≃ Fin (2*2)`
  (the corank-2 matrix↔flat index equiv; used internally by `Rmat2`/`Rmat2_entry`/… throughout that file).
- **EXISTING** (already aggregated): `RouteM3333Atom.lean:267` — `def e2 : Fin 3 ≃ {a : Fin 27 // frameB a = 2}`
  (a `(3,3,3,3)` frame-selector). Confirmed in the aggregator's current import list.

Both are top-level in the same namespace ⟹ `environment already contains 'DLNFibre.DLN.RLCT.e2'` at aggregation.

**Recommended fix:** RENAME the carving one (the incumbent `RouteM3333Atom.e2` predates the lineage; the
carving module should yield). In `RouteMSchurDepth2.lean`, rename `e2 → e2flatD2` (or `eD2`) and update its
internal uses (`e2`, `e2.symm`, `e2 (i,j)` — ~10 sites, lines 583-636+). Local rename, no downstream API
impact (the name is not re-exported under a stable contract). `rg '\be2\b' RouteMSchurDepth2.lean` to scope.
(Do NOT touch `RouteM3333Atom.e2`.)

## The aggregation import set (what to add to `DLNFibre.lean`)

`RouteMSchurFiring`'s sub-closure = 38 modules (excl. self); 24 already imported by the aggregator, **15 NEW
to add** (incl. `RouteMSchurFiring` itself), in dependency order:

    DLNFibre.Core.MeasureTheory.PolynomialZeroSet      -- Core (a.e.-positivity null-set)
    DLNFibre.DLN.RLCT.Foundations.LossContinuity
    DLNFibre.DLN.RLCT.Validate.Case222Block
    DLNFibre.DLN.RLCT.Validate.Case222CoverGE
    DLNFibre.DLN.RLCT.Validate.Case222CoverGETail
    DLNFibre.DLN.RLCT.Validate.RouteMState
    DLNFibre.DLN.RLCT.Validate.RouteMLeaf
    DLNFibre.DLN.RLCT.Validate.RouteMSchurAlg
    DLNFibre.DLN.RLCT.Validate.RouteMSchurShear
    DLNFibre.DLN.RLCT.Validate.RouteMSchur
    DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2        -- ← holds the clashing `e2` (rename first)
    DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral
    DLNFibre.DLN.RLCT.Validate.RadialResidualPower
    DLNFibre.DLN.RLCT.Validate.ResolutionAtlas
    DLNFibre.DLN.RLCT.Validate.RouteMSchurFiring        -- the headline module

(`RouteMSchurGenCover` is already in the aggregator's 24 already-imported set.) Add at the END of
`DLNFibre.lean` per the single-writer rule; the exact emission order above respects intra-set dependencies
(verify with the per-module `import` lines — `RouteMSchurFiring` last).

## Everything else: CLEAN

- The 15 new carving modules' 364 top-level names ∩ existing-234-closure 3219 names = **{e2} only** (the one
  above). No other "environment already contains" risk.
- **No internal duplicate** among the 15 new modules (no name declared twice across them).
- **No duplicate carving lineage** in the tree: the carving files (`RouteMSchurCorank3`, `RouteMSchurFiring`,
  `RouteMSchurGenCover`, `RouteMSchurGeneral`) are one coherent lineage on genm-firing — no second
  `…SchurFiring`-style file that would mass-clash.
- The carving's load-bearing results (`frobSqG_ne_zero_ae`, `frobSqShiftG_ne_zero_ae`, `resolvedShiftRG_le`,
  `coreSchurGenVal`, `schurRecStep_four`, …) and helpers (`eG`, `matToFlatG`, `RmatG`, `innerSGen`,
  `coreEntryPolyG`, `cellR`, `slotMatG`, `bgShiftG`, `zσG`, `zEG`) are all **unique** to the lineage — no
  collision with existing modules.

## Gate (do NOT run yet — branch is moving)

The green-gate `lake build DLNFibre` waits until genm-firing closes `schurRatioResidGen_mid`. After close:
(1) apply the `e2` rename in `RouteMSchurDepth2`; (2) add the 15 imports (order above) at the end of
`DLNFibre.lean`; (3) add the load-bearing carving results to `AxCheck.lean` for the forced `#print axioms`
clean-three gate; (4) full `lake build DLNFibre` (catches any residual clash the isolation build missed).

## Caveat

genm-firing's branch is advancing (HEAD moved 754416ab → 7681b120 → … during this expedition). Re-run the
clash intersection against its FINAL pre-aggregation HEAD before integrating — a late-added helper could
introduce a new short-name clash (the `e2`-class risk is short generic names like `e2`/`e3`/`σ`). The 15-module
list and the `e2` finding are stable as of `7681b120`; the method (this note's commands) re-runs in seconds.

# Merge plan of record — dev → aoyagi-engine (phase-init integration)

Grounded in `cert-reconciliation-map.md` (recon-merge, verified on its crux: our branch touched none of
the 8 Core modules / RlctPayoff; both cordons register the identical `cited` attribute). **Nature: a
superset-selection + dead-stack retirement — the two branches built DISJOINT RLCT stacks, not overlapping
proofs.** Scope: phase INITIALISATION only (operator: prepare, then discuss before the phase in earnest).

## Safety scaffold
- **Tag the pre-merge tip** `aaa857615` as `premerge-dev-<date>` — the recovery point (`git reset --hard`
  restores it if the integration goes wrong).
- Do the integration on `expedition/aoyagi-engine` in root (controller merger role); **push only when the
  full green-gate passes.** Each stage is its own commit (bisectable/revertable).
- The integration is small (breakage ≈ S per the map), so the controller drives it directly; an integrator
  seat is dispatched ONLY if the green-gate surfaces non-trivial breakage.

## Stages (each gated; the only hand-work is the 11 conflicts + the cordon/cite/archive surgery)

**1. Merge + structural conflicts.** `git merge origin/dev`. Accept all dev-only files wholesale (the 8
Core modules, `RlctPayoff`/`General`, `BundleShiftDischarge`, `DeterminantalChartRing`, `Determinantal/**`,
`RankMinors`, `AoyagiCited` — clean, no conflict). Hand-resolve the 11 (cert §4):
  - `DLNFibre.lean` — union imports; keep dev's `Analysis/RLCT/**` + `Determinantal/**` + `RankMinors` +
    `AoyagiCited`; DROP dev's `Core.Meta.Cited`/`CordonAudit` imports (ours is external/moving); keep our
    Aoyagi-Core imports; DROP the 287 `DLN.RLCT.*` Engine imports (archive, stage 5).
  - `lakefile.toml` — keep OUR 3 stanzas (`Meta`/`Core.Meta.Cordon` lib, `cordon-audit` exe, `CordonFixtures`
    w/ 4 globs incl. `CordonClean`/`CordonLeak`); DROP dev's `cited-audit` exe + dev's 2-glob `CordonFixtures`.
  - `tests/CordonFixtures.lean`, `tests/FixtureCited.lean` — take OURS (blueprint coverage). *(Corrects the
    aborted attempt's `--theirs`.)*
  - `lean/CLAUDE.md` — union (keep both Mathlib-gotcha sets).
  - 6 prose/policy — prose-union; `docs/policies/citation-cordon.md` gets a genuine reconcile pass (it
    documents a different cordon each side → rewrite to the chosen cordon + the blueprint half).

**2. Cordon unification (crux).** Standardise on OUR `Meta.Cordon` (strict superset). Delete dev's cordon:
modules `Core/Meta/Cited.lean` + `Core/Meta/CordonAudit.lean`, exe root `scripts/CitedAudit.lean`, wrappers
`scripts/cited`(+`-test`), dev's lakefile stanzas. Port-list (cert §1d — nothing dropped): (i) add
`` `DLNFibre.DLN.RLCT.AoyagiCited `` to `citedFileAllowlist` (module doesn't end in `Cited` → else LOCATION
red); (ii) add it to `CordonGate.parseArgs` default imports (belt+suspenders); (iii) repoint the docstring
example from `cited_aoyagi_dln` to `cited_aoyagi_lower_ax`. Keep our `CordonClean`/`CordonLeak` fixtures.

**3. Cite adoption + placement.** Dev's cite axioms (`cited_watanabe_upper_ax`, `cited_aoyagi_lower_ax`,
`cited_local_zeta_pole`) keep their `@[cited "…"]` tags UNEDITED (shared attribute name). Repoint the 2 cite
files' cordon import/open: `import DLNFibre.Core.Meta.Cited` → the surviving cordon module (+ `open`).
Retire-ours (`cited_aoyagi_dln`) is AUTOMATIC (dev's migrated `RlctPayoff` overwrites ours). **PLACEMENT
TASTE DECISION (operator/elder, cert §2c): option (A) — move our attribute module to
`DLNFibre.Core.Meta.Cordon`** (dev's self-auditing placement + our superset code), so the cordon is under
the gate it enforces and cite files import it naturally. Recommended; pending operator confirm.

**4. Core-drift fix.** Near-zero (weakenings are instance-compatible). Only the relocated `Matrix.*` lemmas
(`RankMinors.lean`) need a one-line `open Matrix`/requalify in any KEPT file that calls them bare —
`CommonPivotL2.lean` (1 line, if kept); `GramFullRank.lean` has its own local copy (no-op).

**5. Archive the chart Engine.** Move `DLN/RLCT/**` (287 imports) to a `retired/` location; drop its
aggregator imports; un-wire from the sorry-census; README (reusable-proven vs category-false). Decide the
2 Engine-support files: if `GramFullRank`/`CommonPivotL2` are Engine-only (no KEPT Aoyagi object imports
them), archive with the Engine; else keep + the stage-4 requalify.

**6. Green-gate + ratify + (no push until green).** Full `lake build DLNFibre` (NOT per-module — name-clash
trap). Run the chosen cordon gate (`scripts/cordon` + `cordon-test`) → green. `#print axioms` the payoff
roots (expect `[propext, Classical.choice, Quot.sound]` + the 2 DLN cites `cited_watanabe_upper_ax` /
`cited_aoyagi_lower_ax`) + the deliverable (`aoyagi_learning_coefficient_L2/gen/gen_le` clean). `scripts/sorries`
sane. Elder ratifies the cordon+cite unification and records the two charter boundaries (prove-`cited_aoyagi_lower`-never-cite;
reuse-geometry-not-L&R-theory). THEN push. Then return to the operator to discuss before the phase in earnest.

## Roles
Controller drives 1–5 (merger role + small mechanical/judgment surgery) + the green-gate (6). Integrator
seat only on green-gate surprise. Elder ratifies (6).

## The single kill-target (charter alignment)
Post-merge, the lower bound is `cited_aoyagi_lower_ax` — ONE named `@[cited]` axiom in ONE located file.
dev's `rlctGlobal` is BUILT cite-free and the `codim_ℝ = codim_K` transfer is PROVED, so this is the sole
clean in-library axiom the new phase exists to discharge (charter §0/§1-A). `cited_watanabe_upper_ax` stays
(external). This is the tidiest possible runway for "prove it, never cite it."

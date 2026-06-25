# thread 09 — chart-flatness prototype (G2a, formalisation / tide — the GATING probe)

**Type:** formalisation (tide) · `OPENED → SPECIFY/DESIGN → CHECKPOINT(no-skip) → PROVE-or-WALL`.
G0 (thread 07) confirmed the chart build is ~6–12 modules whose HIGH-risk core is a **flatness proof on
the pivot chart** (the wall-within-the-wall that stalled thread-04). **Do NOT build the full G2.** This
tide is a *thermometer*: pin + attack the flatness core on the simplest case to get a cheap GO/NO-GO
before committing the rest. If it walls, we land G1 + roadmap; if it lands, we commit full G2.

## The gating question
On the pivot chart `U = {M : top-left r×r block invertible}` of the exact-rank stratum, is the
chart-localized comorphism of `mult` **flat** (via free, through the Schur section) — formalizably at
Mathlib v4.29? Route **M-goingdown** (G0's recommendation): localize F1's `multComap` at the pivot minor;
on that chart `mult` is the trivial bundle `U × mult⁻¹(E)`, so the localized total ring is free
(polynomial) over the localized base ring ⟹ flat ⟹ `HasGoingDown` ⟹ the LANDED
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` gives the shift.

## Scope — the SIMPLEST nontrivial case for cheap signal
Target the **anchor `(2,2,2)`, `r=1`, `E = diag(1,0)`** (or general `N=2, r=1` if no harder). Deliver
the gating fact: the chart-localized comorphism is flat (or its localized total ring is free over the
localized base) on the pivot chart. Concretely, the sub-steps to probe/pin:
1. the pivot localization (`Localization.Away (pivot minor)` of the base/total coordinate rings; or the
   `MvPolynomial`-level localized algebra map) — **does the engine/Mathlib API support stating it?**
2. the Schur section as an explicit `AlgEquiv` / freeness witness on the chart;
3. `Module.Flat` (or `Module.Free`) of the localized total ring over the localized base ring.

Use the pinned `Module.Flat`/free + going-down API in `Core/FlatTrivialProductProbe.lean` (thread-04's
durable contracts) and F1's `Core/MultComorphism.lean` (`multComap`, `fibreGenIdeal`).

## MANDATORY process (no-skip checkpoint)
1. **SPECIFY/DESIGN + PROBE:** pin the localized comorphism + the freeness/flatness statement; probe the
   `Localization.Away` + `Module.Flat`/`Module.Free` API with `example` blocks (keep as durable
   contracts). **Fire a decorrelated `local-codex-consult`** (authenticated, xhigh) on the chart-flatness
   construction; save under `threads/09-chart-flatness-proto/codex/`.
2. **CHECKPOINT — report to `main` BEFORE grinding the full flatness proof:** the pinned construction,
   whether the freeness/flatness is reachable this run, and a GO/NO-GO. **Proceed to PROVE only if
   clearly viable.** If the localized-chart-ring layer or the Schur freeness needs machinery absent at
   v4.29, STOP and report the precise wall — that is a *successful thermometer reading* (it redirects us
   to land G1 + roadmap), NOT a failure. Do NOT grind a doomed proof, do NOT commit a `sorry`, do NOT
   weaken the statement to something vacuous.
3. **PROVE** the gating fact to green (anchor case), then report.

## Hard rules (lean/CLAUDE.md)
Build via `scripts/lb` (never bare `lake build`/`cache get`); zero sorry/axiom/native_decide; `↦`;
`decide +kernel`; name=content (don't name a chart-only fact as the global flatness). **Core only — never
import `DLNFibre.DLN`.** Confirm Mathlib lemmas exist before building on them. Don't touch other worktrees
or any stash. In-repo memory only.

## Report (to `main`)
The GO/NO-GO verdict on chart flatness + the precise reachability of each sub-step (localization,
Schur freeness, flatness); if a gating fact landed — name + signature + green/sorries/axioms + module
path; the decorrelated-Codex read; the honest size estimate for the full G2 given what you found.
This verdict decides whether we commit the remaining ~6–9 modules or land G1 + roadmap.

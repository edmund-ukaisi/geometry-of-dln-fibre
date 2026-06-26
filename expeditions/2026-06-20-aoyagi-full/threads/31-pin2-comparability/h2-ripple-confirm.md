# h2 ripple-confirm — VERDICT: R1 SAFE, headline SAFE. The coreΦ→Score slip is L2-local; the RLCT is unchanged (by an analytic diffeomorphism, not "thin set").

Decorrelated confirm of pp's headline-gate verdict. Computed (not just re-read): my own RLCT numerics
(paired, debiased) + decorrelated Codex (xhigh) + the seam trace from the Lean code. All agree:
**R1 is semantically UNAFFECTED by the coreΦ→Score fix; the headline `rlct = ½·codim` is SAFE** once the
squeeze is rebuilt with `Score`. The slip is confined to the squeeze's pointwise comparability.

---

## (1) The load-bearing claim — R1 is UNAFFECTED. Three independent confirmations.

### (1a) The seam trace (from the code, decorrelated read)
- R1's per-cell transport is `IsSchurStraightenSqueeze.redCore_eq : G y² = dlnLoss S.red 0 (redEmbed y)`
  (`RouteMRecursion.lean:105`, :150) — it resolves `rlctAtOn(dlnLoss S.red)` via its OWN reduced-chain
  recursion (descending `M ↦ S.red` on `ChainDimSplit`). R1 NEVER references the full `loss` or the
  per-layer-vs-global distinction; it computes the RLCT of the function `dlnLoss(reduced chain)`.
- `deepestCoreF := dlnLoss(deepestM)` (`DeepestGaugeChart.lean:114`) — definitionally the reduced-chain
  loss. The bundle's seam `deepest_regular_core_reduces` lands on `nReg/2 + rlctAtOn(dlnLoss M 0) 0`
  (`DeepestGaugeChart.lean:11-16`), and R1 folds `rlctAtOn(dlnLoss M 0) = ofReal(lambdaCore M)`
  (`DeepestGaugeConstruction.lean:3208-3218`). **R1's value `lambdaCore` is the RLCT of `deepestCoreF`,
  computed independently of the squeeze.**
- So the squeeze's `coreΦ` enters ONLY as a SUMMAND in the comparability `loss ≍ Sreg_E + coreΦ` (used to
  TRANSFER `rlctAtOn(loss) → rlctAtOn(Sreg_E + coreΦ)`). The bug is in that transfer, NOT in R1's
  resolution of `rlctAtOn(deepestCoreF)`. **No step between the squeeze and R1 feeds the per-layer-product
  VALUE into R1's recursion — R1 takes `dlnLoss(deepestM)` as a function.**

### (1b) The RLCT-invariance (numerics, mine, decorrelated from pp)
Paired RLCT estimates (CDF-slope, 4–8M samples, bias-cancelling paired statistic) of
`rlctAtOn(Sreg + Score)` vs `rlctAtOn(Sreg + coreΦ)` vs `rlctAtOn(loss)`:

| anchor | λ(Sreg+Score) | λ(Sreg+coreΦ) | λ(loss) | ratio-exp (0 ⟹ same RLCT) |
|---|---|---|---|---|
| (2,2,2) | 1.872 | 1.882 | 1.851 | +0.003 |
| (2,3,2) | 1.957 | 1.966 | 1.945 | +0.002 |
| (2,4,2) bigM1 | 1.943 | 1.919 | — | −0.006 |
| (3,3,3) r1 | 3.636 | 3.593 | — | −0.003 |

All three coincide to within estimator noise (uniform ~0.35 upward bias, IDENTICAL across the three — so
the RELATIVE conclusion is solid; the bias is an estimator artifact, not a real difference). The
bias-cancelling ratio-exponent ≈ 0 everywhere ⟹ `Sreg+Score` and `Sreg+coreΦ` have the SAME RLCT, even
when the tilted-kernel locus is ENLARGED (M1=4). **The thin tilted-kernel discrepancy does NOT move the
RLCT.** (Absolute values are NOT reliably recovered by this crude estimator on a non-isolated singularity
— the absolute (2,2,2) = 3/2 core is the Lean `case222_routeStep_value`, not a numeric claim.)

### (1c) The CLEAN structural reason (decorrelated Codex xhigh — sharper than the numerics)
Codex gives the RIGHT proof of `rlctAtOn(Sreg + Score) = rlctAtOn(Sreg + coreΦ)`, and explicitly WARNS
against "thin set" reasoning (it is the WRONG justification — `Score` and `coreΦ` agree as analytic germs
only off a proper analytic subset, so it is a germ/ideal change, not a null-set value change):

> `Score = ‖S0·(I−K)·S1‖²`, `coreΦ = ‖S0·S1‖²`, `K(0)=0` ⟹ `W := I−K` is an analytic `GL_M`-valued unit
> near 0. The triangular map `Ψ(E,θ,S0,S1) = (E,θ,S0, W(E,θ)·S1)` is a local analytic diffeomorphism
> (derivative = identity at 0) with `(Sreg+coreΦ)∘Ψ = Sreg+Score`. RLCT is diffeomorphism-invariant ⟹
> `rlctAtOn(Sreg+Score) = rlctAtOn(Sreg+coreΦ)`.

This is the load-bearing (b) proof: the `Score → coreΦ` RLCT equality rides the `S1 ↦ (I−K)·S1`
analytic-unit change of variables, NOT pointwise comparability or measure-zero. (For (2,2,2), M=1, `I−K`
is a scalar unit and the zero loci already match — no tilt possible.)

## (2) Spot-confirm

- **`dlnLoss_two_sided_of_frame` IS genuinely two-sided** (`DeepestGaugeBlocks.lean:566`): the conclusion
  is `(Sreg+Score) ≤ k2·loss ∧ loss ≤ k1·(Sreg+Score)` (both directions, an explicit `∧`). So
  `loss ≍ Sreg + Score` ⟹ `rlctAtOn(loss) = rlctAtOn(Sreg + Score)`. pp's (a) is SOUND.
- **(2,2,2) core value = 3/2:** `case222_routeStep_value = 3/2 = lambdaCore(2,2,2)`, `minAdm = 3`
  (`Case222RouteStep.lean:48,74-77`). With `nReg/2 = ½·r(H0+HL−r) = ½·3 = 3/2`, the full local RLCT is
  `3/2 + 3/2 = 3`. (My numeric ≈1.87 is the crude-estimator value of the full Sreg+core in my box, biased
  + non-isolated-singularity contaminated; the Lean value is the authority.)

## VERDICT (the headline-gate)

- **R1 (RouteM*, the (3,3,4) etc. anchors) is SEMANTICALLY UNAFFECTED** by the coreΦ→Score fix. It
  resolves `rlctAtOn(dlnLoss(reduced chain))` via reduced-chain losses, never the full loss or the
  per-layer-vs-global distinction. The slip is L2-LOCAL to the squeeze's pointwise comparability.
- **The headline `rlct = ½·codim` is SAFE**, rebuilt as (Codex's three-step, = pp's (a)+(b)):
  1. `loss ≍ Sreg + Score` (banked two-sided frame leaf) ⟹ `rlctAtOn(loss) = rlctAtOn(Sreg + Score)`.
  2. `rlctAtOn(Sreg + Score) = rlctAtOn(Sreg + coreΦ)` via the analytic diffeomorphism `S1 ↦ (I−K)·S1`
     (NOT "thin set"). **This is a NEW lemma to formalise** — the genuine, clean, sound replacement for
     the false `(♦)`/coreΦ germ-charge (the `sorry` at `DeepestGaugeConstruction.lean:2667`).
  3. `rlctAtOn(Sreg + coreΦ) = nReg/2 + rlctAtOn(deepestCoreF)` (reg peel) `= nReg/2 + lambdaCore` (R1).
- So a9711b920's squeeze restatement closes L2 modulo the L≥3 gap. The coreΦ slip is NOT deeper.

## The recommended fix (supersedes h2-diamond-proof's "restate with Score" — now with the CLEAN step-2)

The `sorry` at `:2667` (false `(♦)` statement) should be replaced NOT by a germ charge but by the
**analytic-unit change-of-variables lemma** `rlctAtOn(Sreg + Score) = rlctAtOn(Sreg + coreΦ)` via
`Ψ : S1 ↦ (I−K)·S1` (`K(0)=0` ⟹ `I−K` unit ⟹ `Ψ` local diffeo, `rlctAtOn_comp_localDiffeo` /
`rlctAtOn_comp_homeomorph`). Then:
- the squeeze is restated/proved with `Sreg + Score` (the banked two-sided leaf, direct);
- step 2 (the new lemma) bridges to the `coreΦ` form R1 consumes;
- R1 + the reg peel are unchanged.
This is cleaner AND smaller than the germ-charge route: no leading-order Taylor, no `(♦)` — a banked
local-diffeo RLCT peel + the unit `I−K`. **Likely 1 tide** (the diffeo + `rlctAtOn_comp_localDiffeo` are
banked; the only content is `I−K` is a unit near 0, from `K(0)=0`).

## Residual / honest caveats
- The diffeo step (2) needs `Ψ` to be a genuine local diffeo on the chart AND the `AtOn` domain
  identified (Codex's "provided the AtOn domain is identified locally" / open-chart caveat). The
  formaliser should confirm `rlctAtOn_comp_localDiffeo`'s domain hypotheses are met (K analytic, `I−K`
  unit on a nbhd, `Ψ(0)=0`). Low risk (all reads → 0 ⟹ `K → 0`), but it is a real check.
- My RLCT numerics confirm the RELATIVE equality robustly; they do NOT independently certify the absolute
  ½·codim (that is the Lean `case222`/`lambdaCore` lane + the cited Aoyagi/Watanabe `rlct ≤ ½·codim`).
- This whole confirm assumes the L2 producer; the L≥3 gap (general-L LDU induction) is separate and
  untouched.

## Artifacts
- `/tmp/h2confirm/diamond_leading.py`, `diamond_mechanism.py`, `diamond_factors.py` (the gap structure).
- RLCT numerics: inline (paired CDF-slope, calibrated) — re-runnable; (2,2,2),(2,3,2),(2,4,2),(3,3,3).
- Codex: `codex/h2-ripple-{prompt,answer}.md` (the analytic-diffeomorphism proof of step 2 + the
  "thin set is the wrong reason" warning).
- Triangulates with: pp's headline-gate verdict, a9711b920's empirical downstream-breakage report.

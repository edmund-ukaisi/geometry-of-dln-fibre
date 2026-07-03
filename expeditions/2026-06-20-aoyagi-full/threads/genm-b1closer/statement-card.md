# genm-b1closer — b1 (derivative-exposing first peel) + the b1→b2 residual-Jacobian rank identity LANDED

Charged to front-load **b1** (the derivative-exposing first-peel variant, "the last real build, the care
piece") and then close `hrank₂` + LEAF 2. This hand **landed b1 AND the full b1→b2 residual-Jacobian rank
identity**, axiom-clean and sorry-free. The remaining `hrank₂` content is precisely the **b3 count** (an
exact middle-stratum `rank(jacFlatL2)` computation — genuine new content, NOT mechanical), plus `hInterface`
/ `hRne` and the ∀-`v` wiring. LEAF 2 (`HeadlineL2Assembly.lean:107`) is left correctly-stated (untouched).

Branch `origin/genm-b1closer` @ `dec11815` (from `origin/genm-d1close`). Two new modules + a surgical
`S1IFTChart` field addition; all green in their import-closure.

## What LANDED (all sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

### The IFT-inverse-derivative field (`lean/DLNFibre/DLN/RLCT/Foundations/S1IFTChart.lean`)
`exists_boundedUnit_chart_of_contDiffAt` now ALSO returns `HasFDerivAt Ψsymm (f'.symm) wstar` — the
internal `hsymm_hfderiv` (line 139), previously discarded by the existential. The 3 downstream `obtain`
sites (2 in `S1IFTChart`, `D1HChartInverse`, `D1HChartResidualC2`) take one extra binder. No new content;
surfaces a fact the constructor already proved.

### b1 — `dln_hchart_residual_c2_deriv` (`lean/DLNFibre/DLN/RLCT/Validate/D1ResidualDerivExpose.lean`)
The `dln_hchart_residual_c2` construction re-run through the derivative-exposing chart corollary
(`rlctAtOn_eq_of_contDiff_chart_rinv_fix_deriv`), ADDITIONALLY exposing

    HasFDerivAt (fun t => q (0, t)) (residDerivL) t0,   residDerivL := dResidPolyZero ∘ f'.symm ∘ sliceMapCLM

(`f' = chartFDerivEquiv`). Route: the bump-locality germ `q =ᶠ residPolyZeroVec ∘ Ψsymm ∘ splitHomeo.symm`
near `w0` + the chain rule on the three factors (`sliceMapCLM` linear; `HasFDerivAt Ψsymm f'.symm 0`;
`HasFDerivAt residPolyZeroVec (dResidPolyZero) 0`), transported by `HasFDerivAt.congr_of_eventuallyEq`.
Supporting API (same file): `sliceMapLin`/`sliceMapCLM` (+ `range = W = {z : z (ec j) = 0}`, the `b2`
`inj`), `residPiZero`/`residPolyZeroVec` (= `rawResidVec … Ψsymm` as a flat-point function) + their
derivative CLMs `dResidPiZero`/`dResidPolyZero`.

### b1→b2 close — `residJacobian_rank_eq` (`lean/DLNFibre/DLN/RLCT/Validate/D1ResidualRankIdentity.lean`)
At an optimal `v` with the invertible flat-Jacobian minor `(er, ec)`:

    ∃ q t0, (C² + q(0,t0)=0 + RLCT-transfer) ∧ (jacResid (q(0,·)) t0).rank = (jacFlatL2 H v).rank − m,

`m = nRegL2 H r` at the use-site. Assembles: the banked bridge `jacResid_rank_eq_of_hasFDerivAt` (b1's
`HasFDerivAt` ⟹ `.rank = finrank(range residDerivL)`) ▸ the composite match `euclidReadout(residDerivL) =
zeroSel er' ∘ Tresid ∘ f'.symm ∘ sliceMapLin` ▸ the network-free b2 `DLNFibre.Core.residual_finrank_eq`
(⟹ `= finrank(range Tresid) − m`) ▸ `finrank_range_Tresid_eq` (⟹ `= jacFlatL2.rank`). The b2 hypotheses
are discharged in-file: `hP` = `chartFDerivEquiv_sel_eq_Tresid` (from `dChartΦcoord_sel`); `hinjW` =
`range_sliceMapLin`; `hsurj` = `surjective_selRowProj_comp_Tresid` (invertible `(er,ec)` minor ⟹ the
selected functionals have full row rank `m`, via the transpose-column-subset bound + `rank_of_isUnit`).

`#print axioms residJacobian_rank_eq` / `dln_hchart_residual_c2_deriv` = `[propext, Classical.choice,
Quot.sound]` (forced, clean-three, no `sorryAx`, no new axiom).

## The precise REMAINING runway to close `hrank₂` + LEAF 2

`hrank₂` (from `d1ge_L2_rect_two_peel`, `D1RectHDomProducer.lean`) is
`extraCountRect (H0−r)(H2−r) a b ≤ (jacResid (q(0,·)) t0).rank`. With `residJacobian_rank_eq` giving
`= (jacFlatL2 H v).rank − m`, `hrank₂` reduces to:

1. **b3 — the exact middle-stratum rank count** `(jacFlatL2 H v).rank = (r+b)·H0 + (r+a)·H2 − (r+a)(r+b)`
   at a middle-stratum optimal `v` with layer-rank rises `(a,b)`, whence
   `(jacFlatL2 H v).rank − nRegL2 H r = extraCountRect (H0−r)(H2−r) a b` (`extraCountRect M0 M2 a b =
   a·M2 + b·M0 − a·b`; the honest-subtraction cross-pairing arithmetic is banked in `D1RectValueArith`).
   Only the LOWER bound `nReg ≤ jacFlatL2.rank` is banked (`nReg_le_jacFlatL2_rank`); the EXACT rank at a
   general middle stratum is **genuine new content** (the DLN loss-entry Jacobian rank formula), NOT
   mechanical — a substantial linear-algebra / gauge-image build in the spirit of
   `nReg_le_finrank_range_jointDiffL2` but computing the rank exactly, not just bounding it below.
2. **`hInterface`** (R1 degraded-core at `M' = MprimeRect (H−r) a b` on the built second-peel residual) and
   **`hRne`** (slice non-vanishing) — each independently open, sequencing on b3 + the second-peel build.
3. **The `(a,b)` extraction + ∀-`v` wiring** to `d1ge_L2_rect_two_peel` then `HeadlineL2Assembly.lean:107`.
   Note the gate `hrank₂` quantifies over an ARBITRARY chart `q` matching the signature, while the producer
   builds its own; the wiring must instantiate at the producer's `q` (the same construction `residJacobian_
   rank_eq` runs), so this is not a pure `exact` — it re-threads the producer.

## Build status
`D1ResidualDerivExpose` + `D1ResidualRankIdentity` green in import-closure (3012 jobs, exit 0); `S1IFTChart`
change green in the full `DLNFibre` closure. NOT yet wired into the aggregator (`DLNFibre.lean` single-writer)
or `AxCheck` — controller wiring: add `import DLNFibre.DLN.RLCT.Validate.D1ResidualRankIdentity` at the end of
`DLNFibre.lean`, and (optionally) `#print axioms residJacobian_rank_eq` to `AxCheck.lean`.

## Pointer for the next hand
`hrank₂`'s sole remaining CORE-geometry content is **b3** (the exact middle-stratum `rank(jacFlatL2)`). Once
built, `hrank₂` closes: `residJacobian_rank_eq` gives `.rank = jacFlatL2.rank − m`, b3 gives
`jacFlatL2.rank − m = extraCountRect`, done. Then `hInterface` + `hRne` + the `(a,b)` extraction + the
∀-`v` wiring finish LEAF 2 on the validated two-peel chain.

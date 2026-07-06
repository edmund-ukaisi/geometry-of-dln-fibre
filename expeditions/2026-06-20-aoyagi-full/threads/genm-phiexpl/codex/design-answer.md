**Q1. Invertible Derivative**

Yes: avoid the Jacobian determinant. Prove explicit local inverse germs and differentiate them.
Use `HasFDerivAt.comp`, `HasFDerivAt.congr_of_eventuallyEq`, `HasFDerivAt.unique`, `hasFDerivAt_id` (confirmed v4.29).
From `Ψ ∘ Φ =ᶠ id` get `B.comp A = ContinuousLinearMap.id ℝ E`; from `Φ ∘ Ψ =ᶠ id` get `A.comp B = id`.
Build the equiv by:
```lean
(LinearEquiv.ofLinear A.toLinearMap B.toLinearMap hAB hBA).toContinuousLinearEquiv
```
`LinearEquiv.ofLinear` and `LinearEquiv.toContinuousLinearEquiv` are confirmed v4.29.
Then `convert hΦA` or `simpa [f']` to get `HasFDerivAt Φ (f' : E →L[ℝ] E) wstar`.
I would not use a “local homeomorph + smooth inverse implies invertible fderiv” route; Mathlib has related IFT APIs, but this direct derivative-of-identities route is shorter and deterministic.

**Q2. Global ContDiff**

Use (a): bump-globalise the rational raw map. This is exactly what your banked
`exists_contDiff_eventuallyEq_of_contDiffOn` is for.
Prove `ContDiffOn ℝ 2 Φraw U` on `U = {det X ≠ 0} ∩ {det M11 ≠ 0}`, then obtain global `Φ`.
Derivative survives by `HasFDerivAt.congr_of_eventuallyEq` (confirmed).
For rational smoothness use `ContDiffOn.inv`, `ContDiffAt.inv`, `ContDiff.inv`, plus `.add/.sub/.mul/.sum` (confirmed).
For matrix inverse, prove entries as `det⁻¹ • adjugate` if no local helper exists; avoid relying on global `Matrix.inv`.
Do not restructure to polynomial Φ unless you are willing to lose the explicit core again; it moves pain back into `qₑ`/germ algebra.

**Q3. Blocks vs Flat Coords**

Define the chart on a block product type, then conjugate by linear equivalences to `Fin (flatDim H) → ℝ`.
Use `LinearEquiv.toContinuousLinearEquiv`, `ContinuousLinearEquiv.prodCongr`, `ContinuousLinearEquiv.contDiff` (confirmed).
Localize all `Fin r ⊕ Fin (H_s-r)` casts inside one “block split” API; after that, no entrywise casts in the main proof.
Prefer arbitrary selected row/hidden/column split equivalences over literal top-left coordinates.
Trap: do not let `HMul` infer dimensions through `Fin.last 2`; name `H0 H1 H2` and expose block types explicitly.
For block identities, use `ext i j; simp [Matrix.mul_apply, Matrix.fromBlocks, Fin.sum_univ_*]`; do not expect `ring_nf` to solve dependent matrix casts.

**Q4. Common Invertible Pivot**

The common pivot is true, but not from `rank A0 ≥ r` and `rank A1 ≥ r` alone.
Choose an invertible product minor `B[I,J]`; Cauchy-Binet gives some hidden `K` with
`det A0[I,K] * det A1[K,J] ≠ 0`, hence `X` and `S` invertible, and `M11 = B[I,J]` invertible.
I did not confirm a v4.29 rectangular Cauchy-Binet theorem; likely fallback is a local `Matrix.det_apply` expansion lemma (high effort).
Lean-minimal route: do not WLOG to top-left; carry `I,K,J` split equivalences through the chart.
If you insist on WLOG, use `Equiv.extendSubtype` (confirmed) plus row/hidden/column parameter homeomorphism RLCT invariance; that is more code.
No, choosing only `M11` invertible is not enough for this explicit reduced-factor chart; you still need `X⁻¹` or a symmetric variant using `S⁻¹`.

**Q5. Overall**

The decomposition is mathematically sound in the positive reduced-width case.
LOUD CAVEAT: the downstream `hRne` is false if any reduced width is zero in a way making `dlnLoss (H-r) 0` identically zero, e.g. `H1 = r`.
Your theorem statement has no `∀ s, r < H s`, so you need a boundary branch or add/derive a usable positivity hypothesis before calling `d1ge_L2_hAtV_of_explicit_chart`.
Under `∀ s, r < H s`, prove `hRne` from `dlnLoss_deepest_core_ae_ne_zero` or `MvPolynomial.ae_eval_ne_zero` (both banked/confirmed in repo).
Highest line-count risk: the exact flat/block germ `lossFlatShift =ᶠ (∑p²+∑q²) ∘ Φ`, not the determinant.
Second-highest risk: the Cauchy-Binet/common-pivot lemma if not already banked.

**LEANEST DECOMPOSITION**

1. `widths_le_of_rank_prod_L2 : hopt → B.rank=r → r≤H0 ∧ r≤H1 ∧ r≤H2` [build] low
2. `exists_common_L2_pivot : ∃ I K J, det A0[I,K]≠0 ∧ det B[I,J]≠0` [build] high
3. `blockFlatEquiv_L2 : Flat H ≃L[ℝ] L2Blocks H r I K J` [build] med
4. `schurChartRaw_contDiffOn : ContDiffOn ℝ 2 Φraw U` [build] med
5. `derivEquiv_of_eventual_inverse : Ψ∘Φ=ᶠid → Φ∘Ψ=ᶠid → ∃ f', HasFDerivAt Φ f' 0` [build] low
6. `schurChart_global : ∃ Φ, ContDiff ℝ 2 Φ ∧ Φ =ᶠ Φraw ∧ HasFDerivAt Φ f' 0` [banked/build] med
7. `schur_loss_germ_L2 : lossFlatShift H B v =ᶠ[𝓝 0] fun w => F (Φ w)` [build] high
8. `schur_slice_factor_L2 : ∑ qₑ (0,t)^2 = dlnLoss (H-r) 0 (core t)` [banked/build] med
9. `schur_slice_hRne_or_boundary_L2 : hpos → hRne; ¬hpos → boundary conclusion` [build] high
10. `d1ge_L2_hAtV_explicit` via `d1ge_L2_hAtV_of_explicit_chart` [banked/build] low
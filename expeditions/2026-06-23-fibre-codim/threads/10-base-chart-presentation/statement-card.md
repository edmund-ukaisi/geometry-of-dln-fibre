# Statement card — G2-1 pivot-chart Schur parametrization

Module: `lean/DLNFibre/Core/DeterminantalChart.lean` @ `9be0eb3c842f7edd65bb2d004c0eca24e1c6bfb2`
(branch `expedition/fibre-codimension`). Axiom-clean `[propext, Classical.choice, Quot.sound]`;
zero sorry. Not yet in the aggregator.

---

> **Claim (headline — the pivot-chart Schur rank criterion).** Over a field `k`, with the
> top-left block `Δ` of a block matrix `M = [[Δ, B12], [B21, B22]]` invertible, `M` has rank
> exactly `card Δ` (the size of `Δ`) **iff** the Schur complement vanishes,
> `B22 = B21 · Δ⁻¹ · B12`.
>
> - **Lean:** `DLNFibre.Core.rank_fromBlocks_eq_card_iff_schur`
>   (and the `Δ⁻¹`-form `rank_fromBlocks_eq_card_iff_schur_inv`, stated under `IsUnit Δ.det`).
> - **Gloss.** For `Δ : Matrix m m k` with `[Invertible Δ]` (resp. `IsUnit Δ.det`),
>   `B12 : Matrix m n k`, `B21 : Matrix l m k`, `B22 : Matrix l n k`:
>   `(Matrix.fromBlocks Δ B12 B21 B22).rank = Fintype.card m ↔ B22 = B21 * ⅟Δ * B12`
>   (resp. `… ↔ B22 = B21 * Δ⁻¹ * B12`). `card m` is `r`, the size of the pivot block.
> - **Proved.** The full `iff`, unconditionally over any field, via LDU + block-diagonal rank
>   additivity. No char-0 / alg-closed hypothesis.
> - **Assumed.** `Δ` invertible (= the pivot chart `U`). This is the chart condition, not an
>   extra hypothesis — off `U` the criterion does not apply.
> - **Cited.** none. (Mathlib supplies the LDU factorization `fromBlocks_eq_of_invertible₁₁`,
>   `rank_mul_eq_left/right_of_isUnit_det`, `range_prodMap`, `Module.finrank_prod`; the
>   block-diagonal rank additivity `rank_fromBlocks_zero` is proved here, not cited.)
> - **Deferred.** The localized-coordinate-ring `AlgEquiv` (G2-3 feeder). This card is the
>   *matrix/variety-level* presentation, NOT the localized ring isomorphism the flatness route
>   consumes (see `ChartFlatnessProbe`). A point-set bijection is not a ring-level trivialization.
> - **Status.** sorry-free + reviewed (fidelity PASS, reviewer + decorrelated Codex, 2026-06-23).

---

> **Claim (reusable brick — block-diagonal rank additivity).** Over a field, the rank of a
> block-diagonal matrix is the sum of the ranks of its diagonal blocks.
>
> - **Lean:** `DLNFibre.Core.rank_fromBlocks_zero`
> - **Gloss.** `(Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank` for `A : Matrix m n k`,
>   `D : Matrix l o k` over a field `k`.
> - **Proved.** The full identity. Missing in Mathlib v4.29; proved by conjugating `mulVecLin`
>   to `A.mulVecLin.prodMap D.mulVecLin` (via `LinearEquiv.sumArrowLequivProdArrow`) then
>   `LinearMap.range_prodMap` + `Module.finrank_prod`.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free + reviewed (fidelity PASS, reviewer + decorrelated Codex, 2026-06-23).

---

> **Claim (parametrization).** The pivot chart `Mat^{rk=r} ∩ U` is in explicit bijection with
> `GL_r × Mat_{r×(q−r)} × Mat_{(p−r)×r}` — the three free blocks `(Δ, B12, B21)`, with `B22`
> Schur-forced.
>
> - **Lean:** `DLNFibre.Core.pivotRankChartEquiv` (chart `DLNFibre.Core.pivotRankChart`).
> - **Gloss.** `pivotRankChart k m l n := {M | M.rank = Fintype.card m ∧ IsUnit M.toBlocks₁₁.det}`,
>   and `pivotRankChartEquiv : {M // M ∈ pivotRankChart k m l n} ≃ {Δ : Matrix m m k //
>   IsUnit Δ.det} × Matrix m n k × Matrix l m k`, sending `M ↦ (toBlocks₁₁ M, toBlocks₁₂ M,
>   toBlocks₂₁ M)` with inverse `(Δ, B12, B21) ↦ fromBlocks Δ B12 B21 (B21·Δ⁻¹·B12)`.
> - **Proved.** A bijection of types (`Equiv`): both round-trips, including that the `(2,2)` block
>   is Schur-forced on the chart (from the headline `iff`).
> - **Assumed.** The chart condition (det of top-left block a unit).
> - **Deferred.** The variety/scheme structure of the bijection (it is an `Equiv` of `k`-points,
>   not yet a morphism of varieties or a ring `AlgEquiv`).
> - **Status.** sorry-free + reviewed (fidelity PASS, reviewer + decorrelated Codex, 2026-06-23).

---

> **Claim (dimension cross-check).** The parameter space of `pivotRankChartEquiv` has
> `k`-dimension `δ = r(p+q−r)`.
>
> - **Lean:** `DLNFibre.Core.finrank_pivotRankChart_params` (the finrank) +
>   `DLNFibre.Core.dim_params_eq_delta` (the arithmetic `r² + r(q−r) + (p−r)r = r(p+q−r)`).
> - **Gloss.** `finrank k (Matrix m m k × Matrix m n k × Matrix l m k) = (card m)² +
>   (card m)(card n) + (card l)(card m)`; and that sum equals `r(p+q−r)` with `r = card m`,
>   `p = card l + r`, `q = card n + r`.
> - **Proved.** The finrank identity of the affine parameter space, and the δ arithmetic.
> - **Deferred.** That the chart's **variety** dimension equals this parameter-space dimension —
>   needs the AG step "a Zariski-open subset has the dimension of its ambient space" (`{Δ //
>   IsUnit Δ.det}` open in `Matrix m m`). That is the variety-dimension engine, not done here.
> - **Status.** sorry-free + reviewed (fidelity PASS, reviewer + decorrelated Codex, 2026-06-23).

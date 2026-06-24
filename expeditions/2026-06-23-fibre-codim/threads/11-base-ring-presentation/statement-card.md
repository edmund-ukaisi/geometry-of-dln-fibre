# Statement card — G2-2 sub-rung 1: the bordered Schur minor (foundation)

This is the foundational, genuinely-new piece of G2-2 (the localized base ring presentation): the
bordered Schur minor identity over any commutative ring, and its corollary that the Schur expression
vanishes on the rank-`≤ r` determinantal locus. It is the generator-free handle that replaces
determinantal-ideal generating-set theory (absent in Mathlib v4.29). Module:
`lean/DLNFibre/Core/DeterminantalChartRing.lean`.

---

> **Claim (bordered Schur minor identity).** Over any commutative ring, the determinant of the
> bordered `(r+1)×(r+1)` matrix `[[Δ, u], [v, d]]` (`r×r` block `Δ`, column `u`, row `v`, scalar
> corner `d`) equals `d · det Δ − v ⬝ adjugate Δ ⬝ u`. No invertibility of `Δ`.
>
> - **Lean:** `DLNFibre.Core.det_fromBlocks_scalar_eq`
>   (`lean/DLNFibre/Core/DeterminantalChartRing.lean` @ `<commit-sha>`)
> - **Gloss.** For `Δ : Matrix (Fin r) (Fin r) α`, `u : Matrix (Fin r) Unit α`,
>   `v : Matrix Unit (Fin r) α`, `d : Matrix Unit Unit α` over a `CommRing α`,
>   `(fromBlocks Δ u v d).det = d () () * Δ.det − (v * adjugate Δ * u) () ()` (packaged as
>   the predicate `BorderedId Δ u v d`).
> - **Proved.** The identity unconditionally over any commutative ring, via the universal-coefficient
>   route: the field case (`borderedId_of_det_ne_zero`, `det Δ ≠ 0` ⟹ via `det_fromBlocks₁₁` +
>   `mul_adjugate`); transfer along ring homs (`borderedId_map`) and its injective reflection
>   (`borderedId_of_map`); the generic `(r+1)×(r+1)` matrix over `ℤ` is a domain whose fraction field
>   has nonzero (hence invertible) generic pivot, where the field case applies, then descend +
>   specialise by entry evaluation.
> - **Assumed.** none.
> - **Cited.** none (Mathlib lemmas: `det_fromBlocks₁₁`, `mul_adjugate`, `RingHom.map_det`,
>   `RingHom.map_adjugate`, `det_mvPolynomialX_ne_zero`, `IsFractionRing.injective` — all reproved
>   upstream in Mathlib, used as engine).
> - **Deferred.** none for this statement.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

> **Claim (Schur expression vanishes on `Mat^{rk ≤ r}`).** For `M : Mat_{p×q}` over a field with
> `rank M ≤ r`, any pivot rows `pr`, pivot columns `pc`, extra row `a`, column `b`: the Schur
> expression `M a b · det M[pr,pc] − (M[a,pc] ⬝ adjugate M[pr,pc] ⬝ M[pr,b])` is zero.
>
> - **Lean:** `DLNFibre.Core.schur_expr_eq_zero_of_rank_le`
>   (`lean/DLNFibre/Core/DeterminantalChartRing.lean` @ `<commit-sha>`)
> - **Gloss.** The Schur expression is the determinant of the bordered `(r+1)×(r+1)` submatrix
>   (`det_fromBlocks_scalar_eq`), which vanishes because it is an `(r+1)`-minor of a rank-`≤ r`
>   matrix (`submatrix_det_eq_zero_of_rank_le`, landed in `Core.RankLocusClosed`).
> - **Proved.** The vanishing unconditionally, for every choice of pivots and extra row/column.
> - **Assumed.** `rank M ≤ r` (the determinantal-locus membership; the only hypothesis).
> - **Cited.** none.
> - **Deferred.** This is the per-point precursor of `relA ∈ vanishingIdeal(Σ̄^r)`; the full
>   localized-ideal equality `I_loc = J` and the base-ring `AlgEquiv` are the next sub-rung (NOT in
>   this module).
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

**Scope note.** This module lands the bordered-minor foundation of G2-2 (the crux friction the
controller flagged). The remaining G2-2 deliverables — the localized base presentation
`R_base,loc[detΔ⁻¹] ≅ₐ free Schur localization` via the Schur graph ideal `J`, the ideal equality
`I_loc = J` by height comparison (`Ideal.height_strict_mono_of_is_prime`), and the re-export of the
landed base facts (`isPrime_…`/`varietyDim_… = δ` from `Core.DeterminantalStratumDim`) — are the
next sub-rung, building directly on `schur_expr_eq_zero_of_rank_le`.

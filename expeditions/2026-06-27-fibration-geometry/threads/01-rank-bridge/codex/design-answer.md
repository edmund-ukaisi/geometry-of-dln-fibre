GO-WITH-CHANGES: the theorem is right, but make the “rank ≥ r iff some r-minor is nonzero” step an explicit lemma, with a real `r = 0` proof path.

1. Yes, correct, assuming your global `Mκ.rank ≤ r` lemma and an explicit r-minor existence lemma.
`rankROpen` is exactly “some `r × r` chart minor is not in `P.asIdeal`”, hence nonzero in κ.
Then automatic `rank ≤ r` turns “rank ≥ r” into “rank = r”.
`r = 0` is mathematically fine: `Fin 0` selectors exist uniquely, `det` is `1`, so the open is `⊤`.
Lean still likely wants a case split for proving `r ≤ rank → ∃ nonzero r-minor`.
Status: inference; banked zero-locus/residue facts as you stated.

2. Use a local bridge lemma:
`((U.map φ).submatrix s t).det = φ ((U.submatrix s t).det)`.
`RingHom.map_det` is the right determinant lemma; orientation is usually `φ A.det = (A.map φ).det` [confident, current-docs confirmed; verify v4.29].
For map/submatrix, do not rely on a name: it should be `rfl`/`change`/`ext i j; rfl`; `Matrix.submatrix_map` is only a guess.
Then unfold `ΔPdeepAt`, `chartDsigAt`, `φ`, `mk`.
Current docs confirm `RingHom.map_det`, not v4.29 specifically. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html))

3. Mostly automatic.
Current `Matrix.rank_of_isUnit` needs `Fintype`, `DecidableEq`, `CommSemiring`, `StrongRankCondition`; a field supplies the ring/rank-condition side [confident; verify v4.29].
Add `haveI : P.asIdeal.IsPrime := P.isPrime` before defining/using κ if inference stalls.
`Fin r` gives `Fintype`/`DecidableEq`; κ should give `Field`.
You may need the import containing `Matrix.isUnit_iff_isUnit_det`.
Current docs confirm `rank_of_isUnit`, `rank_submatrix_le`, and `isUnit_iff_isUnit_det`. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Rank.html))

4. No serious universe pitfall expected.
`Localization.AtPrime P.asIdeal` and `IsLocalRing.ResidueField` live in the same universe as `R` [confident; current-docs confirmed for these definitions, verify v4.29].
`Matrix.rank` is universe-polymorphic enough here.
The only practical issue is typeclass inference, not universes.
Use explicit `haveI` for `P.asIdeal.IsPrime`/`Field κ` if Lean hesitates.
Current docs show `ResidueField R : Type u` and `Localization.AtPrime P : Type u`. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LocalRing/ResidueField/Defs.html))

5. Best packaging:
state `rank_le_residue : Mκ.rank ≤ r` separately.
Then prove `mem_rankROpen_iff_rank_ge : P ∈ rankROpen d r ↔ r ≤ Mκ.rank`.
Headline theorem should be `mem_rankROpen_iff_rank_eq`, obtained by antisymmetry with `rank_le_residue`.
This is the cleanest proof architecture and the most useful public “rank bridge”.
Status: inference/design recommendation.

6. Do not count on definitional equality.
`φ = (algebraMap R κ).comp mk` may be propositionally equal to `algebraMap (MvPolynomial _ k) κ` if the quotient algebra/tower instances line up.
Use `IsScalarTower.algebraMap_eq` or `IsScalarTower.algebraMap_apply` [confident current-docs; verify v4.29].
But for this proof, explicit `φ` is cleaner and avoids instance search churn.
Current docs confirm those tower lemmas. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Tower.html))

Corrected lemma chain, names only:

`Set.mem_compl_iff`, `PrimeSpectrum.mem_zeroLocus`, `Set.range_subset_iff`, `not_forall`, `Ideal.algebraMap_residueField_eq_zero`.

`RingHom.map_det` [confident], `rfl`/`change` for map-submatrix, `ΔPdeepAt`, `chartDsigAt`.

`isUnit_iff_ne_zero` [confident], `Matrix.isUnit_iff_isUnit_det` [confident], `Matrix.rank_of_isUnit` [confident], `Matrix.rank_submatrix_le` or banked `rank_submatrix_le_rank`.

`rank_le_iff_forall_submatrix_det_eq_zero` at `n` when `r = n+1`; `not_forall`; separate `r = 0` via `Matrix.det_isEmpty` or `Matrix.det_eq_one_of_card_eq_zero` [confident/verify].
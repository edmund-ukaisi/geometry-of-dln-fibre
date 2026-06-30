import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# `DLNFibre.Core.LinearAlgebra.BaseChange` — base change preserves the rank of a linear map

A base-change rank brick (`finrank_range_baseChange`): for a `k`-linear `f` between `k`-spaces
and a field extension `K/k`, `finrank K (range (f.baseChange K)) = finrank k (range f)` — base
change preserves the rank of a linear map. This is the rank-side tool the A4.3 generic-Jacobian
bound consumes (`genericDifferentialRank` over `K = FractionRing B` vs `finrank` over `k`).

This is the **linear-map** base-change-rank variant, one of three the engine keeps **visibly
distinct** (name = content):

* **V1 — entrywise matrix** (`Matrix.rank_map_eq_of_injective`, `Core.Matrix.RankMinors`):
  `(B.map ι).rank = B.rank` for an injective ring hom `ι : R →+* S` applied entrywise to a matrix.
* **V2 — linear-map rank under scalar extension** (`finrank_range_baseChange`, *here*):
  `finrank K (range (f.baseChange K)) = finrank k (range f)` for `f : V →ₗ[k] W` and a field
  extension `K/k`. The tensor `K ⊗ f`, not an entrywise map nor a span of a family.
* **V3 — differential-family span** (currently inlined in
  `JacobianTrdeg.diffIndepCriterion_proof`, to be extracted): span-dimension of a family of
  differentials under base change.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Module LinearMap in
/-- **Base change preserves the rank of a linear map** (the **linear-map** base-change-rank
variant, distinct from the entrywise-matrix variant `Matrix.rank_map_eq_of_injective` and from the
differential-family-span variant in `JacobianTrdeg.diffIndepCriterion_proof`). For `f : V →ₗ[k] W`
between `k`-modules with `range f` finite-dimensional, and a field extension `K/k`, the base-changed
map `f.baseChange K` (`= K ⊗ f`) has `finrank K (range (f.baseChange K)) = finrank k (range f)`.
Factor `f = subtype ∘ rangeRestrict`; base change preserves the surjection (`lTensor_surjective`, so
the range of the base-changed `rangeRestrict` is `⊤`) and the injection (over the flat `K`, via
`Flat.lTensor_preserves_injective_linearMap`, so the range of the base-changed `subtype` is
`≅ K ⊗ range f`); then `Module.finrank_baseChange`. The rank-side tool for the A4.3 bound. -/
theorem finrank_range_baseChange {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (K : Type*) [Field K] [Algebra k K]
    (f : V →ₗ[k] W) [Module.Finite k (LinearMap.range f)] :
    finrank K (LinearMap.range (f.baseChange K)) = finrank k (LinearMap.range f) := by
  have hfac : f.baseChange K
      = (LinearMap.range f).subtype.baseChange K ∘ₗ f.rangeRestrict.baseChange K := by
    rw [← LinearMap.baseChange_comp, subtype_comp_codRestrict]
  rw [hfac, LinearMap.range_comp]
  have hsurj : LinearMap.range (f.rangeRestrict.baseChange K) = ⊤ := by
    rw [LinearMap.range_eq_top, LinearMap.baseChange_eq_ltensor]
    exact lTensor_surjective K f.surjective_rangeRestrict
  rw [hsurj, Submodule.map_top]
  have hinj : Function.Injective ((LinearMap.range f).subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

end DLNFibre.Core

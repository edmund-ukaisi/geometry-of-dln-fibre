import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Real.Basic

/-!
# `DLNFibre.Core.ResidualRank` — the network-free residual-Jacobian rank identity (the `b2` brick)

A self-contained linear-algebra fact underneath the L = 2 D1 second-peel gate `hrank₂`. It is the
`b2` brick of the two-peel D1 `≥`-leg: for the residual composite

    L = [T with the selected `er`-rows zeroed] ∘ P⁻¹ ∘ [complement injection]

(where `T` is the loss-entry differential `Dg(v)`, `P = DΦ(0)` the flat IFT-chart derivative, and
the `(er, ec)` minor is invertible), the rank is EXACTLY `rank T − k` with `k` the number of
selected rows. Certified numerically by `hrank2_residual_rank_certificate.py` (0 fails / 400 random
abstract matrices, and 0 fails on the DLN composite at ~860 middle-stratum optima).

## The clean linear-algebra content (no `P⁻¹` matrix built)

The only property of `P` the identity uses is the SELECTED-coordinate relation
`(P x)(ec j) = (T x)(er j)` (`hP`): the chart's selected coordinates read the selected loss-entry
rows. Under it, `P⁻¹` carries the complement coordinate subspace `W = {z : z (ec j) = 0}` exactly
onto `ker (πR ∘ T)`, where `πR : (Fin m → ℝ) →ₗ (Fin k → ℝ)` selects the `er`-rows; and on that
kernel the zeroed map `Tres` agrees with `T` (the selected rows already vanish there). So

    range L = T '' (ker (πR ∘ T)),

and rank-nullity twice gives `finrank (range L) = rank T − rank (πR ∘ T)`. The minor invertibility
enters ONLY to make `πR ∘ T` surjective (rank `k`), via the `k × k` submatrix being nonsingular.

`finrank_map_ker_comp` isolates the network-free rank-nullity core; `residual_finrank_eq` is the
composite identity stated for the abstract chart data. Both are generic over `ℝ` and finite `Fin`
dimensions. No DLN / matrix-chart dependency.
-/

open Module LinearMap Submodule

namespace DLNFibre.Core

section RankNullityCore

variable {K V V₂ V₃ : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]

/-- **The rank-nullity core.** For linear maps `T : V →ₗ V₂` and `S : V →ₗ V₃` with `ker T ≤ ker S`,
the image of `ker S` under `T` has dimension `rank T − rank S`:

    finrank (Submodule.map T (ker S)) = finrank (range T) − finrank (range S).

Proof: `T.domRestrict (ker S)` has range `map T (ker S)` and kernel `(ker T).comap (ker S).subtype`,
which — since `ker T ≤ ker S` — is `≃ₗ ker T`; rank-nullity on it gives
`finrank (map T (ker S)) + finrank (ker T) = finrank (ker S)`, and each `finrank (ker ·)` is
`finrank V − rank ·`. -/
theorem finrank_map_ker_comp (T : V →ₗ[K] V₂) (S : V →ₗ[K] V₃)
    (hle : LinearMap.ker T ≤ LinearMap.ker S) :
    finrank K (Submodule.map T (LinearMap.ker S))
      = finrank K (LinearMap.range T) - finrank K (LinearMap.range S) := by
  classical
  -- rank-nullity on the restriction of `T` to `ker S`.
  have hrn := (T.domRestrict (LinearMap.ker S)).finrank_range_add_finrank_ker
  -- range of the restriction is `map T (ker S)`.
  have hrange : LinearMap.range (T.domRestrict (LinearMap.ker S))
      = Submodule.map T (LinearMap.ker S) := by
    rw [LinearMap.range_domRestrict]
  -- kernel of the restriction `≃ₗ ker T` (as `ker T ≤ ker S`).
  have hkereq : LinearMap.ker (T.domRestrict (LinearMap.ker S))
      = (LinearMap.ker T).comap (LinearMap.ker S).subtype := by
    rw [LinearMap.ker_domRestrict]
  have hkerfin : finrank K (LinearMap.ker (T.domRestrict (LinearMap.ker S)))
      = finrank K (LinearMap.ker T) := by
    rw [hkereq]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  rw [hrange, hkerfin] at hrn
  -- `finrank (ker S) = finrank V − rank S`, `finrank (ker T) = finrank V − rank T`.
  have hkerS : finrank K (LinearMap.ker S) = finrank K V - finrank K (LinearMap.range S) := by
    have := S.finrank_range_add_finrank_ker; omega
  have hkerT : finrank K (LinearMap.ker T) = finrank K V - finrank K (LinearMap.range T) := by
    have := T.finrank_range_add_finrank_ker; omega
  have hrangeT_le : finrank K (LinearMap.range T) ≤ finrank K V := by
    have := T.finrank_range_add_finrank_ker; omega
  have hrangeS_le : finrank K (LinearMap.range S) ≤ finrank K V := by
    have := S.finrank_range_add_finrank_ker; omega
  omega

end RankNullityCore

section Composite

variable {N m k : ℕ}

/-- **The selected-row projection** `πR : (Fin m → ℝ) →ₗ (Fin k → ℝ)`, `πR y j = y (er j)`. -/
def selRowProj (er : Fin k → Fin m) : (Fin m → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun y := fun j => y (er j)
  map_add' x y := by funext j; simp
  map_smul' c x := by funext j; simp

@[simp] theorem selRowProj_apply (er : Fin k → Fin m) (y : Fin m → ℝ) (j : Fin k) :
    selRowProj er y j = y (er j) := rfl

/-- **Row-zeroing** `zeroSel : (Fin m → ℝ) →ₗ (Fin m → ℝ)`: kill the coordinates in `range er`,
keep the rest. Linear projection. -/
noncomputable def zeroSel (er : Fin k → Fin m) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun y := fun i => if (∃ j, er j = i) then 0 else y i
  map_add' x y := by
    funext i; by_cases h : ∃ j, er j = i <;> simp [h]
  map_smul' c x := by
    funext i; by_cases h : ∃ j, er j = i <;> simp [h]

theorem zeroSel_apply (er : Fin k → Fin m) (y : Fin m → ℝ) (i : Fin m) :
    zeroSel er y i = if (∃ j, er j = i) then 0 else y i := rfl

/-- On any `y` whose selected rows already vanish (`y (er j) = 0`), `zeroSel` is the identity. -/
theorem zeroSel_eq_self_of_sel_zero (er : Fin k → Fin m) {y : Fin m → ℝ}
    (hy : ∀ j, y (er j) = 0) : zeroSel er y = y := by
  funext i; rw [zeroSel_apply]
  by_cases h : ∃ j, er j = i
  · obtain ⟨j, rfl⟩ := h; rw [if_pos ⟨j, rfl⟩, hy j]
  · rw [if_neg h]

/-- **`map` of a submodule fixed pointwise by a linear map is itself.** If `f y = y` for every
`y ∈ Q`, then `Submodule.map f Q = Q`. -/
theorem map_eq_self_of_fixed {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : M →ₗ[R] M) (Q : Submodule R M) (hfix : ∀ y ∈ Q, f y = y) :
    Submodule.map f Q = Q := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩; rw [hfix y hy]; exact hy
  · intro y hy; exact ⟨y, hy, hfix y hy⟩

/-- **The residual composite = image of `ker (πR ∘ T)` under `T`.** For `T`, injective selectors
`er, ec`, an invertible `P : (Fin N → ℝ) ≃ₗ (Fin N → ℝ)` with the selected-coordinate relation
`hP : (P x)(ec j) = (T x)(er j)`, and a complement injection `inj` whose range is the complement
coordinate subspace `W = {z : z (ec j) = 0}` (`hinjW`), the residual composite

    L := zeroSel er ∘ T ∘ P.symm ∘ inj

has range `Submodule.map T (ker (selRowProj er ∘ T))`. (The `∘ inj` picks out `W`; `P.symm` carries
`W` to `ker (πR∘T)`; on that kernel the selected rows of `T·` vanish so `zeroSel` is the
identity.) -/
theorem residual_range_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : (Fin N → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (er : Fin k → Fin m) (ec : Fin k → Fin N)
    (P : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ)) (inj : V →ₗ[ℝ] (Fin N → ℝ))
    (hP : ∀ (x : Fin N → ℝ) (j : Fin k), P x (ec j) = T x (er j))
    (hinjW : LinearMap.range inj = { z : Fin N → ℝ | ∀ j, z (ec j) = 0 }) :
    LinearMap.range
        ((zeroSel er).comp (T.comp ((P.symm : (Fin N → ℝ) →ₗ[ℝ] _).comp inj)))
      = Submodule.map T (LinearMap.ker (selRowProj er |>.comp T)) := by
  classical
  -- `P.symm '' (range inj) = ker (πR ∘ T)`, element-wise via `P` bijective.
  have hPsymmW : Submodule.map (P.symm : (Fin N → ℝ) →ₗ[ℝ] _) (LinearMap.range inj)
      = LinearMap.ker (selRowProj er |>.comp T) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      -- `z ∈ range inj`, so `z (ec j) = 0`; and `P (P.symm z) = z`.
      have hz0 : ∀ j, z (ec j) = 0 := by
        have : z ∈ { z : Fin N → ℝ | ∀ j, z (ec j) = 0 } := by rw [← hinjW]; exact hz
        exact this
      rw [LinearMap.mem_ker]; funext j
      have hval : T (P.symm z) (er j) = z (ec j) := by
        rw [← hP (P.symm z) j, P.apply_symm_apply z]
      simp only [LinearMap.comp_apply, selRowProj_apply, Pi.zero_apply, LinearEquiv.coe_coe]
      rw [hval]; exact hz0 j
    · intro hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx
      -- `x = P.symm (P x)` and `P x ∈ range inj` (its `ec`-coords vanish).
      refine ⟨P x, ?_, by simp⟩
      rw [hinjW]
      intro j; rw [hP x j]; exact congrFun hx j
  -- unfold the composite's range through three `range_comp` steps.
  rw [LinearMap.range_comp, LinearMap.range_comp, LinearMap.range_comp, hPsymmW]
  -- on `ker (πR ∘ T)`, `zeroSel` fixes `map T (ker …)` pointwise.
  apply map_eq_self_of_fixed
  rintro _ ⟨x, hx, rfl⟩
  refine zeroSel_eq_self_of_sel_zero er ?_
  intro j
  have : selRowProj er (T x) = 0 := hx
  exact congrFun this j

/-- **The `b2` residual-rank identity.** With `T` a linear map `(Fin N → ℝ) →ₗ (Fin m → ℝ)`,
injective selectors `er : Fin k → Fin m`, `ec : Fin k → Fin N`, an invertible chart derivative
`P : (Fin N → ℝ) ≃ₗ (Fin N → ℝ)` whose selected coordinates read the selected loss-entry rows
(`hP`), a complement injection `inj` onto `W = {z : z (ec j) = 0}` (`hinjW`), and the minor-driven
surjectivity `hsurj : Surjective (selRowProj er ∘ T)` (the `k` selected functionals of `T` are
independent), the residual composite has rank exactly `finrank (range T) − k`:

    finrank (range (zeroSel er ∘ T ∘ P.symm ∘ inj)) = finrank (range T) − k. -/
theorem residual_finrank_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : (Fin N → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (er : Fin k → Fin m) (ec : Fin k → Fin N)
    (P : (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ)) (inj : V →ₗ[ℝ] (Fin N → ℝ))
    (hP : ∀ (x : Fin N → ℝ) (j : Fin k), P x (ec j) = T x (er j))
    (hinjW : LinearMap.range inj = { z : Fin N → ℝ | ∀ j, z (ec j) = 0 })
    (hsurj : Function.Surjective (selRowProj er |>.comp T)) :
    Module.finrank ℝ
        (LinearMap.range
          ((zeroSel er).comp (T.comp ((P.symm : (Fin N → ℝ) →ₗ[ℝ] _).comp inj))))
      = Module.finrank ℝ (LinearMap.range T) - k := by
  classical
  rw [residual_range_eq T er ec P inj hP hinjW]
  -- rank-nullity core, with `S = selRowProj er ∘ T`.
  rw [finrank_map_ker_comp T (selRowProj er |>.comp T)
    (fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [LinearMap.comp_apply, hx, map_zero])]
  -- `rank (πR ∘ T) = k` from surjectivity onto `Fin k → ℝ`.
  have hrangeS : LinearMap.range (selRowProj er |>.comp T) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [hrangeS, finrank_top, Module.finrank_pi]
  simp

end Composite

end DLNFibre.Core

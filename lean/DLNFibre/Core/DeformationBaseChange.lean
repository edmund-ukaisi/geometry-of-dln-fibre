import DLNFibre.Core.DeformationExt
import DLNFibre.Core.MatrixKaehler
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
# `DLNFibre.Core.DeformationBaseChange` — L7: `finrank (range deformationδ)` is base-change invariant

The orbit dimension `finrank_k (range (deformationδ M M))` is the rank of a fixed integer-structured
`k`-linear map (`deformationδ M N φ_i = φ_{i+1} M_i − N_i φ_i`). Under a field extension `K/k`
(`[Algebra k K]`) the entrywise base change `fun i ↦ (M i).map (algebraMap k K)` gives the SAME
integer over `K`:

    finrank K (range (deformationδ (mapTuple K M) (mapTuple K Nt)))
      = finrank k (range (deformationδ M Nt)).

This is the dimension-side of the real↔complex transfer: the orbit dimension does not depend on the
field, so `varietyDim_ℝ(orbit) = varietyDim_K(orbit)` follows from the squeeze
`varietyDim = finrank (range deformationδ)` (`Core.VoigtDischarge`) on each side.

**Route.** The banked brick `finrank_range_baseChange` (`Core.MatrixKaehler`) gives
`finrank K (range (f.baseChange K)) = finrank k (range f)`. The general conjugacy lemma
`finrank_range_eq_of_baseChange_conj` lifts it across a pair of `K`-linear equivs `cochain*_K ≅ K ⊗
cochain*_k` intertwining the two differentials; the `deformationδ`-specific input is the commuting
square `deformationδ_K (mapTuple K M) = cochainBC ∘ (deformationδ_k M).baseChange K ∘ cochainBC⁻¹`,
which holds because every `Matrix.mul` block commutes with the entrywise `algebraMap`
(`Matrix.map_mul`) and base change is a functor (`LinearMap.baseChange_tmul`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix Module TensorProduct LinearMap

universe u

/-! ## The general base-change conjugacy lemma -/

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K]

/-- **Base change preserves the range-finrank, up to conjugacy.** If a `K`-linear map `g` between
`K`-spaces is conjugate to the base change `f.baseChange K` of a `k`-linear map `f`, via `K`-linear
equivs `eV : V' ≃ₗ[K] K ⊗[k] V` and `eW : W' ≃ₗ[K] K ⊗[k] W` (intertwining
`eW ∘ g = f.baseChange K ∘ eV`), then `finrank K (range g) = finrank k (range f)`. -/
theorem finrank_range_eq_of_baseChange_conj
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {V' W' : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (f : V →ₗ[k] W) [Module.Finite k (LinearMap.range f)]
    (g : V' →ₗ[K] W')
    (eV : V' ≃ₗ[K] K ⊗[k] V) (eW : W' ≃ₗ[K] K ⊗[k] W)
    (hsq : (eW : W' →ₗ[K] K ⊗[k] W) ∘ₗ g
      = (f.baseChange K) ∘ₗ (eV : V' →ₗ[K] K ⊗[k] V)) :
    finrank K (LinearMap.range g) = finrank k (LinearMap.range f) := by
  have h1 : finrank K (LinearMap.range g)
      = finrank K (LinearMap.range ((eW : W' →ₗ[K] K ⊗[k] W) ∘ₗ g)) := by
    rw [LinearMap.range_comp]
    exact LinearEquiv.finrank_eq (eW.submoduleMap (LinearMap.range g))
  have hVtop : LinearMap.range (eV : V' →ₗ[K] K ⊗[k] V) = ⊤ :=
    LinearMap.range_eq_top.2 eV.surjective
  have h2 : LinearMap.range ((f.baseChange K) ∘ₗ (eV : V' →ₗ[K] K ⊗[k] V))
      = LinearMap.range (f.baseChange K) :=
    LinearMap.range_comp_of_range_eq_top _ hVtop
  rw [h1, hsq, h2, finrank_range_baseChange K f]

/-! ## The base-change equiv on a single matrix and on a cochain space -/

/-- `K ⊗[k] Matrix m n k ≃ₗ[K] Matrix m n K`, the entrywise base change of a matrix space, built
from the Pi base-change equivs (`Matrix m n k` is `m → n → k`). -/
noncomputable def matrixTensorEquiv (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] :
    K ⊗[k] Matrix m n k ≃ₗ[K] Matrix m n K :=
  (TensorProduct.piRight k K K (fun _ : m ↦ (n → k))).trans
    (LinearEquiv.piCongrRight (fun _ : m ↦ TensorProduct.piScalarRight k K K n))

@[simp] theorem matrixTensorEquiv_tmul (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (x : K) (A : Matrix m n k) (i : m) (j : n) :
    matrixTensorEquiv K m n (x ⊗ₜ A) i j = x * algebraMap k K (A i j) := by
  -- `(e₁.trans e₂) z = e₂ (e₁ z)` is `rfl`; `LinearEquiv.trans_apply` is blocked by the semilinear σ
  rw [show matrixTensorEquiv K m n (x ⊗ₜ A)
      = (LinearEquiv.piCongrRight (fun _ : m ↦ TensorProduct.piScalarRight k K K n))
          ((TensorProduct.piRight k K K (fun _ : m ↦ (n → k))) (x ⊗ₜ A)) from rfl]
  simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    LinearEquiv.piCongrRight_apply, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  rw [Algebra.smul_def, mul_comm]

variable {N : ℕ}

/-- The base-change equiv on a cochain space `K ⊗[k] (∀ i, Matrix … k) ≃ₗ[K] (∀ i, Matrix … K)`,
the per-component `matrixTensorEquiv` pushed through the Pi base-change equiv. -/
noncomputable def cochainTensorEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ) :
    K ⊗[k] (∀ i : ι, Matrix (Fin (a i)) (Fin (b i)) k)
      ≃ₗ[K] (∀ i : ι, Matrix (Fin (a i)) (Fin (b i)) K) :=
  (TensorProduct.piRight k K K (fun i : ι ↦ Matrix (Fin (a i)) (Fin (b i)) k)).trans
    (LinearEquiv.piCongrRight (fun i : ι ↦ matrixTensorEquiv K (Fin (a i)) (Fin (b i))))

/-- The cochain base-change equiv on a pure tensor `x ⊗ₜ φ` is `fun i ↦ x • (φ i).map (algebraMap)`,
entrywise `x * algebraMap (φ i r c)`. -/
theorem cochainTensorEquiv_tmul {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ)
    (x : K) (φ : ∀ i : ι, Matrix (Fin (a i)) (Fin (b i)) k) (i : ι)
    (r : Fin (a i)) (c : Fin (b i)) :
    cochainTensorEquiv K a b (x ⊗ₜ φ) i r c = x * algebraMap k K (φ i r c) := by
  rw [show cochainTensorEquiv K a b (x ⊗ₜ φ)
      = (LinearEquiv.piCongrRight (fun i : ι ↦ matrixTensorEquiv K (Fin (a i)) (Fin (b i))))
          ((TensorProduct.piRight k K K (fun i : ι ↦ Matrix (Fin (a i)) (Fin (b i)) k)) (x ⊗ₜ φ))
      from rfl]
  simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    LinearEquiv.piCongrRight_apply, matrixTensorEquiv_tmul]

/-! ## The cochain base-change equivs for the deformation complex -/

/-- `Φ⁰ : K ⊗[k] cochain0_k ≃ₗ[K] cochain0_K`. -/
noncomputable def cochain0TensorEquiv (d e : Fin (N + 1) → ℕ) :
    K ⊗[k] (cochain0 (k := k) d e) ≃ₗ[K] cochain0 (k := K) d e :=
  cochainTensorEquiv K e d

/-- `Φ¹ : K ⊗[k] cochain1_k ≃ₗ[K] cochain1_K`. -/
noncomputable def cochain1TensorEquiv (d e : Fin (N + 1) → ℕ) :
    K ⊗[k] (cochain1 (k := k) d e) ≃ₗ[K] cochain1 (k := K) d e :=
  cochainTensorEquiv K (fun i : Fin N ↦ e i.succ) (fun i : Fin N ↦ d i.castSucc)

/-- `Φ⁰(x ⊗ φ) v r c = x * algebraMap (φ v r c)`. -/
theorem cochain0TensorEquiv_tmul (d e : Fin (N + 1) → ℕ) (x : K) (φ : cochain0 (k := k) d e)
    (v : Fin (N + 1)) (r : Fin (e v)) (c : Fin (d v)) :
    cochain0TensorEquiv K d e (x ⊗ₜ φ) v r c = x * algebraMap k K (φ v r c) :=
  cochainTensorEquiv_tmul K e d x φ v r c

/-- `Φ¹(x ⊗ ψ) i r c = x * algebraMap (ψ i r c)`. -/
theorem cochain1TensorEquiv_tmul (d e : Fin (N + 1) → ℕ) (x : K) (ψ : cochain1 (k := k) d e)
    (i : Fin N) (r : Fin (e i.succ)) (c : Fin (d i.castSucc)) :
    cochain1TensorEquiv K d e (x ⊗ₜ ψ) i r c = x * algebraMap k K (ψ i r c) :=
  cochainTensorEquiv_tmul K (fun i : Fin N ↦ e i.succ) (fun i : Fin N ↦ d i.castSucc) x ψ i r c

/-- Entrywise base change of a tuple: `(mapTuple K M) i = (M i).map (algebraMap k K)`. -/
def mapTuple {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) : Tuple (k := K) d :=
  fun i ↦ (M i).map (algebraMap k K)

@[simp] theorem mapTuple_apply {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (i : Fin N)
    (r : Fin (d i.succ)) (c : Fin (d i.castSucc)) :
    mapTuple K M i r c = algebraMap k K (M i r c) := rfl

/-! ## The intertwining square -/

/-- **The commuting square (L7 core).** Base change intertwines the two deformation differentials:
`deformationδ_K (mapTuple K M) (mapTuple K Nt) ∘ Φ⁰ = Φ¹ ∘ (deformationδ_k M Nt).baseChange K`. -/
theorem deformationδ_baseChange_square {d e : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) (Nt : Tuple (k := k) e) :
    (deformationδ (mapTuple K M) (mapTuple K Nt)) ∘ₗ
        (cochain0TensorEquiv K d e).toLinearMap
      = (cochain1TensorEquiv K d e).toLinearMap
        ∘ₗ (deformationδ M Nt).baseChange K := by
  -- check on pure tensors `x ⊗ₜ φ`, then entrywise
  apply LinearMap.ext
  intro t
  refine t.induction_on ?_ ?_ ?_
  · simp
  · intro x φ
    funext i
    ext r c
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, deformationδ_apply, Matrix.sub_apply, Matrix.mul_apply,
      mapTuple_apply, cochain0TensorEquiv_tmul, cochain1TensorEquiv_tmul, map_sub, map_sum,
      map_mul, Finset.mul_sum, mul_sub]
    ring_nf
  · intro s t hs ht
    rw [map_add, map_add, hs, ht]

/-! ## L7 — `deformationδ` base-change finrank invariance -/

/-- **L7.** The orbit-tangent dimension `finrank (range deformationδ)` is invariant under base change
along a field extension `K/k`: `deformationδ` has a fixed integer 0/±1 block structure, so its range
rank is the same integer over `K` as over `k`. -/
theorem finrank_range_deformationδ_baseChange {d e : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) (Nt : Tuple (k := k) e) :
    finrank K (LinearMap.range (deformationδ (mapTuple K M) (mapTuple K Nt)))
      = finrank k (LinearMap.range (deformationδ M Nt)) := by
  refine finrank_range_eq_of_baseChange_conj K (deformationδ M Nt)
    (deformationδ (mapTuple K M) (mapTuple K Nt))
    (cochain0TensorEquiv K d e).symm (cochain1TensorEquiv K d e).symm ?_
  -- the conjugacy needs `eW ∘ g = f.baseChange ∘ eV` with `eV = Φ⁰⁻¹`, `eW = Φ¹⁻¹`; equivalently
  -- `Φ¹⁻¹ ∘ g = f.baseChange ∘ Φ⁰⁻¹`, the square `g ∘ Φ⁰ = Φ¹ ∘ f.baseChange` conjugated.
  have hsq := deformationδ_baseChange_square K M Nt
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := (cochain0TensorEquiv (k := k) K d e).surjective w
  have hv := LinearMap.congr_fun hsq v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hv ⊢
  rw [LinearEquiv.symm_apply_apply, hv, LinearEquiv.symm_apply_apply]

/-! ## Non-vacuity witness (ℚ → ℝ) -/

/-- A concrete `ℚ`-tuple for `N = 1`, `d = ![1,1]`: the single `1×1` identity edge map. -/
def witnessTupleQ : Tuple (k := ℚ) (N := 1) (fun _ ↦ 1) := fun _ ↦ (1 : Matrix (Fin 1) (Fin 1) ℚ)

/-- L7 fires over the genuine field extension `ℚ → ℝ`: the orbit-tangent rank of the base-changed
tuple over `ℝ` equals the rank over `ℚ` (non-vacuity of `finrank_range_deformationδ_baseChange`). -/
example :
    finrank ℝ (LinearMap.range
        (deformationδ (mapTuple ℝ witnessTupleQ) (mapTuple ℝ witnessTupleQ)))
      = finrank ℚ (LinearMap.range (deformationδ witnessTupleQ witnessTupleQ)) :=
  finrank_range_deformationδ_baseChange (k := ℚ) ℝ witnessTupleQ witnessTupleQ

end DLNFibre.Core

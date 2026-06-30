import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.LinearAlgebra.BaseChange
import DLNFibre.Core.RingTheory.Derivation.Matrix
import DLNFibre.Core.RingTheory.Kaehler.GenericRank
import DLNFibre.Core.OrbitImageDim
import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Deformation
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# `DLNFibre.Core.OrbitDifferentialRank` — A4.3: the generic-Jacobian rank bound `hA43_le`

The char-free differential-rank bound that discharges the last residual of A4.4:

> `genericDifferentialRank k (groupRing d) (genericOrbitCoord M) ≤ finrank k (range (deformationδ M M))`.

As of P2.4 this bound is the **abstract B1** (`AffineGVarietyDeformation.genericRankBound`,
`Core.AlgebraicGeometry.Group.Orbit.Deformation`) at the DLN deformation instance `dlnOrbitDef M`:
the matrix-tuple **discharges the abstract (H1) factorisation** here (`dlnOrbitDef_differentialFactors`)
and supplies the rank-tie `finrank_range_deltaT`; the abstract engine then closes the bound with
`finrank_range_baseChange` + `finrank_mono`. The (H1) shape is the **transpose/adjoint** Maurer–Cartan
factorisation (the de-risked P2.4 GUARD shape: the *forward* `range (L ∘ δ.baseChange)` form is NOT
dischargeable — the orbit-coordinate differentials pair against *single* edge-cochain entries, not
`range δ⁰`; the adjoint carrier `deltaT` + its rank-tie is the model's natural factorisation).

`genericDifferentialRank` is `finrank_K (span_K {D_k(f_x)})`, `K = FractionRing (groupRing d)`,
`Ω = Ω[K⁄k]`, `f_x = (genericOrbitCoord M) x`. The discharge factors the generic Jacobian through the
deformation coboundary `δ⁰ = deformationδ M M` via the **matrix-Kähler identity** (gate
`derivMatrix_inv_apply` in `Core.RingTheory.Derivation.Matrix`) and the **transpose /
trace-pairing**:

1. **Per-coordinate** (`D_genericOrbitCoord_eq`): over `K`, `D(f_x)` is `D` of the `(s,t)` entry of
   `V₂ · F · V₁⁻¹` (`V_v = (genericUnit v).map alg`, `F = (genericFactor M i).map alg = M_i`, constant
   so `D F = 0`).
2. **Span = bracket span** (conjugation by the invertible `K`-matrices `V₂, V₁⁻¹` preserves the
   `K`-span): `span_K {D(f_x)} = span_K {(δ⁰ Θ)_x}`, `Θ_v = V_v⁻¹ · D(V_v)` the Ω-Maurer–Cartan.
3. **Adjoint pairing** (`pair_deltaT_eq_pair_deformationδ`): the entrywise trace transpose `deltaT M`
   of `δ⁰` satisfies `⟨deltaT ψ, G⟩₀ = ⟨ψ, δ⁰ G⟩₁` for any Ω-valued `G` (`Finset.sum_dite_eq'`
   collapses the `Fin.succ`/`castSucc` casts). So the pairing-with-`δ⁰Θ` map `Φ` factors as
   `evΘ ∘ deltaT`, and `range_K(Φ ⊗ K) ≤ evΘ(range_K(deltaT ⊗ K))`.
4. **Transpose rank** (`finrank_range_deltaT`): `finrank (range deltaT) = finrank (range δ⁰)` via the
   trace self-dualities and `LinearMap.finrank_range_dualMap_eq_finrank_range`.
5. **Base-change rank** (`finrank_range_baseChange`, landed) + `Submodule.finrank_mono` close the bound.

Discharging `hA43_le` makes A4.4 unconditional: `…le_finrank_range_deformationδ_unconditional` (the
Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
(chained with A0, char 0 + `Infinite k`) — the AG-half submersion inequality of `hVoigt`, with no
remaining open hypothesis. All axiom-clean (`[propext, Classical.choice, Quot.sound]`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix Module Finset KaehlerDifferential LinearMap

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The entrywise trace transpose of `deformationδ M M` -/

/-- The raw `cochain0` value of the trace transpose at `ψ`. -/
private def deltaTfun {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (ψ : cochain1 (k := k) d d) :
    cochain0 (k := k) d d := fun v p q =>
  (∑ i : Fin N, if h : i.succ = v then
      ∑ t : Fin (d i.castSucc), ψ i (h ▸ p) t * M i (h ▸ q) t else 0)
  - (∑ i : Fin N, if h : i.castSucc = v then
      ∑ s : Fin (d i.succ), M i s (h ▸ p) * ψ i s (h ▸ q) else 0)

/-- The `i.succ`-fibre half of `deltaTfun` is additive in `ψ` (entrywise). -/
private theorem deltaT_succ_add {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (ψ ψ' : cochain1 (k := k) d d) (v : Fin (N + 1)) (p q : Fin (d v)) :
    (∑ i : Fin N, if h : i.succ = v then
        ∑ t : Fin (d i.castSucc), (ψ + ψ') i (h ▸ p) t * M i (h ▸ q) t else 0)
      = (∑ i : Fin N, if h : i.succ = v then
          ∑ t : Fin (d i.castSucc), ψ i (h ▸ p) t * M i (h ▸ q) t else 0)
        + (∑ i : Fin N, if h : i.succ = v then
          ∑ t : Fin (d i.castSucc), ψ' i (h ▸ p) t * M i (h ▸ q) t else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.succ = v
  · simp only [dif_pos h, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by rw [Pi.add_apply, Matrix.add_apply]; ring
  · simp [dif_neg h]

/-- The `i.castSucc`-fibre half of `deltaTfun` is additive in `ψ` (entrywise). -/
private theorem deltaT_cast_add {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (ψ ψ' : cochain1 (k := k) d d) (v : Fin (N + 1)) (p q : Fin (d v)) :
    (∑ i : Fin N, if h : i.castSucc = v then
        ∑ s : Fin (d i.succ), M i s (h ▸ p) * (ψ + ψ') i s (h ▸ q) else 0)
      = (∑ i : Fin N, if h : i.castSucc = v then
          ∑ s : Fin (d i.succ), M i s (h ▸ p) * ψ i s (h ▸ q) else 0)
        + (∑ i : Fin N, if h : i.castSucc = v then
          ∑ s : Fin (d i.succ), M i s (h ▸ p) * ψ' i s (h ▸ q) else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.castSucc = v
  · simp only [dif_pos h, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [Pi.add_apply, Matrix.add_apply]; ring
  · simp [dif_neg h]

/-- The `i.succ`-fibre half of `deltaTfun` is `c`-homogeneous in `ψ` (entrywise). -/
private theorem deltaT_succ_smul {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (c : k)
    (ψ : cochain1 (k := k) d d) (v : Fin (N + 1)) (p q : Fin (d v)) :
    (∑ i : Fin N, if h : i.succ = v then
        ∑ t : Fin (d i.castSucc), (c • ψ) i (h ▸ p) t * M i (h ▸ q) t else 0)
      = c • (∑ i : Fin N, if h : i.succ = v then
          ∑ t : Fin (d i.castSucc), ψ i (h ▸ p) t * M i (h ▸ q) t else 0) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.succ = v
  · simp only [dif_pos h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun t _ => by
      rw [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  · simp [dif_neg h]

/-- The `i.castSucc`-fibre half of `deltaTfun` is `c`-homogeneous in `ψ` (entrywise). -/
private theorem deltaT_cast_smul {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (c : k)
    (ψ : cochain1 (k := k) d d) (v : Fin (N + 1)) (p q : Fin (d v)) :
    (∑ i : Fin N, if h : i.castSucc = v then
        ∑ s : Fin (d i.succ), M i s (h ▸ p) * (c • ψ) i s (h ▸ q) else 0)
      = c • (∑ i : Fin N, if h : i.castSucc = v then
          ∑ s : Fin (d i.succ), M i s (h ▸ p) * ψ i s (h ▸ q) else 0) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.castSucc = v
  · simp only [dif_pos h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun s _ => by
      rw [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · simp [dif_neg h]

/-- The **entrywise trace transpose** `δ⁰ᵀ` of `deformationδ M M`, as a `k`-linear map
`cochain1 → cochain0`: `(δ⁰ᵀ ψ)_v = Σ_{i.succ = v} ψ_i M_iᵀ − Σ_{i.castSucc = v} M_iᵀ ψ_i`
(entrywise, with `Fin.succ`/`castSucc` casts). The adjoint of `δ⁰` for the entrywise trace pairing
(`pair_deltaT_eq_pair_deformationδ`). -/
noncomputable def deltaT {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    cochain1 (k := k) d d →ₗ[k] cochain0 (k := k) d d where
  toFun ψ := deltaTfun M ψ
  map_add' ψ ψ' := by
    funext v p q
    show deltaTfun M (ψ + ψ') v p q = deltaTfun M ψ v p q + deltaTfun M ψ' v p q
    simp only [deltaTfun, deltaT_succ_add M ψ ψ', deltaT_cast_add M ψ ψ']
    abel
  map_smul' c ψ := by
    funext v p q
    rw [RingHom.id_apply]
    show deltaTfun M (c • ψ) v p q = c • deltaTfun M ψ v p q
    simp only [deltaTfun, deltaT_succ_smul M c ψ, deltaT_cast_smul M c ψ, smul_sub]

@[simp] theorem deltaT_apply {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (ψ : cochain1 (k := k) d d) (v : Fin (N + 1)) (p q : Fin (d v)) :
    deltaT M ψ v p q
      = (∑ i : Fin N, if h : i.succ = v then
          ∑ t : Fin (d i.castSucc), ψ i (h ▸ p) t * M i (h ▸ q) t else 0)
        - (∑ i : Fin N, if h : i.castSucc = v then
          ∑ s : Fin (d i.succ), M i s (h ▸ p) * ψ i s (h ▸ q) else 0) := rfl

/-! ## The adjoint pairing: `⟨deltaT ψ, G⟩₀ = ⟨ψ, δ⁰ G⟩₁` (general module coefficients) -/

variable {Ω : Type u} [AddCommGroup Ω] [Module k Ω]

/-- The entrywise trace pairing of an Ω-valued cochain0 family `G` against `δ⁰ G` (the `δ⁰`-bracket of
`G`, written entrywise with the `k`-scalar `•` Ω-action). For `x = ⟨i,s,t⟩` this is
`(G_{i.succ} M_i − M_i G_{i.castSucc})_{st} = Σ_u M_{i,u,t} • G_{i.succ,s,u} − Σ_u M_{i,s,u} • G_{i.castSucc,u,t}`. -/
private def bracketG {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (G : (v : Fin (N + 1)) → Matrix (Fin (d v)) (Fin (d v)) Ω) (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) : Ω :=
  (∑ u : Fin (d i.succ), (M i u t) • G i.succ s u)
    - (∑ u : Fin (d i.castSucc), (M i s u) • G i.castSucc u t)

/-- **The adjoint relation** (the trace transpose `deltaT` is adjoint to `δ⁰ = deformationδ M M`).
For any Ω-valued cochain0 family `G`, pairing `deltaT M ψ` against `G` over cochain0 equals pairing
`ψ` against the `δ⁰`-bracket of `G` over cochain1:
`Σ_v Σ_{pq} (deltaT M ψ)_{vpq} • G_{vpq} = Σ_i Σ_{st} (ψ_i)_{st} • bracketG_{ist}`. The two halves are
symmetric (the `i.succ` / `i.castSucc` fibers); `Finset.sum_dite_eq'` + `Finset.sum_eq_single`
collapse the dependent casts. -/
theorem pair_deltaT_eq_pair_deformationδ {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (ψ : cochain1 (k := k) d d) (G : (v : Fin (N + 1)) → Matrix (Fin (d v)) (Fin (d v)) Ω) :
    (∑ v : Fin (N + 1), ∑ p : Fin (d v), ∑ q : Fin (d v), (deltaT M ψ) v p q • G v p q)
      = ∑ i : Fin N, ∑ s : Fin (d i.succ), ∑ t : Fin (d i.castSucc),
          (ψ i s t) • bracketG M G i s t := by
  classical
  -- split `deltaT = T1 − T2`, distribute over the pairing, then prove each half
  simp only [deltaT_apply, sub_smul, Finset.sum_sub_distrib]
  rw [show (∑ i : Fin N, ∑ s, ∑ t, (ψ i s t) • bracketG M G i s t)
      = (∑ i : Fin N, ∑ s, ∑ t, (ψ i s t) • (∑ u : Fin (d i.succ), (M i u t) • G i.succ s u))
        - (∑ i : Fin N, ∑ s, ∑ t, (ψ i s t) • (∑ u : Fin (d i.castSucc), (M i s u) • G i.castSucc u t))
      from by rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun s _ => ?_
              rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun t _ => ?_
              rw [bracketG, smul_sub]]
  congr 1
  · -- T1 half
    simp_rw [Finset.sum_smul]
    conv_lhs => enter [2, v, 2, p]; rw [Finset.sum_comm]
    conv_lhs => enter [2, v]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i.succ]
    · simp only [dite_true]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
    · intro v _ hv
      apply Finset.sum_eq_zero; intro p _; apply Finset.sum_eq_zero; intro q _
      rw [dif_neg (Ne.symm hv), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- T2 half
    simp_rw [Finset.sum_smul]
    conv_lhs => enter [2, v, 2, p]; rw [Finset.sum_comm]
    conv_lhs => enter [2, v]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i.castSucc]
    · simp only [dite_true]
      simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]
      conv_lhs => rw [Finset.sum_comm]
      conv_lhs => enter [2, t]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
        Finset.sum_congr rfl fun u _ => ?_
      rw [mul_comm]
    · intro v _ hv
      apply Finset.sum_eq_zero; intro p _; apply Finset.sum_eq_zero; intro q _
      rw [dif_neg (Ne.symm hv), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The trace self-duality of the cochain spaces and the transpose-rank identity -/

/-- The entrywise trace pairing on a finite product of matrix spaces `∀ i, Matrix (Fin (a i))
(Fin (b i)) k`, as a `k`-linear map into its dual. Both `cochain0` and `cochain1` are of this form.
Nondegenerate (`traceFun_injective`), so a self-duality `LinearEquiv` (`traceEquiv`). -/
noncomputable def traceFun {ι : Type} [Fintype ι] {a b : ι → ℕ} :
    (∀ i, Matrix (Fin (a i)) (Fin (b i)) k) →ₗ[k]
      Module.Dual k (∀ i, Matrix (Fin (a i)) (Fin (b i)) k) where
  toFun φ := { toFun := fun ψ => ∑ v, ∑ p, ∑ q, φ v p q * ψ v p q
               map_add' := fun x y => by
                 simp only [Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
               map_smul' := fun c x => by
                 simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
                   Finset.mul_sum]
                 exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun p _ =>
                   Finset.sum_congr rfl fun q _ => by ring }
  map_add' x y := by
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply, Matrix.add_apply,
      add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    refine LinearMap.ext fun ψ => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      Pi.smul_apply, Matrix.smul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun q _ => by ring

@[simp] theorem traceFun_apply {ι : Type} [Fintype ι] {a b : ι → ℕ}
    (φ ψ : ∀ i, Matrix (Fin (a i)) (Fin (b i)) k) :
    traceFun φ ψ = ∑ v, ∑ p, ∑ q, φ v p q * ψ v p q := rfl

/-- The trace pairing is nondegenerate: evaluating at the single-entry families `Pi.single v
(Matrix.single p q 1)` isolates each coordinate. -/
theorem traceFun_injective {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ} :
    Function.Injective (traceFun (k := k) (a := a) (b := b)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  funext v p q
  have h0 : traceFun (k := k) (a := a) (b := b) φ
      (Pi.single v (Matrix.single p q 1)) = 0 := by rw [hφ]; rfl
  rw [traceFun_apply, Finset.sum_eq_single v] at h0
  · simp only [Pi.single_eq_same] at h0
    rw [Finset.sum_eq_single p] at h0
    · rw [Finset.sum_eq_single q] at h0
      · rw [Matrix.single_apply_same] at h0
        simpa [Pi.zero_apply, Matrix.zero_apply] using h0
      · intro c _ hc; rw [Matrix.single_apply_of_col_ne p p (Ne.symm hc) 1, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hc; apply Finset.sum_eq_zero; intro q' _
      rw [Matrix.single_apply_of_row_ne (Ne.symm hc) q q' 1, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro v' _ hv'; rw [Pi.single_eq_of_ne hv']; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The trace pairing as a **self-duality** of a finite product of matrix spaces (injective `k`-linear
map between equidimensional finite spaces, via `LinearEquiv.ofBijective`). -/
noncomputable def traceEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ} :
    (∀ i, Matrix (Fin (a i)) (Fin (b i)) k) ≃ₗ[k]
      Module.Dual k (∀ i, Matrix (Fin (a i)) (Fin (b i)) k) :=
  LinearEquiv.ofBijective traceFun
    ⟨traceFun_injective, by
      have : Function.Surjective (traceFun (k := k) (a := a) (b := b)) :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
          (by rw [Subspace.dual_finrank_eq])).mp traceFun_injective
      exact this⟩

theorem traceEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ}
    (φ ψ : ∀ i, Matrix (Fin (a i)) (Fin (b i)) k) :
    traceEquiv φ ψ = ∑ v, ∑ p, ∑ q, φ v p q * ψ v p q := rfl

/-- **The transpose-rank identity.** `finrank (range (deltaT M)) = finrank (range (deformationδ M M))`:
`deltaT M` is the trace-adjoint of `δ⁰ = deformationδ M M` (`pair_deltaT_eq_pair_deformationδ` at
`Ω = k`), i.e. `traceEquiv ∘ deltaT M = δ⁰.dualMap ∘ traceEquiv`, so the two ranks agree by
`finrank_range_dualMap_eq_finrank_range` transported across the trace self-dualities. -/
theorem finrank_range_deltaT {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    finrank k (LinearMap.range (deltaT M)) = finrank k (LinearMap.range (deformationδ M M)) := by
  set eV := (traceEquiv (k := k) (a := d) (b := d) : cochain0 (k := k) d d ≃ₗ[k] _) with heV
  set eW := (traceEquiv (k := k) (a := fun i : Fin N => d i.succ) (b := fun i : Fin N => d i.castSucc) :
      cochain1 (k := k) d d ≃ₗ[k] _) with heW
  -- the dual-form adjoint hypothesis: traceEquiv ∘ deltaT = δ⁰.dualMap ∘ traceEquiv
  have hadj : eV.toLinearMap ∘ₗ deltaT M
      = (deformationδ M M).dualMap ∘ₗ eW.toLinearMap := by
    refine LinearMap.ext fun ψ => LinearMap.ext fun φ => ?_
    rw [heV, heW]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, traceEquiv_apply, LinearMap.dualMap_apply]
    -- goal: `Σ (deltaT ψ) φ = Σ ψ (δ⁰ φ)`; the adjoint relation at `Ω = k`, `G = φ`
    have hpair := pair_deltaT_eq_pair_deformationδ (k := k) M ψ (Ω := k) (fun v => φ v)
    simp only [smul_eq_mul] at hpair
    rw [hpair]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun t _ => ?_
    rw [bracketG, deformationδ_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    have e1 : (∑ u, M i u t • φ i.succ s u) = ∑ j, φ i.succ s j * M i j t :=
      Finset.sum_congr rfl fun u _ => by rw [smul_eq_mul, mul_comm]
    have e2 : (∑ u, M i s u • φ i.castSucc u t) = ∑ j, M i s j * φ i.castSucc j t :=
      Finset.sum_congr rfl fun u _ => by rw [smul_eq_mul]
    rw [e1, e2]
  -- apply the generic adjoint-rank lemma
  have h1 : finrank k (LinearMap.range (eV.toLinearMap ∘ₗ deltaT M))
      = finrank k (LinearMap.range (deltaT M)) := by
    rw [LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective _ eV.injective _).symm.finrank_eq
  have h2 : finrank k (LinearMap.range ((deformationδ M M).dualMap ∘ₗ eW.toLinearMap))
      = finrank k (LinearMap.range (deformationδ M M).dualMap) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr eW.surjective, Submodule.map_top]
  rw [← h1, hadj, h2, LinearMap.finrank_range_dualMap_eq_finrank_range]

/-! ## The generic units over `K = FractionRing (groupRing d)` and the per-coordinate identity -/

variable {d : Fin (N + 1) → ℕ}

/-- `genericUnit v` pushed into `K = FractionRing (groupRing d)`. -/
private noncomputable def genUnitK (M : Tuple (k := k) d) (v : Fin (N + 1)) :
    Matrix (Fin (d v)) (Fin (d v)) (FractionRing (groupRing (k := k) d)) :=
  (genericUnit (k := k) d v).map (algebraMap (groupRing (k := k) d) (FractionRing _))

/-- `genericUnitInv v` pushed into `K`. -/
private noncomputable def genUnitInvK (M : Tuple (k := k) d) (v : Fin (N + 1)) :
    Matrix (Fin (d v)) (Fin (d v)) (FractionRing (groupRing (k := k) d)) :=
  (genericUnitInv (k := k) d v).map (algebraMap (groupRing (k := k) d) (FractionRing _))

/-- `genUnitK v * genUnitInvK v = 1` over `K` (push `genericUnit_mul_genericUnitInv` through `map`). -/
private theorem genUnitK_mul_inv (M : Tuple (k := k) d) (v : Fin (N + 1)) :
    genUnitK M v * genUnitInvK M v = 1 := by
  rw [genUnitK, genUnitInvK, ← Matrix.map_mul, genericUnit_mul_genericUnitInv,
    Matrix.map_one _ (map_zero _) (map_one _)]

/-- `genUnitInvK v * genUnitK v = 1` over `K`. -/
private theorem genUnitInvK_mul (M : Tuple (k := k) d) (v : Fin (N + 1)) :
    genUnitInvK M v * genUnitK M v = 1 := mul_eq_one_comm.mp (genUnitK_mul_inv M v)

/-- `genericFactor M i` pushed into `K` (`= M i` as a constant matrix, killed by `D`). -/
private noncomputable def genFactorK (M : Tuple (k := k) d) (i : Fin N) :
    Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) (FractionRing (groupRing (k := k) d)) :=
  (genericFactor M i).map (algebraMap (groupRing (k := k) d) (FractionRing _))

/-- `D` kills the constant factor `genFactorK` entrywise (`M i` over `k`, via `map_algebraMap`). -/
private theorem D_genFactorK (M : Tuple (k := k) d) (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) :
    KaehlerDifferential.D k (FractionRing (groupRing (k := k) d)) (genFactorK M i s t) = 0 := by
  rw [genFactorK, Matrix.map_apply, genericFactor, Matrix.map_apply,
    ← IsScalarTower.algebraMap_apply k (groupRing (k := k) d) (FractionRing _)]
  exact (KaehlerDifferential.D k (FractionRing (groupRing (k := k) d))).map_algebraMap _

/-- **Per-coordinate identity.** Over `K`, `D(f_x)` is `D` of the `(s,t)` entry of the matrix product
`genUnitK i.succ * genFactorK i * genUnitInvK i.castSucc`. -/
private theorem D_genericOrbitCoord_eq (M : Tuple (k := k) d) (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) :
    KaehlerDifferential.D k (FractionRing (groupRing (k := k) d))
        (algebraMap (groupRing (k := k) d) (FractionRing _) (genericOrbitCoord M ⟨i, s, t⟩))
      = KaehlerDifferential.D k (FractionRing (groupRing (k := k) d))
        ((genUnitK M i.succ * genFactorK M i * genUnitInvK M i.castSucc) s t) := by
  congr 1
  rw [genericOrbitCoord]
  rw [show (algebraMap (groupRing (k := k) d) (FractionRing _))
        ((genericUnit (k := k) d (⟨i, s, t⟩ : RepCoord d).1.succ
          * genericFactor M (⟨i, s, t⟩ : RepCoord d).1
          * genericUnitInv (k := k) d (⟨i, s, t⟩ : RepCoord d).1.castSucc)
        (⟨i, s, t⟩ : RepCoord d).2.1 (⟨i, s, t⟩ : RepCoord d).2.2)
      = ((genericUnit (k := k) d i.succ * genericFactor M i
        * genericUnitInv (k := k) d i.castSucc).map
        (algebraMap (groupRing (k := k) d) (FractionRing _))) s t from (Matrix.map_apply ..).symm]
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

/-! ## The gate expansion of `D(f_x)` and the conjugated Maurer–Cartan bracket -/

/-- Abbreviation: the universal `k`-derivation into `Ω[K⁄k]`, `K = FractionRing (groupRing d)`. -/
local notation "Dk" => KaehlerDifferential.D k (FractionRing (groupRing (k := k) d))

/-- The Ω-valued **Maurer–Cartan** matrix `Θ_v = V_v⁻¹ · D(V_v)` at vertex `v` (entrywise:
`Θ_{v,p,q} = Σ_c (genUnitInvK_v)_{pc} • D((genUnitK_v)_{cq})`). The infinitesimal generator the
generic Jacobian factors through. -/
private noncomputable def mcΘ (M : Tuple (k := k) d) (v : Fin (N + 1)) :
    Matrix (Fin (d v)) (Fin (d v)) (KaehlerDifferential k (FractionRing (groupRing (k := k) d))) :=
  fun p q => ∑ c, (genUnitInvK M v) p c • Dk ((genUnitK M v) c q)

/-- **The gate expansion of `D(f_x)`.** Applying the matrix-Kähler gate (`derivMatrix_mul_apply` once
on the outer product, `derivMatrix_inv_apply` for `D(V₁⁻¹)`, and `D(genFactorK) = 0`):
`D((V₂ F V₁⁻¹)_{st}) = (Σ_w (V₂F)_{sw} • D(V₁⁻¹)_{wt}) + (Σ_w (V₁⁻¹)_{wt} • Σ_a F_{aw} • D(V₂)_{sa})`. -/
private theorem D_orbit_expand (M : Tuple (k := k) d) (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) :
    Dk ((genUnitK M i.succ * genFactorK M i * genUnitInvK M i.castSucc) s t)
      = (∑ w, (genUnitK M i.succ * genFactorK M i) s w •
          (- ∑ c, ∑ e, (genUnitInvK M i.castSucc) w c • (genUnitInvK M i.castSucc) e t •
            Dk ((genUnitK M i.castSucc) c e)))
        + (∑ w, (genUnitInvK M i.castSucc) w t •
          (∑ a, (genFactorK M i) a w • Dk ((genUnitK M i.succ) s a))) := by
  rw [derivMatrix_mul_apply Dk (genUnitK M i.succ * genFactorK M i) (genUnitInvK M i.castSucc) s t,
    Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [derivMatrix_inv_apply Dk (genUnitK_mul_inv M i.castSucc) w t]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [derivMatrix_mul_apply Dk (genUnitK M i.succ) (genFactorK M i) s w]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [D_genFactorK M i a w, smul_zero, zero_add]

/-- **Left-collapse.** `Σ_a (V_v)_{sa} • Θ_{v,a,u} = D((V_v)_{su})`: left-multiplying the Maurer–Cartan
`Θ_v = V_v⁻¹ DV_v` by `V_v` recovers `D V_v` (uses `genUnitK_mul_inv`, `V_v V_v⁻¹ = 1`). -/
private theorem genUnitK_smul_mcΘ (M : Tuple (k := k) d) (v : Fin (N + 1)) (s u : Fin (d v)) :
    (∑ a, (genUnitK M v) s a • mcΘ M v a u) = Dk ((genUnitK M v) s u) := by
  simp only [mcΘ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  rw [show (∑ c, ∑ a, ((genUnitK M v) s a * (genUnitInvK M v) a c) • Dk ((genUnitK M v) c u))
      = ∑ c, ((genUnitK M v * genUnitInvK M v) s c) • Dk ((genUnitK M v) c u) from
    Finset.sum_congr rfl fun c _ => by rw [← Finset.sum_smul, Matrix.mul_apply]]
  rw [genUnitK_mul_inv, Finset.sum_eq_single s]
  · rw [Matrix.one_apply_eq, one_smul]
  · exact fun b _ hb => by rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **Right-collapse.** `Σ_b Θ_{v,p,b} • (V_v)_{bq}`-style: `Σ_e (V_v⁻¹)_{be} D(V_v)_{e?}`… the right
analogue used for the `M Θ_cast` term. Specifically `Σ_b (V_v⁻¹)_{wb} • (Σ_a (V_v)_{ba} • x a) = x w`
is the matrix-inverse collapse, here packaged as: left-multiplying `Σ_a (V_v)_{ba} • x a` by `V_v⁻¹`
and summing recovers `x`. -/
private theorem genUnitInvK_smul_genUnitK_smul (M : Tuple (k := k) d) (v : Fin (N + 1))
    (w : Fin (d v)) (x : Fin (d v) → KaehlerDifferential k (FractionRing (groupRing (k := k) d))) :
    (∑ b, (genUnitInvK M v) w b • (∑ a, (genUnitK M v) b a • x a)) = x w := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  rw [show (∑ a, ∑ b, ((genUnitInvK M v) w b * (genUnitK M v) b a) • x a)
      = ∑ a, ((genUnitInvK M v * genUnitK M v) w a) • x a from
    Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_smul, Matrix.mul_apply]]
  rw [genUnitInvK_mul, Finset.sum_eq_single w]
  · rw [Matrix.one_apply_eq, one_smul]
  · exact fun b _ hb => by rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- `genFactorK M i a w = algebraMap k K (M i a w)` (the constant `M`-entry over `K`). -/
private theorem genFactorK_apply (M : Tuple (k := k) d) (i : Fin N)
    (a : Fin (d i.succ)) (w : Fin (d i.castSucc)) :
    (genFactorK M i) a w = algebraMap k (FractionRing (groupRing (k := k) d)) (M i a w) := by
  rw [genFactorK, Matrix.map_apply, genericFactor, Matrix.map_apply,
    ← IsScalarTower.algebraMap_apply k (groupRing (k := k) d) (FractionRing _)]

/-! ## The conjugation identity `D_orbit_conj` and the final bound `hA43_le` -/

set_option maxHeartbeats 1000000 in
/-- **TermA of the conjugation identity (the inverse / `D(V₁⁻¹)`-side bracket half).** The gate's
`D(V₁⁻¹) = −V₁⁻¹ (DV₁) V₁⁻¹` group equals `−` the `M Θ_cast` half of the conjugated Maurer–Cartan
bracket. Both sides normalise to `− Σ_w Σ_c Σ_e (V₂F)_{sw} • (V₁⁻¹_{wc} • (V₁⁻¹_{et} • D(V₁_{ce})))`;
the RHS flattens `mcΘ M i.castSucc`, folds the `M_{au}` k-scalar into `genFactorK` (`algebraMap_smul`),
and `Σ_a V₂_{sa} genFactorK_{au} = (V₂ * genFactorK)_{su}` (`Matrix.mul_apply`). Unlike the direct
side, there is **no inverse-collapse** — `Σ_u M_{au} V₁⁻¹_{uc}` is irreducible (`M` is not invertible) —
so this is a two-sided normal-form match, not a collapse. -/
private theorem D_orbit_conj_termA (M : Tuple (k := k) d) (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) :
    (∑ w, (genUnitK M i.succ * genFactorK M i) s w •
        (- ∑ c, ∑ e, (genUnitInvK M i.castSucc) w c • (genUnitInvK M i.castSucc) e t •
          Dk ((genUnitK M i.castSucc) c e)))
      = - ∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          (∑ u, (M i a u) • mcΘ M i.castSucc u b) := by
  classical
  set V₂ := genUnitK M i.succ with hV₂
  set W₁ := genUnitInvK M i.castSucc with hW₁
  set V₁ := genUnitK M i.castSucc with hV₁
  set F := genFactorK M i with hF
  simp only [smul_neg, Finset.smul_sum]
  rw [Finset.sum_neg_distrib]
  refine congrArg Neg.neg ?_
  rw [show (∑ a, ∑ b, ∑ u, (V₂ s a * W₁ b t) • (M i a u) • mcΘ M i.castSucc u b)
      = ∑ b, ∑ u, ∑ c, (∑ a, V₂ s a * F a u) • (W₁ b t • (W₁ u c • Dk (V₁ c b))) from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (∑ a, ∑ u, (V₂ s a * W₁ b t) • (M i a u) • mcΘ M i.castSucc u b)
        = ∑ a, ∑ u, ∑ c, (V₂ s a * F a u) • (W₁ b t • (W₁ u c • Dk (V₁ c b))) from by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [mcΘ, ← hW₁, ← hV₁, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hF, genFactorK_apply, ← algebraMap_smul (FractionRing (groupRing (k := k) d)) (M i a u)]
      rw [smul_smul]
      conv_lhs => rw [mul_assoc, mul_comm (W₁ b t), ← mul_assoc]
      conv_rhs => rw [smul_smul]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul]]
  rw [show (∑ b, ∑ u, ∑ c, (∑ a, V₂ s a * F a u) • (W₁ b t • (W₁ u c • Dk (V₁ c b))))
      = ∑ w, ∑ c, ∑ e, (V₂ * F) s w • (W₁ w c • (W₁ e t • Dk (V₁ c e))) from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.mul_apply, smul_comm (W₁ e t) (W₁ w c)]]

set_option maxHeartbeats 1000000 in
/-- **The conjugation identity (step 2).** `D(f_x)` is the `(s,t)` entry of the conjugated
Maurer–Cartan bracket: `D(f_x) = Σ_a Σ_b (V₂)_{sa} (V₁⁻¹)_{bt} • bracketG (mcΘ M) i a b`, where
`bracketG (mcΘ M)` is the `δ⁰`-bracket of the Maurer–Cartan. From the gate expansion `D_orbit_expand`
(split via `hsplit`), the direct-side half `hB` (the `D(V₂)` group, via the left-collapse
`genUnitK_smul_mcΘ`), and the inverse-side half `D_orbit_conj_termA`. -/
private theorem D_orbit_conj (M : Tuple (k := k) d) (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) :
    Dk ((genUnitK M i.succ * genFactorK M i * genUnitInvK M i.castSucc) s t)
      = ∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          bracketG M (mcΘ M) i a b := by
  rw [D_orbit_expand M i s t]
  -- `bracketG (mcΘ) = (Σ_u M_ub • Θ_succ) − (Σ_u M_au • Θ_cast)`; conjugate and split
  have hsplit : (∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
        bracketG M (mcΘ M) i a b)
      = (∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          (∑ u, (M i u b) • mcΘ M i.succ a u))
        - (∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          (∑ u, (M i a u) • mcΘ M i.castSucc u b)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [bracketG, smul_sub]
  -- TermB (the `D(V₂)` group) = the `Σ_u M_ub • Θ_succ` half
  have hB : (∑ w, (genUnitInvK M i.castSucc) w t •
        (∑ a, (genFactorK M i) a w • Dk ((genUnitK M i.succ) s a)))
      = ∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          (∑ u, (M i u b) • mcΘ M i.succ a u) := by
    rw [show (∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          (∑ u, (M i u b) • mcΘ M i.succ a u))
        = ∑ b, ∑ u, (genUnitInvK M i.castSucc) b t • (M i u b) •
            (∑ a, (genUnitK M i.succ) s a • mcΘ M i.succ a u) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [show (∑ a, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
            (∑ u, (M i u b) • mcΘ M i.succ a u))
          = ∑ a, ∑ u, (M i u b) • ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
              mcΘ M i.succ a u from
        Finset.sum_congr rfl fun a _ => by
          rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun u _ => by rw [smul_comm]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_comm ((genUnitInvK M i.castSucc) b t) (M i u b), smul_smul, mul_comm]]
    simp only [genUnitK_smul_mcΘ]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [genFactorK_apply, ← algebraMap_smul (FractionRing (groupRing (k := k) d)) (M i u w),
      smul_comm]
  rw [hsplit, sub_eq_add_neg, ← hB, ← D_orbit_conj_termA M i s t, add_comm]

/-- The Maurer–Cartan **pairing transport** `pairMC : cochain0 →ₗ[k] Ω`, `φ ↦ Σ_{vpq} φ_{vpq} •
Θ_{vpq}` (pair a `C⁰`-scalar family against the Ω-valued Maurer–Cartan `mcΘ M`). The transport `L`
the matrix-tuple instance supplies for the abstract (H1) factorisation, via its base-change lift
`pairMC.liftBaseChange K : K ⊗ cochain0 → Ω`. -/
private noncomputable def pairMC {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    cochain0 (k := k) d d →ₗ[k] KaehlerDifferential k (FractionRing (groupRing (k := k) d)) where
  toFun φ := ∑ v, ∑ p, ∑ q, φ v p q • mcΘ M v p q
  map_add' φ φ' := by
    simp only [Pi.add_apply, Matrix.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
  map_smul' c φ := by
    simp only [Pi.smul_apply, Matrix.smul_apply, smul_assoc, RingHom.id_apply, Finset.smul_sum]

/-- **The DLN matrix-tuple deformation instance.** The abstract affine-`G`-variety carrier
(`dlnOrbit M`) extended with the deformation data `(cochain0 d d, cochain1 d d, deformationδ M M)`.
The first instance of the abstract deformation/rank engine
(`Core.AlgebraicGeometry.Group.Orbit.Deformation`). Its `R`, `fρ`, `δ` are the DLN ones by `rfl`. -/
noncomputable def dlnOrbitDef {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    AlgebraicGeometry.Group.Orbit.AffineGVarietyDeformation k where
  toAffineGVariety := dlnOrbit M
  C0 := cochain0 (k := k) d d
  C1 := cochain1 (k := k) d d
  δ := deformationδ M M

set_option maxHeartbeats 800000 in
/-- **The DLN discharge of (H1).** The matrix-tuple instance satisfies the abstract (transpose)
Maurer–Cartan factorisation `DifferentialFactors (dlnOrbitDef M) (deltaT M) (pairMC.lift K)`:
the span of the orbit-coordinate differentials sits in `range ((pairMC M).liftBaseChange K ∘
(deltaT M).baseChange K)`. Each generator `D(f_x)` is the `(s,t)` entry of the conjugated
Maurer–Cartan bracket (`D_genericOrbitCoord_eq` + `D_orbit_conj`), a `K`-combination of the
single-entry brackets
`bracketG (mcΘ M)`, each of which is `(pairMC ∘ deltaT)(single)` by the adjoint relation
`pair_deltaT_eq_pair_deformationδ`. Discharges the abstract B1's (H1) input for the DLN model. -/
theorem dlnOrbitDef_differentialFactors {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    (dlnOrbitDef M).DifferentialFactors (deltaT M)
      ((pairMC M).liftBaseChange (FractionRing (groupRing (k := k) d))) := by
  classical
  set K := FractionRing (groupRing (k := k) d)
  -- each Maurer–Cartan bracket is hit by `pairMC ∘ deltaT` at the single-entry cochain1 (adjoint)
  have hbr : ∀ (i : Fin N) (a' : Fin (d i.succ)) (b' : Fin (d i.castSucc)),
      bracketG M (mcΘ M) i a' b' ∈ LinearMap.range ((pairMC M).comp (deltaT M)) := by
    intro i a' b'
    refine ⟨Pi.single i (Matrix.single a' b' (1 : k)), ?_⟩
    rw [LinearMap.comp_apply]
    show (∑ v, ∑ p, ∑ q,
        (deltaT M (Pi.single i (Matrix.single a' b' (1 : k)))) v p q • mcΘ M v p q)
      = bracketG M (mcΘ M) i a' b'
    rw [pair_deltaT_eq_pair_deformationδ M (Pi.single i (Matrix.single a' b' (1 : k))) (mcΘ M)]
    -- collapse the triple sum: the single-entry indicator picks out `(i, a', b')`
    rw [Finset.sum_eq_single i (fun i₁ _ hi₁ => ?_) (fun h => absurd (Finset.mem_univ _) h)]
    · rw [Pi.single_eq_same]
      rw [Finset.sum_eq_single a' (fun s _ hs => ?_) (fun h => absurd (Finset.mem_univ _) h)]
      · rw [Finset.sum_eq_single b' (fun t _ ht => ?_) (fun h => absurd (Finset.mem_univ _) h)]
        · rw [Matrix.single_apply_same, one_smul]
        · rw [Matrix.single_apply_of_col_ne a' a' (Ne.symm ht) 1, zero_smul]
      · refine Finset.sum_eq_zero fun t _ => ?_
        rw [Matrix.single_apply_of_row_ne (Ne.symm hs) b' t 1, zero_smul]
    · refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
      rw [Pi.single_eq_of_ne hi₁, Matrix.zero_apply, zero_smul]
  -- the composed transport `(pairMC.liftBaseChange) ∘ (deltaT.baseChange) = (pairMC ∘ deltaT).lift`
  have hcomp : ((pairMC M).liftBaseChange K).comp ((deltaT M).baseChange K)
      = ((pairMC M).comp (deltaT M)).liftBaseChange K := by
    ext x; simp [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]
  -- reduce the abstract `DifferentialFactors` at the DLN instance to the `groupRing d` span form
  change Submodule.span K
      (Set.range fun x : RepCoord d => KaehlerDifferential.D k K
        (algebraMap (groupRing (k := k) d) K (genericOrbitCoord M x)))
    ≤ LinearMap.range (((pairMC M).liftBaseChange K).comp ((deltaT M).baseChange K))
  rw [hcomp, LinearMap.range_liftBaseChange, Submodule.span_le]
  -- every generator `D(f_x)` lies in `span_K (range (pairMC ∘ deltaT))`
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, a, b⟩ := x
  change KaehlerDifferential.D k K
      (algebraMap (groupRing (k := k) d) K (genericOrbitCoord M ⟨i, a, b⟩))
    ∈ Submodule.span K ↑(LinearMap.range ((pairMC M).comp (deltaT M)))
  rw [D_genericOrbitCoord_eq M i a b, D_orbit_conj M i a b]
  refine Submodule.sum_mem _ fun a' _ => Submodule.sum_mem _ fun b' _ => ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hbr i a' b'))

/-- **A4.3 (`hA43_le`): the generic-Jacobian rank bound.** `genericDifferentialRank ≤ finrank (range
δ⁰)`, char-free. Now a transport of the **abstract B1**
(`AffineGVarietyDeformation.genericRankBound`) at the DLN deformation instance `dlnOrbitDef M`: the
matrix-tuple discharges the (H1) factorisation (`dlnOrbitDef_differentialFactors`, via
`D_orbit_conj` + `pair_deltaT_eq_pair_deformationδ`) with adjoint `deltaT M`, transport
`pairMC.liftBaseChange K`, and the rank-tie `finrank_range_deltaT` (trace self-duality
`finrank (range deltaT) = finrank (range δ⁰)`). The abstract engine supplies the
`finrank_range_baseChange` + `finrank_mono` route; the matrix self-duality stays the model's
detail. -/
theorem genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ
    {d : Fin (N + 1) → ℕ} [Fintype (RepCoord d)] (M : Tuple (k := k) d) :
    genericDifferentialRank k (groupRing (k := k) d) (genericOrbitCoord M)
      ≤ finrank k (LinearMap.range (deformationδ M M)) := by
  haveI : Fintype (dlnOrbitDef M).ρ := inferInstanceAs (Fintype (RepCoord d))
  exact AlgebraicGeometry.Group.Orbit.AffineGVarietyDeformation.genericRankBound (dlnOrbitDef M)
    (deltaT M) ((pairMC M).liftBaseChange (FractionRing (groupRing (k := k) d)))
    (dlnOrbitDef_differentialFactors M) (finrank_range_deltaT M)

/-! ## A4.4 and the AG-half submersion bound, now UNCONDITIONAL (char 0)

`hA43_le` is discharged (`genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ`),
so the route-c submersion bound and its A0-chained variety-dimension form carry no remaining
hypothesis beyond `[CharZero k]` (for the A4.2 criterion `diffIndepCriterion_groupRing`). -/

/-- **A4.4, unconditional (char 0).** `(ringKrullDim (orbitPullback M).range).unbotD 0 ≤
finrank k (range δ⁰)` with NO open hypothesis: the A4.2 criterion is `diffIndepCriterion_groupRing`
and the A4.3 bound `hA43_le` is now the proved
`genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ`. -/
theorem ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_unconditional
    [CharZero k] {d : Fin (N + 1) → ℕ} [Fintype (RepCoord d)] (M : Tuple (k := k) d) :
    (ringKrullDim (orbitPullback M).range).unbotD 0
      ≤ finrank k (LinearMap.range (deformationδ M M)) :=
  ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_charZero M
    (genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ M)

/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
(`[Infinite k]`): the variety dimension of the determinantal rank locus `Z_M = canonicalCoord d ''
orbitRankLocus M` is at most the dimension of the orbit tangent image `range (deformationδ M M) = δ⁰`.
No open hypothesis (`hA43_le` discharged). The AG-half submersion inequality of `hVoigt`. -/
theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
    [CharZero k] [Infinite k] {d : Fin (N + 1) → ℕ} [Fintype (RepCoord d)] (M : Tuple (k := k) d) :
    varietyDim (canonicalCoord d '' orbitRankLocus M)
      ≤ finrank k (LinearMap.range (deformationδ M M)) :=
  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
    (trdeg_range_orbitPullback_le_genericDifferentialRank M diffIndepCriterion_groupRing)
    (genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ M)

end DLNFibre.Core

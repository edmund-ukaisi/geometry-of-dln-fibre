import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.MatrixKaehler
import DLNFibre.Core.JacobianTrdeg
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# `DLNFibre.Core.OrbitDifferentialRank` — A4.3: the generic-Jacobian rank bound `hA43_le`

The char-free differential-rank bound that discharges the last residual of A4.4:

> `genericDifferentialRank k (groupRing d) (genericOrbitCoord M) ≤ finrank k (range (deformationδ M M))`.

`genericDifferentialRank` is `finrank_K (span_K {D_k(f_x)})`, `K = FractionRing (groupRing d)`,
`Ω = Ω[K⁄k]`, `f_x = (genericOrbitCoord M) x`. The proof factors the generic Jacobian through the
deformation coboundary `δ⁰ = deformationδ M M` via the **matrix-Kähler identity** (gate
`derivMatrix_inv_apply` in `Core.MatrixKaehler`) and the **transpose / trace-pairing**:

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

end DLNFibre.Core

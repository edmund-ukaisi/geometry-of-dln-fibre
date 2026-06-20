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

/-! ## Remaining (not yet committed): the conjugation identity + final `hA43_le`

The conjugation identity `D(f_x) = Σ_a Σ_b (V₂)_{sa} (V₁⁻¹)_{bt} • bracketG (mcΘ M) i a b`
(`D_orbit_conj`) and the final bound `genericDifferentialRank ≤ finrank (range δ⁰)` are proved on
paper and validated in Lean piece-by-piece, but `D_orbit_conj` rests on one inverse-side reindex
lemma (`D_orbit_conj_termA`, the `D(V₁⁻¹)`-bracket half) whose assembled `Finset`-sum proof did not
elaborate cleanly (parse/heartbeat/index-type friction; see thread-37 card for the precise
obstruction). To respect the project sorry-gate, those two declarations are kept out of the committed
file until `D_orbit_conj_termA` closes. The landed pieces above (`deltaT`, the adjoint pairing
`pair_deltaT_eq_pair_deformationδ`, the trace self-duality `traceEquiv`, the transpose-rank identity
`finrank_range_deltaT`, the gate expansion `D_orbit_expand`, the Maurer–Cartan collapses, and the
per-coordinate `D_genericOrbitCoord_eq`) are the full 0-sorry scaffold; the direct-side half `hB`
of `D_orbit_conj` is also proved (it is the mirror of `D_orbit_conj_termA`). -/

end DLNFibre.Core

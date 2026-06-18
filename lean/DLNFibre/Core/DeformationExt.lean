import DLNFibre.Core.IntervalModule
import Mathlib.Data.Matrix.Bilinear
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# `DLNFibre.Core.DeformationExt` — the 2-term deformation complex and its `Ext¹`

For two representations of the equioriented `A_N` quiver (arrows `t → t+1`) given as tuples
`M : Tuple d` and `N : Tuple e` (the edge matrices are `M_i = M i`, `N_i = N i`), the **deformation
complex** (Ringel/Voigt) over a field `k`:

* `C⁰(M,N) = ∏_{v : Fin (N+1)} Matrix (Fin (e v)) (Fin (d v)) k` — a vertex map at each vertex;
* `C¹(M,N) = ∏_{i : Fin N} Matrix (Fin (e i.succ)) (Fin (d i.castSucc)) k` — an edge map at each
  arrow;
* `δ : C⁰ → C¹`, `δ(φ)_i = φ(i.succ) * M_i − N_i * φ(i.castSucc)` (a `k`-linear map).

`Hom M N := LinearMap.ker δ` is the space of quiver morphisms `M → N`; `deformationExt1 M N` is the
cokernel `C¹ ⧸ LinearMap.range δ`.

**Name = content.** This is the **deformation-complex** `Ext¹`. For the hereditary path algebra
`kQ` of the equioriented `A_N` quiver (no relations, `gl.dim ≤ 1`) it **equals** the derived
`Ext¹_{kQ}(M,N)`, because every ambient `1`-cochain is a cocycle (`Z¹ = C¹`) and the complex
`C⁰ → C¹` computes `Ext` (Assem–Simson–Skowroński; Crawley-Boevey, quiver notes). That
categorical/derived-`Ext` bridge is **DEFERRED** — it is not built here. Hence the def is named
`deformationExt1`, not `Ext1`; the equality with derived `Ext` is **Cited**, not Proved.

Nothing here is the *geometric* codimension: `finrank deformationExt1 M M = codim O_M` is Voigt's
theorem (Phase B) and needs the orbit-dimension bridge. No declaration here is named `codim…`.

**Typeclass.** `Field k` throughout (the deformation complex computes `Ext` over a field; finrank
additivity needs free finite modules). `Nontrivial k` is automatic from `Field`.
-/

namespace DLNFibre.Core

open Matrix Module

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The two cochain spaces and the differential -/

/-- `C⁰(M,N)`: a vertex map `Matrix (Fin (e v)) (Fin (d v)) k` at each vertex `v`. -/
abbrev cochain0 (d e : Fin (N + 1) → ℕ) : Type u :=
  ∀ v : Fin (N + 1), Matrix (Fin (e v)) (Fin (d v)) k

/-- `C¹(M,N)`: an edge map `Matrix (Fin (e i.succ)) (Fin (d i.castSucc)) k` at each arrow `i`. -/
abbrev cochain1 (d e : Fin (N + 1) → ℕ) : Type u :=
  ∀ i : Fin N, Matrix (Fin (e i.succ)) (Fin (d i.castSucc)) k

/-- The differential `δ : C⁰ → C¹`, `δ(φ)_i = φ(i.succ) * M_i − N_i * φ(i.castSucc)`, as a
`k`-linear map (a difference of left/right matrix-multiply maps in `φ`). -/
def deformationδ {d e : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (Nt : Tuple (k := k) e) :
    cochain0 (k := k) d e →ₗ[k] cochain1 (k := k) d e where
  toFun φ := fun i ↦ φ i.succ * M i - Nt i * φ i.castSucc
  map_add' φ ψ := by
    funext i
    simp only [Pi.add_apply, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c φ := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, Matrix.smul_mul, Matrix.mul_smul]

@[simp] theorem deformationδ_apply {d e : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (Nt : Tuple (k := k) e) (φ : cochain0 (k := k) d e) (i : Fin N) :
    deformationδ M Nt φ i = φ i.succ * M i - Nt i * φ i.castSucc := rfl

/-- `Hom M N`: quiver morphisms `M → N`, the kernel of the deformation differential `δ`. A family
`(φ_v)_v` is a morphism exactly when `φ(i+1) * M_i = N_i * φ(i)` at every arrow. -/
def Hom {d e : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (Nt : Tuple (k := k) e) :
    Submodule k (cochain0 (k := k) d e) :=
  LinearMap.ker (deformationδ M Nt)

/-- `deformationExt1 M N`: the **deformation-complex** `Ext¹`, the cokernel `C¹ ⧸ range δ`. Equals
the derived `Ext¹_{kQ}(M,N)` for the hereditary equioriented-`A_N` path algebra (Cited; see the
module docstring), a bridge not built here. -/
def deformationExt1 {d e : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (Nt : Tuple (k := k) e) :
    Type u :=
  (cochain1 (k := k) d e) ⧸ LinearMap.range (deformationδ M Nt)

noncomputable instance {d e : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (Nt : Tuple (k := k) e) :
    AddCommGroup (deformationExt1 M Nt) :=
  inferInstanceAs (AddCommGroup ((cochain1 (k := k) d e) ⧸ _))

noncomputable instance {d e : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (Nt : Tuple (k := k) e) :
    Module k (deformationExt1 M Nt) :=
  inferInstanceAs (Module k ((cochain1 (k := k) d e) ⧸ _))

/-- `φ ∈ Hom M N` exactly when the morphism square commutes at every arrow:
`φ(i+1) * M_i = N_i * φ(i)`. -/
theorem mem_Hom_iff {d e : Fin (N + 1) → ℕ} {M : Tuple (k := k) d} {Nt : Tuple (k := k) e}
    {φ : cochain0 (k := k) d e} :
    φ ∈ Hom M Nt ↔ ∀ i : Fin N, φ i.succ * M i = Nt i * φ i.castSucc := by
  rw [Hom, LinearMap.mem_ker]
  constructor
  · intro h i
    have := congrFun h i
    simp only [deformationδ_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  · intro h
    funext i
    simp only [deformationδ_apply, Pi.zero_apply, sub_eq_zero, h i]

/-! ## Finite-dimensionality and the Euler identity -/

/-- `finrank C⁰(M,N) = Σ_v e_v d_v`. -/
theorem finrank_cochain0 (d e : Fin (N + 1) → ℕ) :
    finrank k (cochain0 (k := k) d e) = ∑ v : Fin (N + 1), e v * d v := by
  rw [Module.finrank_pi_fintype]
  congr 1; funext v
  rw [finrank_matrix, Fintype.card_fin, Fintype.card_fin, finrank_self, mul_one]

/-- `finrank C¹(M,N) = Σ_i e_{i+1} d_i`. -/
theorem finrank_cochain1 (d e : Fin (N + 1) → ℕ) :
    finrank k (cochain1 (k := k) d e) = ∑ i : Fin N, e i.succ * d i.castSucc := by
  rw [Module.finrank_pi_fintype]
  congr 1; funext i
  rw [finrank_matrix, Fintype.card_fin, Fintype.card_fin, finrank_self, mul_one]

/-- **Euler identity (Ringel form).** `finrank Hom − finrank deformationExt1 = finrank C⁰ − finrank
C¹ = Σ_v e_v d_v − Σ_i e_{i+1} d_i = ⟨d,e⟩`. Pure rank-nullity: `finrank ker δ + finrank range δ =
finrank C⁰` and `finrank coker δ = finrank C¹ − finrank range δ`. -/
theorem euler_identity {d e : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) (Nt : Tuple (k := k) e) :
    (finrank k (Hom M Nt) : ℤ) - finrank k (deformationExt1 M Nt)
      = (finrank k (cochain0 (k := k) d e) : ℤ) - finrank k (cochain1 (k := k) d e) := by
  have hrn : finrank k (LinearMap.range (deformationδ M Nt))
      + finrank k (Hom M Nt) = finrank k (cochain0 (k := k) d e) :=
    (deformationδ M Nt).finrank_range_add_finrank_ker
  have hcoker : finrank k (deformationExt1 M Nt)
      + finrank k (LinearMap.range (deformationδ M Nt)) = finrank k (cochain1 (k := k) d e) :=
    Submodule.finrank_quotient_add_finrank _
  zify at hrn hcoker
  omega

/-! ## The Euler form between interval modules

`⟨e_{ij}, e_{uv}⟩ = finrank C⁰ − finrank C¹` for the interval-module dimension vectors. The two
cochain dimensions are sums of products of `{0,1}` indicators (`intervalDim`), counted as interval
lengths; their difference collapses to `1[u≤i≤v≤j] − 1[i<u≤j+1≤v]` (the latter false at `j = N`).
This is the keystone for the Ext indicator (`euler_identity` + the Hom indicator). -/

open Finset in
/-- `intervalDim` written as a `Nat.val` indicator: `1` on `[i,j]` (value comparison), else `0`. -/
theorem intervalDim_eq_ite (i j w : Fin (N + 1)) :
    intervalDim i j w = if (i : ℕ) ≤ (w : ℕ) ∧ (w : ℕ) ≤ (j : ℕ) then 1 else 0 := by
  unfold intervalDim; simp only [Fin.le_iff_val_le_val]

/-- The `C⁰` summand `e_w · d_w` of two interval modules collapses to the overlap indicator
`[u≤w ∧ w≤v ∧ i≤w ∧ w≤j]` (the product of the two containment indicators). -/
theorem c0_term_eq_ite (i j u v w : Fin (N + 1)) :
    intervalDim u v w * intervalDim i j w
      = (if (u : ℕ) ≤ (w : ℕ) ∧ (w : ℕ) ≤ v ∧ (i : ℕ) ≤ w ∧ (w : ℕ) ≤ j then 1 else 0) := by
  rw [intervalDim_eq_ite, intervalDim_eq_ite]
  split <;> split <;> simp_all

/-- The `C¹` summand `e_{t+1} · d_t` of two interval modules collapses to the shifted overlap
indicator `[u≤t+1 ∧ t+1≤v ∧ i≤t ∧ t≤j]`. -/
theorem c1_term_eq_ite (i j u v : Fin (N + 1)) (t : Fin N) :
    intervalDim u v t.succ * intervalDim i j t.castSucc
      = (if (u : ℕ) ≤ (t : ℕ) + 1 ∧ (t : ℕ) + 1 ≤ v ∧ (i : ℕ) ≤ t ∧ (t : ℕ) ≤ j then 1 else 0) := by
  rw [intervalDim_eq_ite, intervalDim_eq_ite, Fin.val_succ, Fin.val_castSucc]
  split <;> split <;> simp_all

open Finset in
/-- **Counting helper.** Over `Fin M`, the number of `t` with `a ≤ t ≤ b` (value comparison) is the
clamped interval length `(min b (M−1) + 1) − a` (or `M = 0`). Built by an explicit value bijection
to `Finset.Icc a (min b (M−1))`. Reused for both cochain sums (`M = N+1` and `M = N`). -/
theorem count_fin_iff {M : ℕ} (p : Fin M → Prop) [DecidablePred p] (a b : ℕ)
    (hp : ∀ t : Fin M, p t ↔ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)) :
    (Finset.univ.filter p).card = (min b (M - 1) + 1) - a ∨ M = 0 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · right; exact hM
  · left
    rw [← Nat.card_Icc a (min b (M - 1))]
    apply Finset.card_bij (fun (t : Fin M) _ ↦ (t : ℕ))
    · intro t ht; simp only [mem_filter, mem_univ, true_and] at ht
      rw [hp] at ht; rw [Finset.mem_Icc]; exact ⟨ht.1, le_min ht.2 (by omega)⟩
    · intro t1 _ t2 _ h; exact Fin.val_injective h
    · intro n hn; rw [Finset.mem_Icc] at hn
      refine ⟨⟨n, by omega⟩, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]; rw [hp]; simp only; omega

open Finset in
/-- `finrank C⁰(M_{ij}, M_{uv}) = Σ_w e_w d_w` as the overlap length
`(min (min v j) N + 1) − max u i`. -/
theorem c0_sum_eq (i j u v : Fin (N + 1)) :
    (∑ w : Fin (N + 1), intervalDim u v w * intervalDim i j w)
      = (min (min (v : ℕ) j) N + 1) - max (u : ℕ) i := by
  rw [Finset.sum_congr rfl (fun w _ ↦ c0_term_eq_ite i j u v w), Finset.sum_boole]
  rcases count_fin_iff (M := N + 1)
      (fun w ↦ (u : ℕ) ≤ w ∧ (w : ℕ) ≤ v ∧ (i : ℕ) ≤ w ∧ (w : ℕ) ≤ j)
      (max (u : ℕ) i) (min (v : ℕ) j) (by intro w; simp only; omega) with h | h
  · rw [h]; norm_num
  · omega

open Finset in
/-- `finrank C¹(M_{ij}, M_{uv}) = Σ_t e_{t+1} d_t` as the shifted overlap length (zero when `v = 0`,
since no edge can map into an empty target bar). -/
theorem c1_sum_eq (i j u v : Fin (N + 1)) :
    (∑ t : Fin N, intervalDim u v t.succ * intervalDim i j t.castSucc)
      = (if 1 ≤ (v : ℕ) then (min (min ((v : ℕ) - 1) j) (N - 1) + 1) - max ((u : ℕ) - 1) i
          else 0) := by
  rw [Finset.sum_congr rfl (fun t _ ↦ c1_term_eq_ite i j u v t), Finset.sum_boole]
  by_cases hv : 1 ≤ (v : ℕ)
  · rw [if_pos hv]
    rcases count_fin_iff (M := N)
        (fun t ↦ (u : ℕ) ≤ (t : ℕ) + 1 ∧ (t : ℕ) + 1 ≤ v ∧ (i : ℕ) ≤ t ∧ (t : ℕ) ≤ j)
        (max ((u : ℕ) - 1) i) (min ((v : ℕ) - 1) j) (by intro t; simp only; omega) with h | h
    · rw [h]; norm_num
    · exact absurd hv (by subst h; have := v.isLt; omega)
  · rw [if_neg hv]
    have hnone : ∀ t : Fin N,
        ¬ ((u : ℕ) ≤ (t : ℕ) + 1 ∧ (t : ℕ) + 1 ≤ v ∧ (i : ℕ) ≤ t ∧ (t : ℕ) ≤ j) := by
      intro t hh; omega
    rw [Finset.filter_false_of_mem (fun t _ ↦ hnone t)]; simp

/-- **The Euler form between interval modules.** `finrank C⁰ − finrank C¹` collapses to the closed
indicator `1[u≤i≤v≤j] − 1[i<u≤j+1≤v]` (value comparisons; the `Ext`-side term is false when `j = N`,
as `j+1 > v`). The `Hom`/`Ext¹` indicators split this via `euler_identity`. -/
theorem euler_interval (i j u v : Fin (N + 1)) :
    (finrank k (cochain0 (k := k) (intervalDim i j) (intervalDim u v)) : ℤ)
        - finrank k (cochain1 (k := k) (intervalDim i j) (intervalDim u v))
      = (if (u : ℕ) ≤ i ∧ (i : ℕ) ≤ v ∧ (v : ℕ) ≤ j then 1 else 0)
        - (if (i : ℕ) < u ∧ (u : ℕ) ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ v then (1 : ℤ) else 0) := by
  rw [finrank_cochain0, finrank_cochain1, c0_sum_eq, c1_sum_eq]
  have hi := i.isLt; have hj := j.isLt; have hu := u.isLt; have hv := v.isLt
  split <;> split <;> split <;> omega

section Witness

/-! ## Non-vacuity witness for the interval Euler form

`N = 2` (`Fin 3`), over `ℚ`. For `M_{01} → M_{12}` the Euler form is `finrank C⁰ − finrank C¹ =
0 − 1`: the `Hom` indicator `1[u≤i≤v≤j] = 1[1≤0…]` is `0`, the `Ext¹` indicator
`1[i<u≤j+1≤v] = 1[0<1≤2≤2]` is `1`. This pins both indicator pieces of `euler_interval` against a
nonzero value. -/

/-- `euler_interval` on `M_{01} → M_{12}` over `Fin 3`/`ℚ`: `finrank C⁰ − finrank C¹ = 0 − 1`
(`Hom`-indicator `0`, `Ext¹`-indicator `1`). -/
example :
    (finrank ℚ (cochain0 (k := ℚ) (intervalDim (0 : Fin 3) 1) (intervalDim 1 2)) : ℤ)
        - finrank ℚ (cochain1 (k := ℚ) (intervalDim (0 : Fin 3) 1) (intervalDim 1 2))
      = (0 : ℤ) - 1 := by
  rw [euler_interval]; decide

end Witness

end DLNFibre.Core

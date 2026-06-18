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

* `C⁰(M,N) = ∏_{v : Fin (N + 1)} Matrix (Fin (e v)) (Fin (d v)) k` — a vertex map at each vertex;
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

/-! ## The Hom and Ext¹ indicators between interval modules

The two indicator formulas (matching the recon Codex certificate): for interval modules `M_{ij}`
(source)
and `M_{uv}` (target) over a field,
`finrank Hom(M_{ij}, M_{uv}) = 1[u≤i≤v≤j]` and
`finrank deformationExt1(M_{ij}, M_{uv}) = 1[i<u≤j+1≤v]` (the latter false at `j = N`).
The `Hom` side is proved directly (constancy of a morphism's scalar on the connected overlap, with a
failing boundary forcing it to zero); the `Ext¹` side follows from it and `euler_identity` +
`euler_interval`. -/

/-- An inhabited interval-dimension index forces value membership `i ≤ w ≤ j`. -/
theorem mem_of_intervalDim_index {i j w : Fin (N + 1)} (r : Fin (intervalDim i j w)) :
    (i : ℕ) ≤ w ∧ (w : ℕ) ≤ j := by
  rw [intervalDim_eq_ite] at r
  by_cases h : (i : ℕ) ≤ w ∧ (w : ℕ) ≤ j
  · exact h
  · rw [if_neg h] at r; exact r.elim0

/-- `intervalDim i j w = 1` from value membership. -/
theorem intervalDim_eq_one_of_mem {i j w : Fin (N + 1)} (h : (i : ℕ) ≤ w ∧ (w : ℕ) ≤ j) :
    intervalDim i j w = 1 := by rw [intervalDim_eq_ite, if_pos h]

/-- **One-edge constancy.** On an edge `t` active in both modules, a morphism's scalar is unchanged:
`φ t.succ = φ t.castSucc` (the `1×1` commuting square `φ·1 = 1·φ`). -/
theorem hom_const_on_active (i j u v : Fin (N + 1))
    (φ : cochain0 (k := k) (intervalDim i j) (intervalDim u v))
    (hφ : φ ∈ Hom (intervalModule i j) (intervalModule u v)) (t : Fin N)
    (hMt : intervalActive i j t) (hNt : intervalActive u v t)
    (rs : Fin (intervalDim u v t.succ)) (cs : Fin (intervalDim i j t.succ))
    (rc : Fin (intervalDim u v t.castSucc)) (cc : Fin (intervalDim i j t.castSucc)) :
    φ t.succ rs cs = φ t.castSucc rc cc := by
  rw [mem_Hom_iff] at hφ
  have hd : intervalDim i j t.succ = 1 := by
    rw [intervalDim_eq_ite, if_pos]; obtain ⟨h1, h2⟩ := hMt
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢; omega
  have he : intervalDim u v t.castSucc = 1 := by
    rw [intervalDim_eq_ite, if_pos]; obtain ⟨h1, h2⟩ := hNt
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢; omega
  have huniq_d : Unique (Fin (intervalDim i j t.succ)) := by rw [hd]; infer_instance
  have huniq_e : Unique (Fin (intervalDim u v t.castSucc)) := by rw [he]; infer_instance
  have h := congrFun (congrFun (hφ t) rs) cc
  rw [intervalModule_active_eq_one i j t hMt, intervalModule_active_eq_one u v t hNt] at h
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton] at h
  rw [mul_one, one_mul] at h
  rw [Subsingleton.elim cs (default : Fin (intervalDim i j t.succ)),
      Subsingleton.elim rc (default : Fin (intervalDim u v t.castSucc))]
  exact h

/-- **General overlap constancy.** For `a ≤ w` both inside the overlap `[max i u, min j v]`, the
scalars agree: `φ w = φ a`. Forward induction; each edge strictly inside the overlap is active in
both
modules (`hom_const_on_active`). -/
theorem hom_scalar_const_gen (i j u v : Fin (N + 1))
    (φ : cochain0 (k := k) (intervalDim i j) (intervalDim u v))
    (hφ : φ ∈ Hom (intervalModule i j) (intervalModule u v)) (a : Fin (N + 1))
    (hai : (i : ℕ) ≤ a) (hau : (u : ℕ) ≤ a) (haj : (a : ℕ) ≤ j) (hav : (a : ℕ) ≤ v) :
    ∀ (w : Fin (N + 1)), (a : ℕ) ≤ w → (w : ℕ) ≤ j → (w : ℕ) ≤ v →
      ∀ (rs : Fin (intervalDim u v w)) (cs : Fin (intervalDim i j w))
        (ra : Fin (intervalDim u v a)) (ca : Fin (intervalDim i j a)),
      φ w rs cs = φ a ra ca := by
  intro w
  induction w using Fin.induction with
  | zero =>
    intro haw hwj hwv rs cs ra ca
    have ha0 : a = 0 := by apply Fin.ext; simp only [Fin.val_zero] at haw ⊢; omega
    subst ha0
    have h1u : intervalDim u v (0 : Fin (N + 1)) = 1 :=
      intervalDim_eq_one_of_mem ⟨hau, by simpa using hwv⟩
    have h1i : intervalDim i j 0 = 1 :=
      intervalDim_eq_one_of_mem ⟨by simpa using hai, by simpa using hwj⟩
    have su : Subsingleton (Fin (intervalDim u v (0 : Fin (N + 1)))) := by rw [h1u]; infer_instance
    have si : Subsingleton (Fin (intervalDim i j 0)) := by rw [h1i]; infer_instance
    congr 1
    · exact su.elim rs ra
    · exact si.elim cs ca
  | succ p ih =>
    intro haw hwj hwv rs cs ra ca
    by_cases hbase : (p.succ : ℕ) ≤ a
    · have hpa : a = p.succ := by apply Fin.ext; omega
      subst hpa
      have h1u : intervalDim u v p.succ = 1 :=
        intervalDim_eq_one_of_mem ⟨hau, by simpa using hwv⟩
      have h1i : intervalDim i j p.succ = 1 :=
        intervalDim_eq_one_of_mem ⟨by simpa using hai, by simpa using hwj⟩
      have su : Subsingleton (Fin (intervalDim u v p.succ)) := by rw [h1u]; infer_instance
      have si : Subsingleton (Fin (intervalDim i j p.succ)) := by rw [h1i]; infer_instance
      congr 1
      · exact su.elim rs ra
      · exact si.elim cs ca
    · rw [not_le] at hbase
      have hvp : (p.castSucc : ℕ) = (p : ℕ) := by simp [Fin.val_castSucc]
      have hsp : (p.succ : ℕ) = (p : ℕ) + 1 := by simp [Fin.val_succ]
      have hap : (a : ℕ) ≤ (p : ℕ) := by omega
      have hpj : (p : ℕ) ≤ j := by omega
      have hpv : (p : ℕ) ≤ v := by omega
      have hMt : intervalActive i j p := by
        refine ⟨?_, ?_⟩ <;> rw [Fin.le_def] <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
      have hNt : intervalActive u v p := by
        refine ⟨?_, ?_⟩ <;> rw [Fin.le_def] <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
      have h1u : intervalDim u v p.castSucc = 1 :=
        intervalDim_eq_one_of_mem ⟨by rw [hvp]; omega, by rw [hvp]; omega⟩
      have h1i : intervalDim i j p.castSucc = 1 :=
        intervalDim_eq_one_of_mem ⟨by rw [hvp]; omega, by rw [hvp]; omega⟩
      have hrc : Nonempty (Fin (intervalDim u v p.castSucc)) := by rw [h1u]; exact ⟨0⟩
      have hcc : Nonempty (Fin (intervalDim i j p.castSucc)) := by rw [h1i]; exact ⟨0⟩
      obtain ⟨rc0⟩ := hrc; obtain ⟨cc0⟩ := hcc
      have hc := hom_const_on_active i j u v φ hφ p hMt hNt rs cs rc0 cc0
      rw [hc, ih (by rw [hvp]; omega) (by rw [hvp]; omega) (by rw [hvp]; omega) rc0 cc0 ra ca]

/-- The const-`1` generator family of `Hom(M_{ij}, M_{uv})` (the identity on the overlap). -/
def homGen (i j u v : Fin (N + 1)) : cochain0 (k := k) (intervalDim i j) (intervalDim u v) :=
  fun _ _ _ ↦ (1 : k)

/-- The const-`1` generator is a morphism when `u≤i≤v≤j` (the overlap is connected and left-aligned,
so every edge in it is active in both modules). -/
theorem homGen_mem (i j u v : Fin (N + 1)) (h : (u : ℕ) ≤ i ∧ (i : ℕ) ≤ v ∧ (v : ℕ) ≤ j) :
    homGen (k := k) i j u v ∈ Hom (intervalModule i j) (intervalModule u v) := by
  rw [mem_Hom_iff]; intro t; funext a b
  have ha : (u : ℕ) ≤ (t : ℕ) + 1 ∧ (t : ℕ) + 1 ≤ v := by
    by_contra hc
    have : intervalDim u v t.succ = 0 := by
      rw [intervalDim_eq_ite, if_neg]; simpa [Fin.val_succ] using hc
    rw [this] at a; exact a.elim0
  have hb : (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ j := by
    by_contra hc
    have : intervalDim i j t.castSucc = 0 := by
      rw [intervalDim_eq_ite, if_neg]; simpa [Fin.val_castSucc] using hc
    rw [this] at b; exact b.elim0
  have hMact : intervalModule (k := k) i j t = fun _ _ ↦ (1 : k) := by
    apply intervalModule_active_eq_one; constructor <;> rw [Fin.le_def] <;>
      simp only [Fin.val_succ, Fin.val_castSucc] <;> omega
  have hNact : intervalModule (k := k) u v t = fun _ _ ↦ (1 : k) := by
    apply intervalModule_active_eq_one; constructor <;> rw [Fin.le_def] <;>
      simp only [Fin.val_succ, Fin.val_castSucc] <;> omega
  rw [hMact, hNact]
  simp only [homGen, Matrix.mul_apply]
  have hd1 : intervalDim i j t.succ = 1 := by
    rw [intervalDim_eq_ite, if_pos]; simp only [Fin.val_succ]; omega
  have he1 : intervalDim u v t.castSucc = 1 := by
    rw [intervalDim_eq_ite, if_pos]; simp only [Fin.val_castSucc]; omega
  rw [Finset.sum_congr rfl (fun _ _ ↦ by ring : ∀ x ∈ _, (1 : k) * 1 = 1),
      Finset.sum_congr rfl (fun _ _ ↦ by ring : ∀ x ∈ _, (1 : k) * 1 = 1)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hd1, he1, one_smul]

/-- Boundary forcing (lower vertex): if the source edge `p` is active but the target's lower vertex
is empty, then the morphism's scalar at the upper vertex is `0`
(the square reads `φ·1 = empty sum`). -/
theorem hom_force_zero_lower (i j u v : Fin (N + 1))
    (φ : cochain0 (k := k) (intervalDim i j) (intervalDim u v))
    (hφ : φ ∈ Hom (intervalModule i j) (intervalModule u v)) (p : Fin N)
    (hMp : intervalActive i j p) (hNlo : intervalDim u v p.castSucc = 0)
    (rs : Fin (intervalDim u v p.succ)) (cs : Fin (intervalDim i j p.succ)) :
    φ p.succ rs cs = 0 := by
  rw [mem_Hom_iff] at hφ
  have hdlo : intervalDim i j p.castSucc = 1 := by
    rw [intervalDim_eq_ite, if_pos]; obtain ⟨h1, h2⟩ := hMp
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢; omega
  have huniq : Unique (Fin (intervalDim i j p.castSucc)) := by rw [hdlo]; infer_instance
  have hempty : IsEmpty (Fin (intervalDim u v p.castSucc)) := by rw [hNlo]; infer_instance
  have hd : intervalDim i j p.succ = 1 := by
    rw [intervalDim_eq_ite, if_pos]; obtain ⟨h1, h2⟩ := hMp
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢; omega
  have : Unique (Fin (intervalDim i j p.succ)) := by rw [hd]; infer_instance
  have h := congrFun (congrFun (hφ p) rs) (default : Fin (intervalDim i j p.castSucc))
  rw [intervalModule_active_eq_one i j p hMp] at h
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, mul_one,
    Finset.univ_eq_empty, Finset.sum_empty] at h
  rw [Subsingleton.elim cs (default : Fin (intervalDim i j p.succ))]
  exact h

/-- Boundary forcing (upper vertex): if the target edge `p` is active but the source's upper vertex
is empty, the morphism's scalar at the lower vertex is `0`. -/
theorem hom_force_zero_upper (i j u v : Fin (N + 1))
    (φ : cochain0 (k := k) (intervalDim i j) (intervalDim u v))
    (hφ : φ ∈ Hom (intervalModule i j) (intervalModule u v)) (p : Fin N)
    (hNp : intervalActive u v p) (hMup : intervalDim i j p.succ = 0)
    (rs : Fin (intervalDim u v p.castSucc)) (cs : Fin (intervalDim i j p.castSucc)) :
    φ p.castSucc rs cs = 0 := by
  rw [mem_Hom_iff] at hφ
  have heup : intervalDim u v p.succ = 1 := by
    rw [intervalDim_eq_ite, if_pos]; obtain ⟨h1, h2⟩ := hNp
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢; omega
  have : Unique (Fin (intervalDim u v p.succ)) := by rw [heup]; infer_instance
  have hempty : IsEmpty (Fin (intervalDim i j p.succ)) := by rw [hMup]; infer_instance
  have he : intervalDim u v p.castSucc = 1 := by
    rw [intervalDim_eq_ite, if_pos]; obtain ⟨h1, h2⟩ := hNp
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢; omega
  have : Unique (Fin (intervalDim u v p.castSucc)) := by rw [he]; infer_instance
  have h := congrFun (congrFun (hφ p) (default : Fin (intervalDim u v p.succ))) cs
  rw [intervalModule_active_eq_one u v p hNp] at h
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, one_mul,
    Finset.univ_eq_empty, Finset.sum_empty] at h
  rw [Subsingleton.elim rs (default : Fin (intervalDim u v p.castSucc))]
  exact h.symm

/-- Positive case of the `Hom` indicator: `finrank Hom = 1` when `u≤i≤v≤j`. `Hom = k ∙ homGen` —
every morphism is its scalar at vertex `i` times the const-`1` generator (overlap constancy plus
vanishing `0`-dimensional entries). -/
theorem finrank_Hom_interval_pos (i j u v : Fin (N + 1))
    (hpos : (u : ℕ) ≤ i ∧ (i : ℕ) ≤ v ∧ (v : ℕ) ≤ j) :
    finrank k (Hom (intervalModule (k := k) i j) (intervalModule u v)) = 1 := by
  have hg := homGen_mem (k := k) i j u v hpos
  have hi1u : intervalDim u v i = 1 := intervalDim_eq_one_of_mem ⟨hpos.1, hpos.2.1⟩
  have hi1i : intervalDim i j i = 1 :=
    intervalDim_eq_one_of_mem ⟨le_refl _, le_trans hpos.2.1 hpos.2.2⟩
  have pu : 0 < intervalDim u v i := by rw [hi1u]; norm_num
  have pii : 0 < intervalDim i j i := by rw [hi1i]; norm_num
  have hspan : Hom (intervalModule (k := k) i j) (intervalModule u v)
      = k ∙ homGen (k := k) i j u v := by
    apply le_antisymm
    · intro φ hφ
      rw [Submodule.mem_span_singleton]
      refine ⟨φ i ⟨0, pu⟩ ⟨0, pii⟩, ?_⟩
      funext w rs cs
      change (φ i ⟨0, pu⟩ ⟨0, pii⟩ • homGen (k := k) i j u v) w rs cs = φ w rs cs
      simp only [homGen, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_one]
      obtain ⟨hwu, hwv⟩ := mem_of_intervalDim_index rs
      obtain ⟨hwi, hwj⟩ := mem_of_intervalDim_index cs
      exact (hom_scalar_const_gen i j u v φ hφ i (le_refl _) hpos.1 (le_trans hpos.2.1 hpos.2.2)
        hpos.2.1 w hwi hwj hwv rs cs ⟨0, pu⟩ ⟨0, pii⟩).symm
    · rw [Submodule.span_singleton_le_iff_mem]; exact hg
  rw [hspan, finrank_span_singleton]
  intro hz
  have := congrFun (congrFun (congrFun hz i) ⟨0, pu⟩) ⟨0, pii⟩
  simp only [homGen, Pi.zero_apply] at this
  exact one_ne_zero this

/-- Negative case of the `Hom` indicator: `Hom = ⊥` when `¬(u≤i≤v≤j)`. A failing boundary forces the
overlap scalar to `0` (left edge if `i<u`, right edge if `j<v`); an empty overlap (`i>v`) admits no
scalar. Overlap constancy (`hom_scalar_const_gen`) spreads the zero. -/
theorem Hom_interval_eq_bot (i j u v : Fin (N + 1))
    (hneg : ¬ ((u : ℕ) ≤ i ∧ (i : ℕ) ≤ v ∧ (v : ℕ) ≤ j)) :
    Hom (intervalModule (k := k) i j) (intervalModule u v) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  funext w rs cs
  simp only [Pi.zero_apply, Matrix.zero_apply]
  obtain ⟨hwu, hwv⟩ := mem_of_intervalDim_index rs
  obtain ⟨hwi, hwj⟩ := mem_of_intervalDim_index cs
  rcases not_and_or.mp hneg with hui | hrest
  · have hiu : (i : ℕ) < u := by omega
    have hpu : (u : ℕ) - 1 < N := by have := u.isLt; omega
    set p : Fin N := ⟨(u : ℕ) - 1, hpu⟩ with hp
    have hpsucc : (p.succ : ℕ) = (u : ℕ) := by simp [hp]; omega
    have hpcast : (p.castSucc : ℕ) = (u : ℕ) - 1 := by simp [hp]
    have hMp : intervalActive i j p := by
      refine ⟨?_, ?_⟩ <;> rw [Fin.le_def] <;>
        simp only [Fin.val_castSucc, Fin.val_succ, hp] <;> omega
    have hNlo : intervalDim u v p.castSucc = 0 := by
      rw [intervalDim_eq_ite, if_neg]; · rw [hpcast]; rintro ⟨_, _⟩; omega
    have h1ru : intervalDim u v p.succ = 1 := by
      rw [intervalDim_eq_ite, if_pos]; rw [hpsucc]; exact ⟨by omega, by omega⟩
    have h1cu : intervalDim i j p.succ = 1 := by
      rw [intervalDim_eq_ite, if_pos]; rw [hpsucc]; exact ⟨by omega, by omega⟩
    have rz : Fin (intervalDim u v p.succ) := ⟨0, by rw [h1ru]; norm_num⟩
    have cz : Fin (intervalDim i j p.succ) := ⟨0, by rw [h1cu]; norm_num⟩
    have hforce := hom_force_zero_lower i j u v φ hφ p hMp hNlo rz cz
    have hconst := hom_scalar_const_gen i j u v φ hφ p.succ
      (by rw [hpsucc]; omega) (by rw [hpsucc]) (by rw [hpsucc]; omega) (by rw [hpsucc]; omega)
      w (by rw [hpsucc]; omega) hwj hwv rs cs rz cz
    rw [hconst, hforce]
  · rcases not_and_or.mp hrest with hiv | hvj
    · exact absurd (le_trans hwi hwv) hiv
    · have hjv : (j : ℕ) < v := by omega
      have hjN : (j : ℕ) < N := by have := v.isLt; omega
      set p : Fin N := ⟨(j : ℕ), hjN⟩ with hp
      have hpcast : (p.castSucc : ℕ) = (j : ℕ) := by simp [hp]
      have hpsucc : (p.succ : ℕ) = (j : ℕ) + 1 := by simp [hp]
      have hNp : intervalActive u v p := by
        refine ⟨?_, ?_⟩ <;> rw [Fin.le_def] <;>
          simp only [Fin.val_castSucc, Fin.val_succ, hp] <;> omega
      have hMup : intervalDim i j p.succ = 0 := by
        rw [intervalDim_eq_ite, if_neg]; · rw [hpsucc]; rintro ⟨_, _⟩; omega
      have h1rj : intervalDim u v p.castSucc = 1 := by
        rw [intervalDim_eq_ite, if_pos]; rw [hpcast]; exact ⟨by omega, by omega⟩
      have h1cj : intervalDim i j p.castSucc = 1 := by
        rw [intervalDim_eq_ite, if_pos]; rw [hpcast]; exact ⟨by omega, by omega⟩
      have rz : Fin (intervalDim u v p.castSucc) := ⟨0, by rw [h1rj]; norm_num⟩
      have cz : Fin (intervalDim i j p.castSucc) := ⟨0, by rw [h1cj]; norm_num⟩
      have hforce := hom_force_zero_upper i j u v φ hφ p hNp hMup rz cz
      have hconst := hom_scalar_const_gen i j u v φ hφ w
        hwi hwu hwj hwv p.castSucc (by rw [hpcast]; omega) (by rw [hpcast]) (by rw [hpcast]; omega)
        rz cz rs cs
      rw [← hconst, hforce]

/-- **The Hom indicator.** `finrank Hom(M_{ij}, M_{uv}) = 1[u≤i≤v≤j]` (target bar starts no later
than the source, ends inside it). -/
theorem finrank_Hom_interval (i j u v : Fin (N + 1)) :
    finrank k (Hom (intervalModule (k := k) i j) (intervalModule u v))
      = if (u : ℕ) ≤ i ∧ (i : ℕ) ≤ v ∧ (v : ℕ) ≤ j then 1 else 0 := by
  by_cases h : (u : ℕ) ≤ i ∧ (i : ℕ) ≤ v ∧ (v : ℕ) ≤ j
  · rw [if_pos h, finrank_Hom_interval_pos i j u v h]
  · rw [if_neg h, Hom_interval_eq_bot i j u v h, finrank_bot]

/-- **The Ext¹ indicator.** `finrank deformationExt1(M_{ij}, M_{uv}) = 1[i<u≤j+1≤v]` (false when
`j = N`). From the `Hom` indicator and the Euler identity. -/
theorem finrank_deformationExt1_interval (i j u v : Fin (N + 1)) :
    finrank k (deformationExt1 (intervalModule (k := k) i j) (intervalModule u v))
      = if (i : ℕ) < u ∧ (u : ℕ) ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ v then 1 else 0 := by
  have he := euler_identity (intervalModule (k := k) i j) (intervalModule u v)
  rw [euler_interval, finrank_Hom_interval] at he
  split_ifs at he ⊢ <;> push_cast at he ⊢ <;> omega

/-! ## Additivity over `dirSum` and the headline `dim Ext¹(M,M)` formula

The deformation differential `δ` is block-diagonal under the binary direct sum `dirSum` (the
engine's
`Fin a ⊕ Fin b ≃ Fin (a + b)` reindexed block matrix), so `range δ` — and hence the cokernel
`deformationExt1` — splits as a product, and `finrank` adds. Folded over the interval list, this
gives
the headline: `finrank deformationExt1(⊕L, ⊕L)` is the double sum over ordered list pairs of
the `Ext¹`
indicator (Le Halleur–Rimányi Cor 3.5, the algebraic `Ext` codimension). -/

noncomputable def matrixRowSplit (a b : ℕ) (γ : Type*) [Fintype γ] :
    Matrix (Fin (a + b)) γ k ≃ₗ[k] Matrix (Fin a) γ k × Matrix (Fin b) γ k where
  toFun M := (Matrix.of (fun i j => M (finSumFinEquiv (Sum.inl i)) j),
              Matrix.of (fun i j => M (finSumFinEquiv (Sum.inr i)) j))
  invFun P := Matrix.of fun i j =>
    Sum.elim (fun a => P.1 a j) (fun b => P.2 b j) (finSumFinEquiv.symm i)
  map_add' M M' := rfl
  map_smul' r M := by refine Prod.ext ?_ ?_ <;> · funext i j; rfl
  left_inv M := by
    funext i j
    change Sum.elim (fun a => M (finSumFinEquiv (Sum.inl a)) j)
        (fun b => M (finSumFinEquiv (Sum.inr b)) j) (finSumFinEquiv.symm i) = M i j
    conv_rhs => rw [← Equiv.apply_symm_apply finSumFinEquiv i]
    rcases finSumFinEquiv.symm i with c | d <;> simp only [Sum.elim_inl, Sum.elim_inr]
  right_inv P := by
    refine Prod.ext ?_ ?_ <;> funext i j <;>
      simp only [Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
@[simp] theorem rowSplit_fst {a b : ℕ} {γ : Type*} [Fintype γ]
    (M : Matrix (Fin (a + b)) γ k) (i j) :
    (matrixRowSplit a b γ M).1 i j = M (finSumFinEquiv (Sum.inl i)) j := rfl
@[simp] theorem rowSplit_snd {a b : ℕ} {γ : Type*} [Fintype γ]
    (M : Matrix (Fin (a + b)) γ k) (i j) :
    (matrixRowSplit a b γ M).2 i j = M (finSumFinEquiv (Sum.inr i)) j := rfl
theorem rowSplit_block_mul {p q r s m : ℕ}
    (P : Matrix (Fin p) (Fin r) k) (Q : Matrix (Fin q) (Fin s) k)
    (φ : Matrix (Fin (r + s)) (Fin m) k) :
    matrixRowSplit p q (Fin m)
        (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 Q) * φ)
      = (P * (matrixRowSplit r s (Fin m) φ).1, Q * (matrixRowSplit r s (Fin m) φ).2) := by
  refine Prod.ext ?_ ?_
  · funext i j
    rw [rowSplit_fst, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp (fun x =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 Q)
        (finSumFinEquiv (Sum.inl i)) x * φ x j)]
    rw [Fintype.sum_sum_type]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero, Matrix.mul_apply, rowSplit_fst]
  · funext i j
    rw [rowSplit_snd, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp (fun x =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 Q)
        (finSumFinEquiv (Sum.inr i)) x * φ x j)]
    rw [Fintype.sum_sum_type]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
      zero_add, Matrix.mul_apply, rowSplit_snd]
-- row-split commutes with right-mult (shared source)
theorem rowSplit_mul_right {p q r m : ℕ} (X : Matrix (Fin (p + q)) (Fin r) k)
    (M : Matrix (Fin r) (Fin m) k) :
    matrixRowSplit p q (Fin m) (X * M)
      = ((matrixRowSplit p q (Fin r) X).1 * M, (matrixRowSplit p q (Fin r) X).2 * M) := by
  refine Prod.ext ?_ ?_ <;> · funext i j; simp only [rowSplit_fst, rowSplit_snd, Matrix.mul_apply]
-- pi-prod swap
noncomputable def piProdSwap (ι : Type*) (A B : ι → Type*) [∀ i, AddCommGroup (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (A i)] [∀ i, Module k (B i)] :
    (∀ i, A i × B i) ≃ₗ[k] (∀ i, A i) × (∀ i, B i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

-- cochain1 split: cochain1 d (e+e') ≃ₗ cochain1 d e × cochain1 d e'
noncomputable def cochain1Split {N : ℕ} (d e e' : Fin (N + 1) → ℕ) :
    cochain1 (k := k) d (fun l => e l + e' l)
      ≃ₗ[k] cochain1 (k := k) d e × cochain1 (k := k) d e' :=
  (LinearEquiv.piCongrRight
      (fun i => matrixRowSplit (e i.succ) (e' i.succ) (Fin (d i.castSucc)))).trans
    (piProdSwap (Fin N) _ _)

noncomputable def cochain0Split {N : ℕ} (d e e' : Fin (N + 1) → ℕ) :
    cochain0 (k := k) d (fun l => e l + e' l)
      ≃ₗ[k] cochain0 (k := k) d e × cochain0 (k := k) d e' :=
  (LinearEquiv.piCongrRight (fun v => matrixRowSplit (e v) (e' v) (Fin (d v)))).trans
    (piProdSwap (Fin (N + 1)) _ _)
theorem cochain1Split_fst {N : ℕ} {d e e' : Fin (N + 1) → ℕ}
    (φ : cochain1 (k := k) d (fun l => e l + e' l)) (i) :
    (cochain1Split d e e' φ).1 i
      = (matrixRowSplit (e i.succ) (e' i.succ) (Fin (d i.castSucc)) (φ i)).1 := rfl
theorem cochain1Split_snd {N : ℕ} {d e e' : Fin (N + 1) → ℕ}
    (φ : cochain1 (k := k) d (fun l => e l + e' l)) (i) :
    (cochain1Split d e e' φ).2 i
      = (matrixRowSplit (e i.succ) (e' i.succ) (Fin (d i.castSucc)) (φ i)).2 := rfl
theorem cochain0Split_fst {N : ℕ} {d e e' : Fin (N + 1) → ℕ}
    (φ : cochain0 (k := k) d (fun l => e l + e' l)) (v) :
    (cochain0Split d e e' φ).1 v = (matrixRowSplit (e v) (e' v) (Fin (d v)) (φ v)).1 := rfl
theorem cochain0Split_snd {N : ℕ} {d e e' : Fin (N + 1) → ℕ}
    (φ : cochain0 (k := k) d (fun l => e l + e' l)) (v) :
    (cochain0Split d e e' φ).2 v = (matrixRowSplit (e v) (e' v) (Fin (d v)) (φ v)).2 := rfl
theorem deformationδ_dirSum_compat {N : ℕ} {d e e' : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (Nt : Tuple (k := k) e) (Nt' : Tuple (k := k) e')
    (φ : cochain0 (k := k) d (fun l => e l + e' l)) :
    cochain1Split d e e' (deformationδ M (dirSum Nt Nt') φ)
      = (deformationδ M Nt (cochain0Split d e e' φ).1,
         deformationδ M Nt' (cochain0Split d e e' φ).2) := by
  refine Prod.ext ?_ ?_
  · funext i
    rw [cochain1Split_fst]
    change ((matrixRowSplit _ _ _ (φ i.succ * M i - dirSum Nt Nt' i * φ i.castSucc)).1) = _
    rw [map_sub, rowSplit_mul_right, dirSum, rowSplit_block_mul]
    simp only [Prod.fst_sub, deformationδ_apply, cochain0Split_fst]
  · funext i
    rw [cochain1Split_snd]
    change ((matrixRowSplit _ _ _ (φ i.succ * M i - dirSum Nt Nt' i * φ i.castSucc)).2) = _
    rw [map_sub, rowSplit_mul_right, dirSum, rowSplit_block_mul]
    simp only [Prod.snd_sub, deformationδ_apply, cochain0Split_snd]
theorem range_deformationδ_dirSum {N : ℕ} {d e e' : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
    (Nt : Tuple (k := k) e) (Nt' : Tuple (k := k) e') :
    Submodule.map ((cochain1Split d e e' (k := k)) : _ →ₗ[k] _)
        (LinearMap.range (deformationδ M (dirSum Nt Nt')))
      = (LinearMap.range (deformationδ M Nt)).prod (LinearMap.range (deformationδ M Nt')) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_prod, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨φ, rfl⟩, rfl⟩
    rw [deformationδ_dirSum_compat]
    exact ⟨⟨(cochain0Split d e e' φ).1, rfl⟩, ⟨(cochain0Split d e e' φ).2, rfl⟩⟩
  · rintro ⟨⟨ψ, hψ⟩, ⟨ψ', hψ'⟩⟩
    refine ⟨deformationδ M (dirSum Nt Nt') ((cochain0Split d e e').symm (ψ, ψ')), ⟨_, rfl⟩, ?_⟩
    rw [deformationδ_dirSum_compat]
    simp only [LinearEquiv.apply_symm_apply, hψ, hψ']

/-- **Additivity in the target.** `finrank deformationExt1` adds over a direct sum of targets:
the differential is block-diagonal under `dirSum`, so the range (and hence the cokernel) splits. -/
theorem finrank_deformationExt1_dirSum_right {N : ℕ} {d e e' : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d)
    (Nt : Tuple (k := k) e) (Nt' : Tuple (k := k) e') :
    finrank k (deformationExt1 M (dirSum Nt Nt'))
      = finrank k (deformationExt1 M Nt) + finrank k (deformationExt1 M Nt') := by
  have hq : ∀ {ee : Fin (N + 1)→ℕ} (NN : Tuple (k := k) ee), finrank k (deformationExt1 M NN)
      + finrank k (LinearMap.range (deformationδ M NN)) = finrank k (cochain1 (k := k) d ee) :=
    fun NN => Submodule.finrank_quotient_add_finrank _
  have hr : finrank k (LinearMap.range (deformationδ M (dirSum Nt Nt')))
      = finrank k (LinearMap.range (deformationδ M Nt))
        + finrank k (LinearMap.range (deformationδ M Nt')) := by
    rw [← LinearEquiv.finrank_map_eq (cochain1Split d e e' (k := k))
        (LinearMap.range (deformationδ M (dirSum Nt Nt'))), range_deformationδ_dirSum,
      finrank_submodule_prod]
  have hc1 : finrank k (cochain1 (k := k) d (fun l => e l + e' l))
      = finrank k (cochain1 (k := k) d e) + finrank k (cochain1 (k := k) d e') := by
    rw [(cochain1Split d e e' (k := k)).finrank_eq, Module.finrank_prod]
  have e1 := hq (dirSum Nt Nt'); have e2 := hq Nt; have e3 := hq Nt'
  rw [hc1] at e1; omega
noncomputable def matrixColSplit (γ : Type*) [Fintype γ] (a b : ℕ) :
    Matrix γ (Fin (a + b)) k ≃ₗ[k] Matrix γ (Fin a) k × Matrix γ (Fin b) k where
  toFun M := (Matrix.of (fun i j => M i (finSumFinEquiv (Sum.inl j))),
              Matrix.of (fun i j => M i (finSumFinEquiv (Sum.inr j))))
  invFun P := Matrix.of fun i j =>
    Sum.elim (fun a => P.1 i a) (fun b => P.2 i b) (finSumFinEquiv.symm j)
  map_add' M M' := rfl
  map_smul' r M := by refine Prod.ext ?_ ?_ <;> · funext i j; rfl
  left_inv M := by
    funext i j
    change Sum.elim (fun a => M i (finSumFinEquiv (Sum.inl a)))
        (fun b => M i (finSumFinEquiv (Sum.inr b))) (finSumFinEquiv.symm j) = M i j
    conv_rhs => rw [← Equiv.apply_symm_apply finSumFinEquiv j]
    rcases finSumFinEquiv.symm j with c | d <;> simp only [Sum.elim_inl, Sum.elim_inr]
  right_inv P := by
    refine Prod.ext ?_ ?_ <;> funext i j <;>
      simp only [Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
@[simp] theorem colSplit_fst {γ : Type*} [Fintype γ] {a b : ℕ}
    (M : Matrix γ (Fin (a + b)) k) (i j) :
    (matrixColSplit γ a b M).1 i j = M i (finSumFinEquiv (Sum.inl j)) := rfl
@[simp] theorem colSplit_snd {γ : Type*} [Fintype γ] {a b : ℕ}
    (M : Matrix γ (Fin (a + b)) k) (i j) :
    (matrixColSplit γ a b M).2 i j = M i (finSumFinEquiv (Sum.inr j)) := rfl
-- X * reindex(fromBlocks A 0 0 B) col-splits as (X.col1 * A, X.col2 * B)
theorem colSplit_mul_block {p r s t1 t2 : ℕ}
    (X : Matrix (Fin p) (Fin (r + s)) k) (A : Matrix (Fin r) (Fin t1) k)
    (B : Matrix (Fin s) (Fin t2) k) :
    matrixColSplit (Fin p) t1 t2
        (X * Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
      = ((matrixColSplit (Fin p) r s X).1 * A, (matrixColSplit (Fin p) r s X).2 * B) := by
  refine Prod.ext ?_ ?_
  · funext i j
    rw [colSplit_fst, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp (fun x =>
      X i x * Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B) x
        (finSumFinEquiv (Sum.inl j)))]
    rw [Fintype.sum_sum_type]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero, Matrix.mul_apply, colSplit_fst]
  · funext i j
    rw [colSplit_snd, Matrix.mul_apply]
    rw [← finSumFinEquiv.sum_comp (fun x =>
      X i x * Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B) x
        (finSumFinEquiv (Sum.inr j)))]
    rw [Fintype.sum_sum_type]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
      zero_add, Matrix.mul_apply, colSplit_snd]
-- col-split commutes with left-mult (shared target N)
theorem colSplit_mul_left {p q r s : ℕ} (Y : Matrix (Fin p) (Fin q) k)
    (X : Matrix (Fin q) (Fin (r + s)) k) :
    matrixColSplit (Fin p) r s (Y * X)
      = (Y * (matrixColSplit (Fin q) r s X).1, Y * (matrixColSplit (Fin q) r s X).2) := by
  refine Prod.ext ?_ ?_ <;> · funext i j; simp only [colSplit_fst, colSplit_snd, Matrix.mul_apply]
-- pi-prod swap (reuse)
noncomputable def piProdSwapL (ι : Type*) (A B : ι → Type*) [∀ i, AddCommGroup (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (A i)] [∀ i, Module k (B i)] :
    (∀ i, A i × B i) ≃ₗ[k] (∀ i, A i) × (∀ i, B i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
-- cochain splits on COLUMNS (source dim d = d1+d2)
noncomputable def cochain0SplitL {N : ℕ} (d1 d2 e : Fin (N + 1) → ℕ) :
    cochain0 (k := k) (fun l => d1 l + d2 l) e
      ≃ₗ[k] cochain0 (k := k) d1 e × cochain0 (k := k) d2 e :=
  (LinearEquiv.piCongrRight (fun v => matrixColSplit (Fin (e v)) (d1 v) (d2 v))).trans
    (piProdSwapL (Fin (N + 1)) _ _)
noncomputable def cochain1SplitL {N : ℕ} (d1 d2 e : Fin (N + 1) → ℕ) :
    cochain1 (k := k) (fun l => d1 l + d2 l) e
      ≃ₗ[k] cochain1 (k := k) d1 e × cochain1 (k := k) d2 e :=
  (LinearEquiv.piCongrRight
      (fun i => matrixColSplit (Fin (e i.succ)) (d1 i.castSucc) (d2 i.castSucc))).trans
    (piProdSwapL (Fin N) _ _)
theorem cochain1SplitL_fst {N : ℕ} {d1 d2 e : Fin (N + 1) → ℕ}
    (φ : cochain1 (k := k) (fun l => d1 l + d2 l) e) (i) :
    (cochain1SplitL d1 d2 e φ).1 i
      = (matrixColSplit (Fin (e i.succ)) (d1 i.castSucc) (d2 i.castSucc) (φ i)).1 := rfl
theorem cochain1SplitL_snd {N : ℕ} {d1 d2 e : Fin (N + 1) → ℕ}
    (φ : cochain1 (k := k) (fun l => d1 l + d2 l) e) (i) :
    (cochain1SplitL d1 d2 e φ).2 i
      = (matrixColSplit (Fin (e i.succ)) (d1 i.castSucc) (d2 i.castSucc) (φ i)).2 := rfl
theorem cochain0SplitL_fst {N : ℕ} {d1 d2 e : Fin (N + 1) → ℕ}
    (φ : cochain0 (k := k) (fun l => d1 l + d2 l) e) (v) :
    (cochain0SplitL d1 d2 e φ).1 v = (matrixColSplit (Fin (e v)) (d1 v) (d2 v) (φ v)).1 := rfl
theorem cochain0SplitL_snd {N : ℕ} {d1 d2 e : Fin (N + 1) → ℕ}
    (φ : cochain0 (k := k) (fun l => d1 l + d2 l) e) (v) :
    (cochain0SplitL d1 d2 e φ).2 v = (matrixColSplit (Fin (e v)) (d1 v) (d2 v) (φ v)).2 := rfl

theorem deformationδ_dirSum_compat_left {N : ℕ} {d1 d2 e : Fin (N + 1) → ℕ} (A : Tuple (k := k) d1)
    (B : Tuple (k := k) d2) (Nt : Tuple (k := k) e)
    (φ : cochain0 (k := k) (fun l => d1 l + d2 l) e) :
    cochain1SplitL d1 d2 e (deformationδ (dirSum A B) Nt φ)
      = (deformationδ A Nt (cochain0SplitL d1 d2 e φ).1,
         deformationδ B Nt (cochain0SplitL d1 d2 e φ).2) := by
  refine Prod.ext ?_ ?_
  · funext i
    rw [cochain1SplitL_fst]
    change ((matrixColSplit _ _ _ (φ i.succ * dirSum A B i - Nt i * φ i.castSucc)).1) = _
    rw [map_sub, dirSum, colSplit_mul_block, colSplit_mul_left]
    simp only [Prod.fst_sub, deformationδ_apply, cochain0SplitL_fst]
  · funext i
    rw [cochain1SplitL_snd]
    change ((matrixColSplit _ _ _ (φ i.succ * dirSum A B i - Nt i * φ i.castSucc)).2) = _
    rw [map_sub, dirSum, colSplit_mul_block, colSplit_mul_left]
    simp only [Prod.snd_sub, deformationδ_apply, cochain0SplitL_snd]

theorem range_deformationδ_dirSum_left {N : ℕ} {d1 d2 e : Fin (N + 1) → ℕ} (A : Tuple (k := k) d1)
    (B : Tuple (k := k) d2) (Nt : Tuple (k := k) e) :
    Submodule.map ((cochain1SplitL d1 d2 e (k := k)) : _ →ₗ[k] _)
        (LinearMap.range (deformationδ (dirSum A B) Nt))
      = (LinearMap.range (deformationδ A Nt)).prod (LinearMap.range (deformationδ B Nt)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_prod, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨φ, rfl⟩, rfl⟩
    rw [deformationδ_dirSum_compat_left]
    exact ⟨⟨(cochain0SplitL d1 d2 e φ).1, rfl⟩, ⟨(cochain0SplitL d1 d2 e φ).2, rfl⟩⟩
  · rintro ⟨⟨ψ, hψ⟩, ⟨ψ', hψ'⟩⟩
    refine ⟨deformationδ (dirSum A B) Nt ((cochain0SplitL d1 d2 e).symm (ψ, ψ')), ⟨_, rfl⟩, ?_⟩
    rw [deformationδ_dirSum_compat_left]
    simp only [LinearEquiv.apply_symm_apply, hψ, hψ']

theorem finrank_deformationExt1_dirSum_left {N : ℕ} {d1 d2 e : Fin (N + 1) → ℕ}
    (A : Tuple (k := k) d1)
    (B : Tuple (k := k) d2) (Nt : Tuple (k := k) e) :
    finrank k (deformationExt1 (dirSum A B) Nt)
      = finrank k (deformationExt1 A Nt) + finrank k (deformationExt1 B Nt) := by
  have hq : ∀ {dd : Fin (N + 1)→ℕ} (AA : Tuple (k := k) dd), finrank k (deformationExt1 AA Nt)
      + finrank k (LinearMap.range (deformationδ AA Nt)) = finrank k (cochain1 (k := k) dd e) :=
    fun AA => Submodule.finrank_quotient_add_finrank _
  have hr : finrank k (LinearMap.range (deformationδ (dirSum A B) Nt))
      = finrank k (LinearMap.range (deformationδ A Nt))
        + finrank k (LinearMap.range (deformationδ B Nt)) := by
    rw [← LinearEquiv.finrank_map_eq (cochain1SplitL d1 d2 e (k := k))
        (LinearMap.range (deformationδ (dirSum A B) Nt)), range_deformationδ_dirSum_left,
      finrank_submodule_prod]
  have hc1 : finrank k (cochain1 (k := k) (fun l => d1 l + d2 l) e)
      = finrank k (cochain1 (k := k) d1 e) + finrank k (cochain1 (k := k) d2 e) := by
    rw [(cochain1SplitL d1 d2 e (k := k)).finrank_eq, Module.finrank_prod]
  have e1 := hq (dirSum A B); have e2 := hq A; have e3 := hq B
  rw [hc1] at e1; omega
theorem finrank_deformationExt1_eq_zero_of_cochain1 {N : ℕ} {d e : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d)
    (Nt : Tuple (k := k) e) (h : finrank k (cochain1 (k := k) d e) = 0) :
    finrank k (deformationExt1 M Nt) = 0 := by
  have hle : finrank k (deformationExt1 M Nt) ≤ finrank k (cochain1 (k := k) d e) :=
    Submodule.finrank_quotient_le _
  omega
theorem finrank_deformationExt1_intervalDirectSum_right {N : ℕ} {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d)
    (L : List (Fin (N + 1) × Fin (N + 1))) :
    finrank k (deformationExt1 M (intervalDirectSum (k := k) L))
      = (L.map (fun b => finrank k (deformationExt1 M (intervalModule b.1 b.2)))).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    refine finrank_deformationExt1_eq_zero_of_cochain1 _ _ ?_
    rw [finrank_cochain1]; exact Finset.sum_eq_zero (fun i _ => by simp [foldDim])
  | cons p ps ih =>
    have hstep : finrank k (deformationExt1 M (intervalDirectSum (k := k) (p :: ps)))
        = finrank k (deformationExt1 M (intervalModule p.1 p.2))
          + finrank k (deformationExt1 M (intervalDirectSum (k := k) ps)) :=
      finrank_deformationExt1_dirSum_right M (intervalModule p.1 p.2) (intervalDirectSum ps)
    rw [hstep, ih, List.map_cons, List.sum_cons]
theorem finrank_deformationExt1_intervalDirectSum {N : ℕ}
    (L L' : List (Fin (N + 1) × Fin (N + 1))) :
    finrank k (deformationExt1 (intervalDirectSum (k := k) L) (intervalDirectSum (k := k) L'))
      = (L.map (fun a => (L'.map (fun b =>
          finrank k (deformationExt1 (intervalModule (k := k) a.1 a.2)
            (intervalModule b.1 b.2)))).sum)).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    refine finrank_deformationExt1_eq_zero_of_cochain1 _ _ ?_
    rw [finrank_cochain1]; exact Finset.sum_eq_zero (fun i _ => by simp [foldDim])
  | cons p ps ih =>
    have hstep : finrank k (deformationExt1 (intervalDirectSum (k := k) (p :: ps))
        (intervalDirectSum (k := k) L'))
        = finrank k (deformationExt1 (intervalModule (k := k) p.1 p.2)
            (intervalDirectSum (k := k) L'))
          + finrank k (deformationExt1 (intervalDirectSum (k := k) ps)
            (intervalDirectSum (k := k) L')) :=
      finrank_deformationExt1_dirSum_left (intervalModule p.1 p.2) (intervalDirectSum ps)
        (intervalDirectSum L')
    rw [hstep, ih,
      finrank_deformationExt1_intervalDirectSum_right (intervalModule (k := k) p.1 p.2) L',
      List.map_cons, List.sum_cons]

/-! ### The multiplicity form `Σ m_{i-1,j-1} m_{uv}` (Le Halleur–Rimányi Cor 3.5)

Regrouping the ordered list double-sum by interval multiplicities (`multiplicityArray`, the count of
each endpoint pair in `L`) turns the headline into the paper's quadratic form: a sum over the
endpoint
grid of `m(p)·m(q)·1[i<u≤j+1≤v]`. The `Ext¹` indicator `extIndicator` is the `ℤ` form of
`finrank_deformationExt1_interval`; `multiplicityArray_eq_count` is the bridge `m = list count`. -/

theorem multiplicityArray_eq_count (L : List (Fin (N + 1) × Fin (N + 1)))
    (a : Fin (N + 1) × Fin (N + 1)) :
    multiplicityArray L (a.1 : ℤ) (a.2 : ℤ) = (L.count a : ℤ) := by
  unfold multiplicityArray
  induction L with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    have hiff : ((a.1 : ℤ) = (p.1 : ℤ) ∧ (a.2 : ℤ) = (p.2 : ℤ)) ↔ a = p := by
      refine ⟨fun ⟨h1,h2⟩ => Prod.ext (Fin.ext (Nat.cast_injective (R := ℤ) h1))
        (Fin.ext (Nat.cast_injective (R := ℤ) h2)), ?_⟩
      rintro rfl; exact ⟨rfl, rfl⟩
    by_cases hap : a = p
    · rw [if_pos (hiff.mpr hap)]; simp only [hap, beq_self_eq_true, if_true]; push_cast; ring
    · rw [if_neg (fun hc => hap (hiff.mp hc)),
        if_neg (by simp only [beq_iff_eq]; exact fun hc => hap hc.symm)]; push_cast; ring
theorem list_sum_to_grid (L : List (Fin (N + 1) × Fin (N + 1)))
    (h : (Fin (N + 1) × Fin (N + 1)) → ℤ) :
    (L.map h).sum
      = ∑ q : Fin (N + 1) × Fin (N + 1), multiplicityArray L (q.1 : ℤ) (q.2 : ℤ) * h q := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    symm
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [show multiplicityArray ([] : List (Fin (N + 1) × Fin (N + 1))) (q.1 : ℤ) (q.2 : ℤ) = 0
      from by
      simp [multiplicityArray], zero_mul]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih]
    rw [show (multiplicityArray (p :: ps) : ℤ → ℤ → ℤ)
        = fun a b => singleDelta p.1 p.2 a b + multiplicityArray ps a b
        from multiplicityArray_cons p ps]
    have hsplit : ∑ q : Fin (N + 1) × Fin (N + 1),
        (singleDelta p.1 p.2 (q.1 : ℤ) (q.2 : ℤ) + multiplicityArray ps (q.1 : ℤ) (q.2 : ℤ)) * h q
        = (∑ q : Fin (N + 1) × Fin (N + 1), singleDelta p.1 p.2 (q.1 : ℤ) (q.2 : ℤ) * h q)
          + ∑ q : Fin (N + 1) × Fin (N + 1), multiplicityArray ps (q.1 : ℤ) (q.2 : ℤ) * h q := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun q _ => by ring)
    rw [hsplit]
    congr 1
    -- Σ singleDelta_p ↑q.1 ↑q.2 * h q = h p
    rw [Finset.sum_eq_single p]
    · rw [show singleDelta p.1 p.2 (p.1 : ℤ) (p.2 : ℤ) = 1 from by simp [singleDelta], one_mul]
    · intro q _ hqp
      rw [show singleDelta p.1 p.2 (q.1 : ℤ) (q.2 : ℤ) = 0 from by
        simp only [singleDelta]; rw [if_neg]; rintro ⟨h1, h2⟩
        exact hqp (Prod.ext (Fin.ext (Nat.cast_injective (R := ℤ) h1))
          (Fin.ext (Nat.cast_injective (R := ℤ) h2))), zero_mul]
    · intro hp; exact absurd (Finset.mem_univ p) hp

theorem list_double_sum_to_grid (L : List (Fin (N + 1) × Fin (N + 1)))
    (g : (Fin (N + 1) × Fin (N + 1)) → (Fin (N + 1) × Fin (N + 1)) → ℤ) :
    ((L.map (fun a => (L.map (fun b => g a b)).sum)).sum)
      = ∑ p : Fin (N + 1) × Fin (N + 1), ∑ q : Fin (N + 1) × Fin (N + 1),
          multiplicityArray L (p.1 : ℤ) (p.2 : ℤ) * multiplicityArray L (q.1 : ℤ) (q.2 : ℤ)
            * g p q := by
  rw [list_sum_to_grid L (fun a => (L.map (fun b => g a b)).sum)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [list_sum_to_grid L (fun b => g p b), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_); ring

def extIndicator (p q : Fin (N + 1) × Fin (N + 1)) : ℤ :=
  if (p.1:ℕ) < q.1 ∧ (q.1:ℕ) ≤ (p.2:ℕ) + 1 ∧ (p.2:ℕ) + 1 ≤ q.2 then 1 else 0

theorem finrank_deformationExt1_interval_cast (a b : Fin (N + 1) × Fin (N + 1)) :
    ((finrank k (deformationExt1 (intervalModule (k := k) a.1 a.2)
        (intervalModule b.1 b.2)) : ℕ) : ℤ)
      = extIndicator a b := by
  rw [finrank_deformationExt1_interval, extIndicator]; split <;> simp

theorem cast_listSum (L : List (Fin (N + 1) × Fin (N + 1))) (f : (Fin (N + 1) × Fin (N + 1)) → ℕ) :
    ((L.map f).sum : ℤ) = (L.map (fun a => (f a : ℤ))).sum := by
  induction L with
  | nil => simp
  | cons a as ih => simp [ih]

theorem finrank_deformationExt1_intervalDirectSum_mult (L : List (Fin (N + 1) × Fin (N + 1))) :
    (finrank k (deformationExt1 (intervalDirectSum (k := k) L) (intervalDirectSum (k := k) L)) : ℤ)
      = ∑ p : Fin (N + 1) × Fin (N + 1), ∑ q : Fin (N + 1) × Fin (N + 1),
          multiplicityArray L (p.1 : ℤ) (p.2 : ℤ) * multiplicityArray L (q.1 : ℤ) (q.2 : ℤ)
            * extIndicator p q := by
  rw [← list_double_sum_to_grid L extIndicator, finrank_deformationExt1_intervalDirectSum,
    cast_listSum]
  refine congrArg List.sum (List.map_congr_left (fun a _ => ?_))
  rw [cast_listSum]
  refine congrArg List.sum (List.map_congr_left (fun b _ => ?_))
  exact finrank_deformationExt1_interval_cast a b

section MultSum
open Finset

/-! ### Reindexing the grid m-form to the paper's restricted region

The grid m-form (`finrank_deformationExt1_intervalDirectSum_mult`) sums over the full endpoint grid
with
the `Ext¹` indicator. Le Halleur–Rimányi Cor 3.5 states it as a sum over the restricted region
`1≤i≤u≤j≤v≤N` of `m_{i-1,j-1} m_{uv}`. The two are equal by reindexing each `Fin (N + 1)` coordinate
to an
integer `Icc 0 N`, absorbing the indicator into the summation bounds, and the shift
`(a,b,u,v) ↦ (a+1,u,b+1,v)` (one `Finset.sum_nbij'` on the flattened product). -/

theorem extIndicator_eq (p q : Fin (N + 1) × Fin (N + 1)) :
    extIndicator p q
      = (if (p.1 : ℤ) < (q.1 : ℤ) ∧ (q.1 : ℤ) ≤ (p.2 : ℤ) + 1 ∧ (p.2 : ℤ) + 1 ≤ (q.2 : ℤ)
          then 1 else 0) := by
  unfold extIndicator
  congr 1
  simp only [eq_iff_iff]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨?_,?_,?_⟩ <;>
    first
    | (exact_mod_cast h1) | (exact_mod_cast h2) | (exact_mod_cast h3)
theorem sum_fin_eq_sum_Icc (f : ℤ → ℤ) :
    ∑ x : Fin (N + 1), f (x : ℤ) = ∑ a ∈ Finset.Icc (0 : ℤ) N, f a := by
  refine Finset.sum_nbij' (i := fun (x : Fin (N + 1)) => (x : ℤ))
    (j := fun (a : ℤ) => (⟨min a.toNat N, by omega⟩ : Fin (N + 1))) ?_ ?_ ?_ ?_ ?_
  · intro x _; rw [Finset.mem_Icc]
    refine ⟨by positivity, ?_⟩
    have : ((x : ℕ):ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp x.isLt
    simpa using this
  · intro a _; exact Finset.mem_univ _
  · intro x _; apply Fin.ext
    have hx : (x : ℤ).toNat = (x : ℕ) := by simp
    rw [Fin.val_mk, hx]; have := x.isLt; omega
  · intro a ha; rw [Finset.mem_Icc] at ha
    have h2 : a.toNat ≤ N := by omega
    simp [Int.toNat_of_nonneg ha.1, Nat.min_eq_left h2]
  · intro x _; rfl

-- 4-fold Fin form
theorem grid_eq_fin4 (m : ℤ → ℤ → ℤ) :
    (∑ p : Fin (N + 1) × Fin (N + 1), ∑ q : Fin (N + 1) × Fin (N + 1),
        m (p.1 : ℤ) (p.2 : ℤ) * m (q.1 : ℤ) (q.2 : ℤ) * extIndicator p q)
      = ∑ a : Fin (N + 1), ∑ b : Fin (N + 1), ∑ u : Fin (N + 1), ∑ v : Fin (N + 1),
          m (a : ℤ) (b : ℤ) * m (u : ℤ) (v : ℤ)
          * (if (a : ℤ) < (u : ℤ) ∧ (u : ℤ) ≤ (b : ℤ) + 1 ∧ (b : ℤ) + 1 ≤ (v : ℤ)
              then 1 else 0) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [extIndicator_eq]

theorem fin4_eq_Icc4 (m : ℤ → ℤ → ℤ) :
    (∑ a : Fin (N + 1), ∑ b : Fin (N + 1), ∑ u : Fin (N + 1), ∑ v : Fin (N + 1),
        m (a : ℤ) (b : ℤ) * m (u : ℤ) (v : ℤ)
        * (if (a : ℤ) < (u : ℤ) ∧ (u : ℤ) ≤ (b : ℤ) + 1 ∧ (b : ℤ) + 1 ≤ (v : ℤ) then 1 else 0))
      = ∑ a ∈ Finset.Icc (0 : ℤ) N, ∑ b ∈ Finset.Icc (0 : ℤ) N, ∑ u ∈ Finset.Icc (0 : ℤ) N,
          ∑ v ∈ Finset.Icc (0 : ℤ) N,
          m a b * m u v * (if a < u ∧ u ≤ b+1 ∧ b+1 ≤ v then 1 else 0) := by
  rw [sum_fin_eq_sum_Icc (fun a => ∑ b : Fin (N + 1), ∑ u : Fin (N + 1), ∑ v : Fin (N + 1),
    m a (b : ℤ) * m (u : ℤ) (v : ℤ)
        * (if a < (u : ℤ) ∧ (u : ℤ) ≤ (b : ℤ) + 1 ∧ (b : ℤ) + 1 ≤ (v : ℤ) then 1 else 0))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_fin_eq_sum_Icc (fun b => ∑ u : Fin (N + 1), ∑ v : Fin (N + 1),
    m a b * m (u : ℤ) (v : ℤ) * (if a < (u : ℤ) ∧ (u : ℤ) ≤ b+1 ∧ b+1 ≤ (v : ℤ) then 1 else 0))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [sum_fin_eq_sum_Icc (fun u => ∑ v : Fin (N + 1),
    m a b * m u (v : ℤ) * (if a < u ∧ u ≤ b+1 ∧ b+1 ≤ (v : ℤ) then 1 else 0))]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [sum_fin_eq_sum_Icc (fun v => m a b * m u v * (if a < u ∧ u ≤ b+1 ∧ b+1 ≤ v then 1 else 0))]
theorem Icc_lo_absorb (lo : ℤ) (hlo : 0 ≤ lo) (f : ℤ → ℤ) :
    ∑ x ∈ Finset.Icc lo (N : ℤ), f x
      = ∑ x ∈ Finset.Icc (0 : ℤ) N, f x * (if lo ≤ x then 1 else 0) := by
  rw [show (∑ x ∈ Finset.Icc (0 : ℤ) N, f x * (if lo ≤ x then 1 else 0))
      = ∑ x ∈ Finset.Icc (0 : ℤ) N, (if lo ≤ x then f x else 0) from by
    refine Finset.sum_congr rfl (fun x _ => ?_); split <;> simp]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun x _ => rfl)
  ext x; rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]; omega

theorem region_to_Icc4 (m : ℤ → ℤ → ℤ) :
    (∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
        ∑ v ∈ Finset.Icc j (N : ℤ), m (i-1) (j-1) * m u v)
      = ∑ i ∈ Finset.Icc (0 : ℤ) N, ∑ u ∈ Finset.Icc (0 : ℤ) N, ∑ j ∈ Finset.Icc (0 : ℤ) N,
          ∑ v ∈ Finset.Icc (0 : ℤ) N,
          m (i-1) (j-1) * m u v * (if 1 ≤ i ∧ i ≤ u ∧ u ≤ j ∧ j ≤ v then 1 else 0) := by
  rw [Icc_lo_absorb 1 (by norm_num)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  rw [Finset.sum_mul, Icc_lo_absorb i (by omega)]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [Finset.mem_Icc] at hu
  rw [Finset.sum_mul, Finset.sum_mul, Icc_lo_absorb u (by omega)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Icc_lo_absorb j (by omega)]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  by_cases h : 1 ≤ i ∧ i ≤ u ∧ u ≤ j ∧ j ≤ v
  · obtain ⟨h1,h2,h3,h4⟩ := h
    rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos ⟨h1,h2,h3,h4⟩]; ring
  · rw [if_neg h]
    rcases not_and_or.mp h with h1 | h
    · rw [if_neg h1]; ring
    rcases not_and_or.mp h with h2 | h
    · rw [if_neg h2]; ring
    rcases not_and_or.mp h with h3 | h4
    · rw [if_neg h3]; ring
    · rw [if_neg h4]; ring
-- flatten my Icc4 (a,b,u,v ite) to a product sum
theorem myIcc4_flat (m : ℤ → ℤ → ℤ) :
    (∑ a ∈ Finset.Icc (0 : ℤ) N, ∑ b ∈ Finset.Icc (0 : ℤ) N, ∑ u ∈ Finset.Icc (0 : ℤ) N,
        ∑ v ∈ Finset.Icc (0 : ℤ) N,
        m a b * m u v * (if a < u ∧ u ≤ b+1 ∧ b+1 ≤ v then 1 else 0))
      = ∑ t ∈ (Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N ×ˢ
          Finset.Icc (0 : ℤ) N),
          m t.1 t.2.1 * m t.2.2.1 t.2.2.2
          * (if t.1 < t.2.2.1 ∧ t.2.2.1 ≤ t.2.1+1 ∧ t.2.1+1 ≤ t.2.2.2 then 1 else 0) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_product]

theorem regionIcc4_flat (m : ℤ → ℤ → ℤ) :
    (∑ i ∈ Finset.Icc (0 : ℤ) N, ∑ u ∈ Finset.Icc (0 : ℤ) N, ∑ j ∈ Finset.Icc (0 : ℤ) N,
        ∑ v ∈ Finset.Icc (0 : ℤ) N,
        m (i-1) (j-1) * m u v * (if 1 ≤ i ∧ i ≤ u ∧ u ≤ j ∧ j ≤ v then 1 else 0))
      = ∑ t ∈ (Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N ×ˢ
          Finset.Icc (0 : ℤ) N),
          m (t.1-1) (t.2.2.1-1) * m t.2.1 t.2.2.2
          * (if 1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.2.2.2 then 1 else 0) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_product]
theorem two_Icc4_bridge (m : ℤ → ℤ → ℤ) :
    (∑ t ∈ (Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N ×ˢ
        Finset.Icc (0 : ℤ) N),
        m t.1 t.2.1 * m t.2.2.1 t.2.2.2
        * (if t.1 < t.2.2.1 ∧ t.2.2.1 ≤ t.2.1+1 ∧ t.2.1+1 ≤ t.2.2.2 then 1 else 0))
      = ∑ t ∈ (Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N ×ˢ Finset.Icc (0 : ℤ) N ×ˢ
          Finset.Icc (0 : ℤ) N),
          m (t.1-1) (t.2.2.1-1) * m t.2.1 t.2.2.2
          * (if 1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.2.2.2 then 1 else 0) := by
  rw [show (fun t : (ℤ×ℤ×ℤ×ℤ) => m t.1 t.2.1 * m t.2.2.1 t.2.2.2
        * (if t.1 < t.2.2.1 ∧ t.2.2.1 ≤ t.2.1+1 ∧ t.2.1+1 ≤ t.2.2.2 then (1 : ℤ) else 0))
      = (fun t => if t.1 < t.2.2.1 ∧ t.2.2.1 ≤ t.2.1+1 ∧ t.2.1+1 ≤ t.2.2.2
          then m t.1 t.2.1 * m t.2.2.1 t.2.2.2 else 0)
      from by funext t; split <;> simp]
  rw [show (fun t : (ℤ×ℤ×ℤ×ℤ) => m (t.1-1) (t.2.2.1-1) * m t.2.1 t.2.2.2
        * (if 1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.2.2.2 then (1 : ℤ) else 0))
      = (fun t => if 1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.2.2.2
          then m (t.1-1) (t.2.2.1-1) * m t.2.1 t.2.2.2 else 0)
      from by funext t; split <;> simp]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (i := fun t => (t.1+1, t.2.2.1, t.2.1+1, t.2.2.2))
    (j := fun t => (t.1-1, t.2.2.1-1, t.2.1, t.2.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, u, v⟩ ht
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
    obtain ⟨⟨⟨ha0,haN⟩, ⟨hb0,hbN⟩, ⟨hu0,huN⟩, hv0, hvN⟩, hP1, hP2, hP3⟩ := ht
    refine ⟨⟨⟨?_,?_⟩, ⟨?_,?_⟩, ⟨?_,?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨i, u, j, v⟩ ht
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
    obtain ⟨⟨⟨hi0,hiN⟩, ⟨hu0,huN⟩, ⟨hj0,hjN⟩, hv0, hvN⟩, hQ1, hQ2, hQ3, hQ4⟩ := ht
    refine ⟨⟨⟨?_,?_⟩, ⟨?_,?_⟩, ⟨?_,?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨a, b, u, v⟩ _; simp
  · rintro ⟨i, u, j, v⟩ _; simp
  · rintro ⟨a, b, u, v⟩ _; simp

/-- **Headline, multiplicity form (Le Halleur–Rimányi Cor 3.5, verbatim).** For
`M = intervalDirectSum
L` over a field, the algebraic `Ext¹` codimension is the paper's quadratic form
`Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}`, `m = multiplicityArray L`. The later `(C, θ)` optimisation
minimises this form. Chains the grid m-form through the Fin→ℤ-Icc reindex and the
`(a,b,u,v) ↦ (a+1,u,b+1,v)` shift to the restricted summation region. -/
theorem finrank_deformationExt1_self_eq_multSum (L : List (Fin (N + 1) × Fin (N + 1))) :
    (finrank k (deformationExt1 (intervalDirectSum (k := k) L) (intervalDirectSum (k := k) L)) : ℤ)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ),
          multiplicityArray L (i-1) (j-1) * multiplicityArray L u v := by
  rw [finrank_deformationExt1_intervalDirectSum_mult, grid_eq_fin4, fin4_eq_Icc4,
    region_to_Icc4, regionIcc4_flat, myIcc4_flat, two_Icc4_bridge]

end MultSum


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

/-- The `Hom` indicator on `M_{01} → M_{12}` over `Fin 3`/`ℚ`: `finrank Hom = 0` (the target bar
`[1,2]` starts strictly after the source's left end `0`, so no morphism). -/
example : finrank ℚ (Hom (intervalModule (k := ℚ) (0 : Fin 3) 1) (intervalModule 1 2)) = 0 := by
  rw [finrank_Hom_interval]; decide

/-- The `Ext¹` indicator on `M_{01} → M_{12}` over `Fin 3`/`ℚ`: `finrank deformationExt1 = 1`
(`1[0<1≤2≤2]`). -/
example :
    finrank ℚ (deformationExt1 (intervalModule (k := ℚ) (0 : Fin 3) 1) (intervalModule 1 2))
      = 1 := by
  rw [finrank_deformationExt1_interval]; decide

/-! ### The `(2,2,2)` headline witnesses (Le Halleur–Rimányi Ex 4.3, `C = 3`; the `{A=0}` locus)

`N = 2` (`Fin 3`), over `ℚ`. Two Kostant partitions of the dimension vector `(2,2,2)`:
the `(1,1)`-orbit `M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}` has `dim Ext¹(M,M) = 3` (the codimension `C`);
the zero-product locus `{A = 0} = M_{00}² ⊕ M_{12}²` has `dim Ext¹(M,M) = 4`. Both computed from the
list expansion + the `Ext¹` indicator + `decide`. -/

/-- **`(2,2,2)` `(1,1)`-orbit:** `dim Ext¹(M,M) = 3` for `M = M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}`. -/
example :
    finrank ℚ (deformationExt1
        (intervalDirectSum (k := ℚ) [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)])
        (intervalDirectSum [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)])) = 3 := by
  rw [finrank_deformationExt1_intervalDirectSum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    finrank_deformationExt1_interval]
  decide

/-- **`(2,2,2)` zero-product locus:** `dim Ext¹(M,M) = 4` for `M = M_{00}² ⊕ M_{12}²`
(`{A = 0}`). -/
example :
    finrank ℚ (deformationExt1
        (intervalDirectSum (k := ℚ) [((0 : Fin 3), (0 : Fin 3)), (0, 0), (1, 2), (1, 2)])
        (intervalDirectSum [((0 : Fin 3), (0 : Fin 3)), (0, 0), (1, 2), (1, 2)])) = 4 := by
  rw [finrank_deformationExt1_intervalDirectSum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    finrank_deformationExt1_interval]
  decide

/-- **`(2,2,2)` `(1,1)`-orbit via the multiplicity grid form:** `Σ_{p,q} m(p)·m(q)·1[i<u≤j+1≤v] = 3`
(`finrank_deformationExt1_intervalDirectSum_mult`). -/
example :
    (finrank ℚ (deformationExt1
        (intervalDirectSum (k := ℚ) [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)])
        (intervalDirectSum [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)])) : ℤ) = 3 := by
  rw [finrank_deformationExt1_intervalDirectSum_mult]; decide

/-- **`(2,2,2)` `(1,1)`-orbit via the verbatim Cor 3.5 region form:**
`Σ_{1≤i≤u≤j≤v≤2} m_{i-1,j-1} m_{uv} = 3` (`finrank_deformationExt1_self_eq_multSum`). -/
example :
    (finrank ℚ (deformationExt1
        (intervalDirectSum (k := ℚ) [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)])
        (intervalDirectSum [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)])) : ℤ) = 3 := by
  rw [finrank_deformationExt1_self_eq_multSum]; decide

end Witness

end DLNFibre.Core

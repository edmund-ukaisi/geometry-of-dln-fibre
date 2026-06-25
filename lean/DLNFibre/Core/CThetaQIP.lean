import DLNFibre.Core.CTheta
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# `DLNFibre.Core.CThetaQIP` — the QIP (Thm 6.1), EASY half (substitution `≤`)

Lehalleur–Rimányi 2024 Theorem 6.1 reduces the combinatorial codimension `C` (and `θ`) of the
zero-product locus to a **quadratic integer program** in `N` non-negative integers. For a
**weakly-increasing** dimension vector `d` (`Monotone d`):

$$
\min_{\substack{e \in \mathbb N^N \\ \sum_i e_i = d_0}}\
  G_{d}(e), \qquad
G_{d}(e) = \sum_{1 \le j \le i \le N} e_i\,(e_j + d_j - d_{j-1}).
$$

**This file proves only the EASY direction `cCodim d 0 ≤ qipMin d`** — the *substitution*. Each
feasible `e` is mapped to a Kostant partition `mOfE d e` (the **horizontal-lace** module of `e`),
whose `codimForm` is *exactly* `G_d(e)` (`codimForm_mOfE`); as `mOfE d e ∈ kostantPartitions d 0`,
`cCodim` is `≤ G_d(e)` for every feasible `e`, hence `≤ qipMin` (`cCodim_le_qipMin`).

**Name = content (the load-bearing caveat).** This is the `≤` half only. The reverse
`cCodim ≥ qipMin` (every minimiser is in the `e`-image — Lemma 6.4/6.7, the *horizontal-lace
representability* of top-dimensional orbits) is the HARD converse and is **NOT** proved here;
`cCodim = qipMin` (Thm 6.1 proper) is therefore **NOT** asserted in this file. The `e`-image is a
*proper* subset of all Kostant partitions (3 of 6 for `(2,2,2)`), so the substitution alone gives
only `≤`. The hard converse `cCodim ≥ qipMin`, hence the equality `cCodim = qipMin`, is **PROVED**
in `Core.CThetaQIPConverse` (`cCodim_eq_qipMin`).

The **per-orbit** geometric reading (`codimForm` = geometric codimension of the orbit closure `Ō_M`)
is PROVED in `Core.CThetaGeometric` via the discharged Voigt lemma
`Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim` (`[IsAlgClosed k] [CharZero k]`);
the **aggregate** reading (`cCodim` = geometric codim of the whole *closed* rank-`≤ r` locus `Σ̄^r`)
is also formalised — `codim Σ̄^r = cCodim d r` (`Core.SigmaCodim`), via the orbit stratification
(`Core.SigmaStratification`). `cCodim`/`qipMin` here are min-values of ℤ-quadratic forms over finite
sets.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## The QIP objective `G_d` and feasible set

`Gqip d e` is the paper's `G_d(e) = ∑_{1 ≤ j ≤ i ≤ N} e_i (e_j + d_j − d_{j-1})`, `i, j : Fin N`
encoding the paper's `1..N` (`e i` is paper `e_{i+1}`; `d_j − d_{j-1}` for paper `j ∈ 1..N` is
`d j.succ − d j.castSucc`). The feasible set is `Finset.finAntidiagonal N (d 0)`, i.e.
`{e : Fin N → ℕ | ∑ e = d_0}`. -/

/-- The QIP objective `G_d(e) = ∑_{1 ≤ j ≤ i ≤ N} e_i (e_j + d_j − d_{j-1})` over `ℤ`
(`i, j : Fin N` encode paper `1..N`). -/
def Gqip (d : Fin (N + 1) → ℕ) (e : Fin N → ℕ) : ℤ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if j ≤ i then (e i : ℤ) * ((e j : ℤ) + (d j.succ : ℤ) - (d j.castSucc : ℤ)) else 0

/-- The QIP feasible set: `e : Fin N → ℕ` with `∑ i, e i = d 0` (the antidiagonal). -/
def qipFeasible (d : Fin (N + 1) → ℕ) : Finset (Fin N → ℕ) :=
  Finset.finAntidiagonal N (d 0)

/-! ## The substitution `mOfE` — the horizontal-lace module of `e`

`mOfE d e` is the multiplicity array of the lace diagram with `e_i` copies of the horizontal
intervals `[0, i-1]`, `[i, N]`, plus `(d_i − d_{i-1})` copies of `[i, N]` — i.e. the interval module
`⊕_i M_{0,i-1}^{e_i} ⊕_i M_{i,N}^{e_i + d_i − d_{i-1}}`. Closed-form entry at `(a, b)`:

* `a = 0, (b : ℕ) < N`:   `e_{b+1}` (`= e ⟨b⟩`);
* `(a : ℕ) ≥ 1, b = last`: `e_a + (d_a − d_{a-1})` (`= e ⟨a-1⟩ + (d a − d (a-1))`);
* else `0`.

The corner `(0, last)` is `0` (the `a = 0` branch needs `b < N`). For `Monotone d` it is a valid
Kostant partition of `d`. -/

/-- The substitution `e ↦ mOfE d e`: the horizontal-lace multiplicity array of `e` (see section
docstring for the closed-form entry). Corner `(0, last)` is `0`. -/
def mOfE (d : Fin (N + 1) → ℕ) (e : Fin N → ℕ) : Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦
    (if h : p.1 = 0 ∧ (p.2 : ℕ) < N then e ⟨p.2, h.2⟩ else 0)
    + (if h : 1 ≤ (p.1 : ℕ) ∧ p.2 = Fin.last N then
        e ⟨(p.1 : ℕ) - 1, by omega⟩ + (d p.1 - d ⟨(p.1 : ℕ) - 1, by omega⟩) else 0)

/-! ### Pointwise values of `mOfE`

The two `dite` branches are mutually exclusive (`p.1 = 0` vs `p.1 ≥ 1`), so each entry is read by at
most one. These value lemmas pin the entry at the four index patterns that the proofs read. -/

/-- `mOfE` on a low column `(0, b)` with `b < N`: the first branch, value `e_{b+1}`. -/
theorem mOfE_zero_lt {d : Fin (N + 1) → ℕ} {e : Fin N → ℕ} {b : Fin (N + 1)} (hb : (b : ℕ) < N) :
    mOfE d e (0, b) = e ⟨b, hb⟩ := by
  unfold mOfE
  rw [dif_pos ⟨rfl, hb⟩, dif_neg (by simp), add_zero]

/-- `mOfE` on the top row `(a, last)` with `a ≥ 1`: the second branch,
value `e_{a-1} + (d_a − d_{a-1})`. -/
theorem mOfE_top {d : Fin (N + 1) → ℕ} {e : Fin N → ℕ} {a : Fin (N + 1)} (ha : 1 ≤ (a : ℕ)) :
    mOfE d e (a, Fin.last N) =
      e ⟨(a : ℕ) - 1, by omega⟩ + (d a - d ⟨(a : ℕ) - 1, by omega⟩) := by
  unfold mOfE
  rw [dif_neg (by simp), dif_pos ⟨ha, rfl⟩, zero_add]

/-- The corner `(0, last)` of `mOfE` is `0`. -/
theorem mOfE_corner {d : Fin (N + 1) → ℕ} {e : Fin N → ℕ} :
    mOfE d e (0, Fin.last N) = 0 := by
  unfold mOfE
  rw [dif_neg (by simp [Fin.last]), dif_neg (by simp), add_zero]

/-- `mOfE` vanishes off the support triangle `p.1 ≤ p.2`. -/
theorem mOfE_eq_zero_of_not_le {d : Fin (N + 1) → ℕ} {e : Fin N → ℕ}
    {p : Fin (N + 1) × Fin (N + 1)} (hp : ¬ p.1 ≤ p.2) :
    mOfE d e p = 0 := by
  unfold mOfE
  have h1 : (p.1 : ℕ) ≠ 0 := by
    intro h0; exact hp (by rw [show p.1 = 0 from Fin.ext h0]; exact Fin.zero_le _)
  rw [dif_neg (by rintro ⟨h, -⟩; exact h1 (by rw [h]; rfl))]
  rw [dif_neg (by rintro ⟨-, h⟩; rw [h] at hp; exact hp (Fin.le_last _)), add_zero]

/-! ## The exact identity `codimForm (mOfE d e) = G_d(e)`

`codimForm` reads `M = extendℤ (mOfE d e)` at `M (i-1) (j-1)` and `M u v`, over
`1 ≤ i ≤ u ≤ j ≤ v ≤ N`. On that range both reads land in the `extendℤ` box. The first is nonzero
at `i = 1` (`mOfE`'s low-column branch, value `e_{j-1}`); the second only at `v = N` (the top-row
branch, value `e_{u-1} + d_u − d_{u-1}`). Collapsing `i` to `1` and `v` to `N` leaves a double sum
`∑_{1 ≤ u ≤ j ≤ N} e_{j-1} (e_{u-1} + d_u − d_{u-1})`, which reindexes to `G_d(e)`. -/

/-- `extendℤ` of any array in the box `0 ≤ a ≤ b ≤ N`: drops the `dite` guard. -/
theorem extendℤ_in_box (m : Fin (N + 1) × Fin (N + 1) → ℕ) {a b : ℤ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (N : ℤ)) :
    extendℤ m a b = (m (⟨a.toNat, by omega⟩, ⟨b.toNat, by omega⟩) : ℤ) := by
  unfold extendℤ; rw [dif_pos ⟨ha, hab, hb⟩]

/-- **First read pattern.** On `1 ≤ i`, `i ≤ j`, `j ≤ N`, `M (i-1) (j-1)` is `e_{j-1}` when `i = 1`,
else `0` (`mOfE`'s low-column branch; the second index `j-1 < N` never hits the top). -/
theorem extendℤ_mOfE_first {d : Fin (N + 1) → ℕ} {e : Fin N → ℕ} {i j : ℤ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ (N : ℤ)) :
    extendℤ (mOfE d e) (i - 1) (j - 1)
      = if i = 1 then (e ⟨(j - 1).toNat, by omega⟩ : ℤ) else 0 := by
  rw [extendℤ_in_box _ (by omega) (by omega) (by omega)]
  by_cases hi1 : i = 1
  · subst hi1
    rw [if_pos rfl]
    rw [show (⟨((1 : ℤ) - 1).toNat, by omega⟩ : Fin (N + 1)) = 0 from Fin.ext (by simp)]
    have hjb : ((⟨(j - 1).toNat, by omega⟩ : Fin (N + 1)) : ℕ) < N := by simp; omega
    rw [mOfE_zero_lt hjb]
  · rw [if_neg hi1]
    -- first index `(i-1).toNat ≥ 1`, second `(j-1).toNat < N`: both `mOfE` branches off
    have h1 : (⟨(i - 1).toNat, by omega⟩ : Fin (N + 1)) ≠ 0 := by
      rw [Fin.ne_iff_vne]; simp; omega
    have h2 : (⟨(j - 1).toNat, by omega⟩ : Fin (N + 1)) ≠ Fin.last N := by
      rw [Fin.ne_iff_vne, Fin.val_last]; simp; omega
    unfold mOfE
    rw [dif_neg (by rintro ⟨h, -⟩; exact h1 h), dif_neg (by rintro ⟨-, h⟩; exact h2 h)]
    norm_num

/-- **Second read pattern.** On `1 ≤ u`, `u ≤ v`, `v ≤ N`, the factor `M u v` is
`e_{u-1} + (d_u − d_{u-1})` when `v = N` and `0` otherwise (`mOfE`'s top-row branch; the first index
`u ≥ 1` never hits the low column). -/
theorem extendℤ_mOfE_second {d : Fin (N + 1) → ℕ} {e : Fin N → ℕ} {u v : ℤ}
    (hd : Monotone d) (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ (N : ℤ)) :
    extendℤ (mOfE d e) u v
      = if v = (N : ℤ) then
          (e ⟨(u - 1).toNat, by omega⟩ : ℤ)
            + ((d ⟨u.toNat, by omega⟩ : ℤ) - (d ⟨(u - 1).toNat, by omega⟩ : ℤ))
        else 0 := by
  rw [extendℤ_in_box _ (by omega) (by omega) (by omega)]
  have hu1 : 1 ≤ ((⟨u.toNat, by omega⟩ : Fin (N + 1)) : ℕ) := by simp; omega
  by_cases hvN : v = (N : ℤ)
  · subst hvN
    rw [if_pos rfl]
    rw [show (⟨(N : ℤ).toNat, by omega⟩ : Fin (N + 1)) = Fin.last N from
      Fin.ext (by simp [Fin.val_last])]
    rw [mOfE_top hu1]
    -- `mOfE_top` returns `e_{u'-1} + (d_{u'} − d_{u'-1})` with `u' = ⟨u.toNat⟩`; match indices.
    have hsubF : (⟨((⟨u.toNat, by omega⟩ : Fin (N + 1)) : ℕ) - 1, by omega⟩ : Fin N)
        = ⟨(u - 1).toNat, by omega⟩ := Fin.ext (by simp)
    have hsub1 : (⟨((⟨u.toNat, by omega⟩ : Fin (N + 1)) : ℕ) - 1, by omega⟩ : Fin (N + 1))
        = ⟨(u - 1).toNat, by omega⟩ := Fin.ext (by simp)
    have hle : (d ⟨(u - 1).toNat, by omega⟩ : ℕ) ≤ d ⟨u.toNat, by omega⟩ :=
      hd (by rw [Fin.le_def]; simp)
    rw [hsubF, hsub1, Nat.cast_add, Nat.cast_sub hle]
  · rw [if_neg hvN]
    have h1 : (⟨u.toNat, by omega⟩ : Fin (N + 1)) ≠ 0 := by
      rw [Fin.ne_iff_vne]; simp; omega
    have h2 : (⟨v.toNat, by omega⟩ : Fin (N + 1)) ≠ Fin.last N := by
      rw [Fin.ne_iff_vne, Fin.val_last]; simp; omega
    unfold mOfE
    rw [dif_neg (by rintro ⟨h, -⟩; exact h1 h), dif_neg (by rintro ⟨-, h⟩; exact h2 h)]
    norm_num

/-- Reindex a `ℤ`-`Icc 1 N` sum to a `Fin N` sum via `a ↦ (a : ℤ) + 1`. -/
theorem sum_Icc_one_eq_fin {A : Type*} [AddCommMonoid A] (F : ℤ → A) :
    (∑ a : Fin N, F ((a : ℕ) + 1 : ℤ)) = ∑ u ∈ Finset.Icc (1 : ℤ) N, F u := by
  apply Finset.sum_bij (fun (a : Fin N) _ ↦ ((a : ℕ) + 1 : ℤ))
  · intro a _; simp only [Finset.mem_Icc]; exact ⟨by omega, by have := a.isLt; omega⟩
  · intro a _ b _ h; exact Fin.ext (by omega)
  · intro u hu; simp only [Finset.mem_Icc] at hu
    exact ⟨⟨(u - 1).toNat, by omega⟩, Finset.mem_univ _, by simp; omega⟩
  · intro a _; rfl

/-- **The substitution identity (Thm 6.1, substitution direction).** For weakly-increasing `d`, the
`codimForm` of the horizontal-lace module `mOfE d e` equals the QIP objective `G_d(e)` exactly. -/
theorem codimForm_mOfE (d : Fin (N + 1) → ℕ) (hd : Monotone d) (e : Fin N → ℕ) :
    codimForm N (extendℤ (mOfE d e)) = Gqip d e := by
  set M := extendℤ (mOfE d e) with hM
  -- `N = 0`: both sides are empty sums, `= 0`.
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp only [Gqip, codimForm, hM]; rfl
  unfold codimForm
  -- Stage 1: collapse the inner `v`-sum to its `v = N` term (the only nonzero one).
  have hvcollapse : ∀ i ∈ Finset.Icc (1 : ℤ) N, ∀ u ∈ Finset.Icc i (N : ℤ),
      ∀ j ∈ Finset.Icc u (N : ℤ),
      (∑ v ∈ Finset.Icc j (N : ℤ), M (i - 1) (j - 1) * M u v)
        = M (i - 1) (j - 1) * M u (N : ℤ) := by
    intro i hi u hu j hj
    simp only [Finset.mem_Icc] at hi hu hj
    rw [← Finset.mul_sum]
    congr 1
    refine Finset.sum_eq_single_of_mem (N : ℤ) (by simp only [Finset.mem_Icc]; omega) ?_
    intro v hv hvN; simp only [Finset.mem_Icc] at hv
    rw [hM, extendℤ_mOfE_second hd (by omega) (by omega) (by omega), if_neg hvN]
  rw [Finset.sum_congr rfl (fun i hi ↦ Finset.sum_congr rfl (fun u hu ↦
    Finset.sum_congr rfl (fun j hj ↦ hvcollapse i hi u hu j hj)))]
  -- Stage 2: collapse the outer `i`-sum to `i = 1` (`M (i-1) (j-1) = 0` for `i ≥ 2`).
  rw [Finset.sum_eq_single_of_mem (1 : ℤ) (by simp only [Finset.mem_Icc]; omega)]
  · -- `i = 1`: rewrite the inner `Icc u N` as a filter of `Icc 1 N`, reindex both to `Fin N`.
    -- Inner sum over `Icc u N` (with `u ∈ Icc 1 N`) = filtered sum over `Icc 1 N`.
    have hinner : ∀ u ∈ Finset.Icc (1 : ℤ) N,
        (∑ j ∈ Finset.Icc u (N : ℤ), M ((1 : ℤ) - 1) (j - 1) * M u (N : ℤ))
          = ∑ j ∈ Finset.Icc (1 : ℤ) N, if u ≤ j then M ((1 : ℤ) - 1) (j - 1) * M u (N : ℤ)
              else 0 := by
      intro u hu; simp only [Finset.mem_Icc] at hu
      rw [← Finset.sum_filter]
      congr 1
      ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [Finset.sum_congr rfl hinner]
    -- Reindex both sums `Icc 1 N → Fin N` (`u ↦ (a:ℤ)+1`, `j ↦ (b:ℤ)+1`).
    rw [← sum_Icc_one_eq_fin]
    simp only [← sum_Icc_one_eq_fin (N := N)]
    -- Now evaluate the factors and match `Gqip`. My outer index `a = u-1`, inner `b = j-1`;
    -- `Gqip` has outer `e_{i'}` and inner `e_{j'}` with `j' ≤ i'`, so swap the sum order.
    rw [Gqip, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ ↦ Finset.sum_congr rfl (fun a _ ↦ ?_))
    -- LHS summand (after `sum_comm`, outer `b`, inner `a`): the `Icc`-reindexed factors.
    -- `M ((1:ℤ)-1) ((b+1)-1) = e_b`; `M (a+1) N = e_a + (d_{a+1} − d_a)`; cond `a+1 ≤ b+1`.
    have hb : ((b : ℕ) + 1 : ℤ) ≤ (N : ℤ) := by have := b.isLt; omega
    have ha : (1 : ℤ) ≤ ((a : ℕ) + 1 : ℤ) := by omega
    have haN : ((a : ℕ) + 1 : ℤ) ≤ (N : ℤ) := by have := a.isLt; omega
    rw [hM]
    rw [extendℤ_mOfE_first (i := 1) (j := ((b : ℕ) + 1 : ℤ)) (by omega) (by omega) (by omega),
      if_pos rfl,
      extendℤ_mOfE_second (u := ((a : ℕ) + 1 : ℤ)) (v := (N : ℤ)) hd ha haN le_rfl,
      if_pos rfl]
    -- Identify the `Fin N` indices and the condition.
    by_cases hcond : (a : ℕ) ≤ (b : ℕ)
    · rw [if_pos (by omega), if_pos (Fin.le_def.mpr hcond)]
      have hbi : (⟨(((b : ℕ) + 1 : ℤ) - 1).toNat, by omega⟩ : Fin N) = b := Fin.ext (by simp)
      have hai : (⟨(((a : ℕ) + 1 : ℤ) - 1).toNat, by omega⟩ : Fin N) = a := Fin.ext (by simp)
      have hasucc : (⟨((a : ℕ) + 1 : ℤ).toNat, by omega⟩ : Fin (N + 1)) = a.succ :=
        Fin.ext (by simp [Fin.val_succ])
      have hacast : (⟨(((a : ℕ) + 1 : ℤ) - 1).toNat, by omega⟩ : Fin (N + 1)) = a.castSucc :=
        Fin.ext (by simp)
      rw [hbi, hai, hasucc, hacast]; ring
    · rw [if_neg (by omega), if_neg (by rw [Fin.le_def]; omega)]
  · -- `i ≠ 1`, `i ∈ Icc 1 N` ⟹ `i ≥ 2`: every summand has `M (i-1) (j-1) = 0`.
    intro i hi hi1; simp only [Finset.mem_Icc] at hi
    refine Finset.sum_eq_zero (fun u hu ↦ Finset.sum_eq_zero (fun j hj ↦ ?_))
    simp only [Finset.mem_Icc] at hu hj
    rw [hM, extendℤ_mOfE_first (by omega) (by omega) (by omega), if_neg (by omega), zero_mul]

/-- **The Kostant constraint for `mOfE`.** At every vertex `k`, the filtered sum of `mOfE d e` over
intervals containing `k` is `d k` — given `∑ e = d 0` and `d` monotone. This telescopes:
`∑_{k ≤ b < N} e_{b+1} + ∑_{1 ≤ a ≤ k} (e_a + d_a − d_{a-1})
= (∑ e − ∑_{a ≤ k} e_a) + ∑_{a ≤ k} e_a + (d_k − d_0) = d_0 + d_k − d_0 = d_k`. -/
theorem mOfE_kostantAt (d : Fin (N + 1) → ℕ) (hd : Monotone d) {e : Fin N → ℕ}
    (he : ∑ i, e i = d 0) (k : Fin (N + 1)) :
    kostantAt d (mOfE d e) k := by
  rw [kostantAt, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
  -- Row `x = 0`: reindex `y` to `Fin N` (the `y = last` term is the corner, `= 0`).
  have hrow0 : (∑ y, if ((0 : Fin (N + 1)), y).1 ≤ k ∧ k ≤ ((0 : Fin (N + 1)), y).2 then
        mOfE d e (0, y) else 0)
      = ∑ j : Fin N, if k ≤ j.castSucc then e j else 0 := by
    rw [Fin.sum_univ_castSucc]
    have hlast : (if ((0 : Fin (N + 1)), Fin.last N).1 ≤ k ∧ k ≤ ((0 : Fin (N + 1)), Fin.last N).2
        then mOfE d e (0, Fin.last N) else 0) = 0 := by
      rw [mOfE_corner]; simp
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    have hjN : ((j.castSucc : Fin (N + 1)) : ℕ) < N := by
      rw [Fin.val_castSucc]; exact j.isLt
    have hje : (⟨(j.castSucc : Fin (N + 1)), hjN⟩ : Fin N) = j := Fin.ext (by rw [Fin.val_castSucc])
    rw [mOfE_zero_lt hjN, hje]
    simp only [Fin.zero_le, true_and]
  -- Rows `x ≥ 1` (indexed by `x.succ`): only the `y = last` term survives.
  have hrows : (∑ x : Fin N, ∑ y, if (x.succ, y).1 ≤ k ∧ k ≤ (x.succ, y).2 then
        mOfE d e (x.succ, y) else 0)
      = ∑ x : Fin N, if x.succ ≤ k then e x + (d x.succ - d x.castSucc) else 0 := by
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [Finset.sum_eq_single (Fin.last N)]
    · have hx1 : 1 ≤ ((x.succ : Fin (N + 1)) : ℕ) := by rw [Fin.val_succ]; omega
      rw [mOfE_top hx1]
      have hkl : k ≤ Fin.last N := Fin.le_last _
      simp only [hkl, and_true]
      by_cases hxk : x.succ ≤ k
      · rw [if_pos hxk, if_pos hxk]
        congr 2 <;> exact Fin.ext (by rw [Fin.val_succ])
      · rw [if_neg hxk, if_neg hxk]
    · intro y _ hy
      by_cases hcond : x.succ ≤ k ∧ k ≤ y
      · rw [if_pos hcond]
        have hyN : (y : ℕ) < N := by
          rcases Fin.eq_castSucc_or_eq_last y with ⟨j, rfl⟩ | rfl
          · rw [Fin.val_castSucc]; exact j.isLt
          · exact absurd rfl hy
        -- `mOfE (x.succ, y)` with `x.succ ≥ 1` and `y ≠ last`: both branches off → 0
        unfold mOfE
        have hb1 : ¬ ((x.succ, y).1 = 0 ∧ ((x.succ, y).2 : ℕ) < N) := by
          rintro ⟨h, -⟩; simp [Fin.ext_iff, Fin.val_succ] at h
        have hb2 : ¬ (1 ≤ ((x.succ, y).1 : ℕ) ∧ (x.succ, y).2 = Fin.last N) := by
          rintro ⟨-, h⟩; exact hy h
        rw [dif_neg hb1, dif_neg hb2, add_zero]
      · rw [if_neg hcond]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hrow0, hrows]
  -- Conditions: `k ≤ j.castSucc ↔ (k:ℕ) ≤ j`; `x.succ ≤ k ↔ (x:ℕ) < k`. They partition `Fin N`.
  have hcastSucc : ∀ x : Fin N, (k ≤ x.castSucc) ↔ (k : ℕ) ≤ (x : ℕ) := fun x ↦ by
    rw [Fin.le_def, Fin.val_castSucc]
  have hsucc : ∀ x : Fin N, (x.succ ≤ k) ↔ (x : ℕ) < (k : ℕ) := fun x ↦ by
    rw [Fin.le_def, Fin.val_succ]; omega
  -- Split the second `e + ddiff` sum into an `e`-sum and a `ddiff`-sum.
  have hsplit : (∑ x : Fin N, if x.succ ≤ k then e x + (d x.succ - d x.castSucc) else 0)
      = (∑ x : Fin N, if x.succ ≤ k then e x else 0)
        + ∑ x : Fin N, if x.succ ≤ k then d x.succ - d x.castSucc else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ ↦ by split_ifs <;> simp)
  -- The two `e`-sums recombine to `∑ e = d 0` (conditions partition `Fin N`).
  have hesum : (∑ j : Fin N, if k ≤ j.castSucc then e j else 0)
      + (∑ x : Fin N, if x.succ ≤ k then e x else 0) = d 0 := by
    rw [← Finset.sum_add_distrib, ← he]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [if_congr (hcastSucc x) rfl rfl, if_congr (hsucc x) rfl rfl]
    by_cases h : (k : ℕ) ≤ (x : ℕ)
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  -- The ddiff-sum telescopes to `d k − d 0` (monotone `d`).
  have hdiff : (∑ x : Fin N, if x.succ ≤ k then d x.succ - d x.castSucc else 0) = d k - d 0 := by
    set f : ℕ → ℕ := fun i ↦ d ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ with hf
    have hfmono : Monotone f := fun a b hab ↦ hd (by
      simp only [Fin.le_def]; exact min_le_min hab le_rfl)
    have hfk : f (k : ℕ) = d k := by
      simp only [hf, Nat.min_eq_left (Nat.le_of_lt_succ k.isLt)]
    have hf0 : f 0 = d 0 := by simp [hf]
    -- Rewrite the `Fin N` summand in terms of `f`, then reindex to `range N` and telescope.
    have hsummand : ∀ x : Fin N, (if x.succ ≤ k then d x.succ - d x.castSucc else 0)
        = (if (x : ℕ) < (k : ℕ) then f ((x : ℕ) + 1) - f (x : ℕ) else 0) := by
      intro x
      have hxN : (x : ℕ) < N := x.isLt
      have e1 : f ((x : ℕ) + 1) = d x.succ := by
        simp only [hf, Nat.min_eq_left (by omega : (x : ℕ) + 1 ≤ N)]
        exact congrArg d (Fin.ext (by simp [Fin.val_succ]))
      have e2 : f (x : ℕ) = d x.castSucc := by
        simp only [hf, Nat.min_eq_left (by omega : (x : ℕ) ≤ N)]
        exact congrArg d (Fin.ext (by simp))
      rw [e1, e2]
      exact if_congr (hsucc x) rfl rfl
    rw [Finset.sum_congr rfl (fun x _ ↦ hsummand x)]
    rw [show (∑ x : Fin N, if (x : ℕ) < (k : ℕ) then f ((x : ℕ) + 1) - f (x : ℕ) else 0)
        = ∑ i ∈ Finset.range N, if i < (k : ℕ) then f (i + 1) - f i else 0 from
      Fin.sum_univ_eq_sum_range (fun i ↦ if i < (k : ℕ) then f (i + 1) - f i else 0) N]
    -- On `range N`, the `if i < k` cut leaves `range k` (since `k ≤ N`), which telescopes.
    have hkN : (k : ℕ) ≤ N := Nat.le_of_lt_succ k.isLt
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilter : (Finset.range N).filter (fun i ↦ i < (k : ℕ)) = Finset.range (k : ℕ) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilter, Finset.sum_range_tsub hfmono (k : ℕ), hfk, hf0]
  have hd0k : d 0 ≤ d k := hd (Fin.zero_le k)
  rw [hsplit, ← add_assoc, hesum, hdiff]
  omega

/-- **`mOfE d e` is a Kostant partition with corner 0.** For weakly-increasing `d` and feasible `e`
(`∑ e = d 0`), the horizontal-lace module lands in `kostantPartitions d 0`. -/
theorem mOfE_mem (d : Fin (N + 1) → ℕ) (hd : Monotone d) {e : Fin N → ℕ}
    (he : ∑ i, e i = d 0) :
    mOfE d e ∈ kostantPartitions d 0 := by
  rw [mem_kostantPartitions]
  have hsupp : ∀ p, ¬ p.1 ≤ p.2 → mOfE d e p = 0 := fun p hp ↦ mOfE_eq_zero_of_not_le hp
  exact ⟨bound_of_kostant hsupp (mOfE_kostantAt d hd he), hsupp,
    mOfE_kostantAt d hd he, mOfE_corner⟩

/-! ## The QIP minimum and the easy `≤` -/

/-- The QIP minimum value `min_{e feasible} G_d(e)` (`Finset.inf'`; needs the feasible set
nonempty). -/
noncomputable def qipMin (d : Fin (N + 1) → ℕ) (hne : (qipFeasible d).Nonempty) : ℤ :=
  (qipFeasible d).inf' hne (Gqip d)

/-- **Easy `≤` for a single feasible `e`.** `cCodim d 0 ≤ G_d(e)`: `mOfE d e` is a Kostant partition
whose `codimForm` is `G_d(e)`, so the minimum `cCodim` is below it. -/
theorem cCodim_le_Gqip (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) {e : Fin N → ℕ} (he : ∑ i, e i = d 0) :
    cCodim d 0 h ≤ Gqip d e := by
  rw [← codimForm_mOfE d hd e]
  exact Finset.inf'_le (s := kostantPartitions d 0) (fun m ↦ codimForm N (extendℤ m))
    (mOfE_mem d hd he)

/-- **The easy half of the QIP (Thm 6.1, `≤`).** `cCodim d 0 ≤ qipMin d`: the combinatorial
codimension is below the QIP minimum, via the substitution `mOfE`. The reverse `≥` (Lemma 6.4) is
NOT proved here — see module docstring. -/
theorem cCodim_le_qipMin (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    cCodim d 0 h ≤ qipMin d hne := by
  refine Finset.le_inf' hne _ (fun e he ↦ ?_)
  have hfeas : ∑ i, e i = d 0 := by
    simpa [qipFeasible, Finset.mem_finAntidiagonal] using he
  exact cCodim_le_Gqip d hd h hfeas

/-! ## Witness — `(2,2,2)`, `r = 0` (Lehalleur–Rimányi Ex 4.3 / Ex 6.2 form)

`d = (2,2,2)` is weakly increasing. `G_d` over the feasible set
`{e : Fin 2 → ℕ | e₀+e₁ = 2} = {(0,2),(1,1),(2,0)}` takes values `{4,3,4}`, so `qipMin = 3`, at
`(1,1)` — the horizontal-lace module `mOfE d222 (1,1)` is the unique `(1,1)`-orbit `mMin` of
`Core.CTheta`. The easy `≤` gives `cCodim d222 0 = 3 ≤ qipMin = 3` (tight here; tightness in general
is the unproved converse). -/

section Witness

/-- `(2,2,2)` is weakly increasing — the QIP hypothesis. -/
theorem d222_monotone : Monotone d222 := by decide

/-- The QIP feasible set for `(2,2,2)` is nonempty (`e = (1,1)` is feasible). -/
theorem qipFeasible_d222_nonempty : (qipFeasible d222).Nonempty := by
  refine ⟨![1, 1], ?_⟩; decide

/-- **`(2,2,2)`: `G_d(1,1) = 3`.** The QIP objective at the minimiser `e = (1,1)` (Ex 6.2). -/
theorem Gqip_d222_eq_three : Gqip d222 ![1, 1] = 3 := by decide

/-- **`(2,2,2)`: `mOfE d222 (1,1)` is the `(1,1)`-orbit `mMin`.** The horizontal-lace module of the
QIP minimiser reproduces the unique top component of `Core.CTheta`. -/
theorem mOfE_d222_eq_mMin : mOfE d222 ![1, 1] = mMin := by decide

/-- **`(2,2,2)`: `qipMin = 3`.** The QIP minimum over the feasible set, matching `cCodim d222 0 = 3`
(`Core.CTheta.cCodim_d222_zero`). Axiom-clean kernel `decide`. -/
theorem qipMin_d222_eq_three : qipMin d222 qipFeasible_d222_nonempty = 3 := by
  decide +kernel

/-- **`(2,2,2)`: the easy `≤` is tight.** `cCodim d222 0 = 3 ≤ qipMin d222 = 3`, both `= 3`. The
inequality `cCodim_le_qipMin` here holds with equality; equality in general is the unproved converse
(Lemma 6.4). -/
theorem cCodim_le_qipMin_d222 :
    cCodim d222 0 kostantPartitions_d222_nonempty ≤ qipMin d222 qipFeasible_d222_nonempty :=
  cCodim_le_qipMin d222 d222_monotone _ _

end Witness

end DLNFibre.Core

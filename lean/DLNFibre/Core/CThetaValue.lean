import DLNFibre.Core.CThetaDropM

/-!
# `DLNFibre.Core.CThetaValue` — the explicit closed form for `C` (and `θ`)

Lehalleur–Rimányi 2024 Theorem 7.10 (`r = 0`) gives the combinatorial codimension `C` of the
zero-product locus in closed form. This module assembles it from the two upstream tides:

* the **drop-to-`m`** reduction (`Core.CThetaDropM`): a `Φ`-minimiser is supported on the first `m`
  coordinates, `m = qipM d`, with `S = qipS d = ∑_{i=0}^m d_i`;
* the **integer-square optimum** (`Core.CThetaExplicit.isLeast_sumSq`) and the **square-completion**
  bridge (`Core.CThetaExplicit.two_Gqipℤ_sub_sq`).

For weakly-increasing `d` (`Monotone d`, `d 0 ≥ 1`), with `m = qipM d`, `S = qipS d`,

$$ a := \Bigl\lfloor \tfrac{S}{m} + \tfrac12 \Bigr\rfloor = \frac{2S + m}{2m}\ (\text{integer div}),
   \qquad \delta := S - m\,a, $$

the closed form is

$$ C = \tfrac12\Bigl( d_0^2 - \sum_{i=1}^m (d_i - d_0)^2 + m(a - d_0)^2 + 2(a - d_0)\,\delta
       + |\delta| \Bigr), \qquad \theta = \binom{m}{|\delta|}. $$

The route: on the `m`-face, substituting `w_i = e_i + d_{i+1}` (so `e_i - s_i = w_i - d_0`,
`∑ w = S`) and `t_i = w_i - a` (so `∑ t = δ`) turns `min Φ` into `min ∑ t_i²` subject to `∑ t = δ`,
which is `|δ|` by `isLeast_sumSq` (valid as `|δ| ≤ m`); reassembling and crossing the
square-completion bridge gives `C`.

**Scope (name = content).** This file lands the **closed-form objects** (`qipRound`, `qipDelta`,
`cValue`, `cTheta`), the foundational bound **`abs_qipDelta_le_m : |δ| ≤ m`**, the closed form for
`C` (**`qipMin_eq_cValue : qipMin d = cValue d`**, the `m`-face assembly), and the closed form for
`θ` (**`qipNumMinimisers_eq_cTheta`**: the number of `Gqip`-minimisers is `C(m, |δ|)`, via the
minimiser ↔ `|δ|`-subset-of-`qipLow` bijection — the integer-square equality characterization
`sumSq_eq_abs_characterization` pins minimisers to `{0, sgn δ}`-valued `t`-vectors). The proofs need
`Monotone d`. Nothing here asserts the geometric reading (`C = codim Σ⁰`), which rides on the
deferred Voigt hypothesis as upstream; and `cValue`/`cTheta` read `d` through its order-sensitive
prefix data (`qipM`/`qipS`/`qipRound`/`qipDelta`), so **permutation invariance of `(C, θ)`
(Cor 5.10) is NOT a corollary of this file** — see the thread retrospective for the obstruction.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## The rounding centre `a`, the residue `δ`, and the closed form -/

/-- The integer rounding centre `a := ⌊S/m + ½⌋ = (2S + m) / (2m)` (`Int` division), `S = qipS d`,
`m = qipM d`. -/
noncomputable def qipRound (d : Fin (N + 1) → ℕ) : ℤ :=
  (2 * qipS d + (qipM d : ℤ)) / (2 * (qipM d : ℤ))

/-- The rounding residue `δ := S − m·a`. -/
noncomputable def qipDelta (d : Fin (N + 1) → ℕ) : ℤ :=
  qipS d - (qipM d : ℤ) * qipRound d

/-- The closed-form combinatorial codimension
`C = ½(d_0² − ∑_{i=1}^m (d_i − d_0)² + m(a − d_0)² + 2(a − d_0)δ + |δ|)`. -/
noncomputable def cValue (d : Fin (N + 1) → ℕ) : ℤ :=
  ((d 0 : ℤ) ^ 2
    - ∑ i ∈ Finset.Icc 1 (qipM d),
        ((d ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ) - (d 0 : ℤ)) ^ 2
    + (qipM d : ℤ) * (qipRound d - (d 0 : ℤ)) ^ 2
    + 2 * (qipRound d - (d 0 : ℤ)) * qipDelta d
    + |qipDelta d|) / 2

/-- The closed-form number of top-dimensional components `θ = C(m, |δ|)`. -/
noncomputable def cTheta (d : Fin (N + 1) → ℕ) : ℕ := Nat.choose (qipM d) (qipDelta d).natAbs

/-! ## The foundational bound `|δ| ≤ m` -/

/-- **`|δ| ≤ m`** (`m ≥ 1`): the residue fits the slot count, so `isLeast_sumSq` applies.
From `a = (2S + m) / (2m)`: `2m·a ≤ 2S + m < 2m·a + 2m`, hence `−m ≤ 2(S − m·a) − m < m`, i.e.
`−m ≤ 2δ − m`, `2δ ≤ m`… cross-multiplied to `|δ| ≤ m`. -/
theorem abs_qipDelta_le_m (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) : |qipDelta d| ≤ (qipM d : ℤ) := by
  have hm1 : 1 ≤ qipM d := qipM_ge_one d hN
  have hmpos : (0 : ℤ) < 2 * (qipM d : ℤ) := by positivity
  set S := qipS d
  set m := (qipM d : ℤ) with hmdef
  -- `a = (2S + m) / (2m)`; let `r` be the residue: `2m·a + r = 2S + m`, `0 ≤ r < 2m`.
  have hdm := Int.mul_ediv_add_emod (2 * S + m) (2 * m)
  have hr0 : 0 ≤ (2 * S + m) % (2 * m) := Int.emod_nonneg _ (by positivity)
  have hrlt : (2 * S + m) % (2 * m) < 2 * m := Int.emod_lt_of_pos _ hmpos
  have hround : qipRound d = (2 * S + m) / (2 * m) := rfl
  have hdelta : qipDelta d = S - m * qipRound d := rfl
  rw [abs_le]
  rw [hdelta, hround]
  have hm0 : (0 : ℤ) ≤ m := by positivity
  constructor <;> nlinarith [hdm, hr0, hrlt, hm0, hm1]

/-! ## Within-prefix bound and the in-face nonnegativity inequalities

The witness on the `m`-face is `e_i = a + t_i − d_{i+1}` with `t_i ∈ {0, ±1}`. Nonnegativity needs
`d_i ≤ a` (when `δ ≥ 0`) and the stronger `d_i ≤ a − 1` (when `δ < 0`, since some `t_i = −1`). Both
descend from the within-prefix bound `m·d_i ≤ S` (`qipPred_qipM`) plus the rounding identity
`2m·a + r = 2S + m`. -/

/-- `A_m = S − m·d_m` (the clamp in `qipA` is inert at `m ≤ N`). -/
theorem qipA_qipM_eq (d : Fin (N + 1) → ℕ) :
    qipA d (qipM d) = qipS d - (qipM d : ℤ) * (d ⟨qipM d, Nat.lt_succ_of_le (qipM_le d)⟩ : ℤ) := by
  unfold qipA qipS
  have : (d ⟨min (qipM d) N, Nat.lt_succ_of_le (min_le_right (qipM d) N)⟩ : ℤ)
      = (d ⟨qipM d, Nat.lt_succ_of_le (qipM_le d)⟩ : ℤ) :=
    congrArg (fun x ↦ (d x : ℤ)) (Fin.ext (by simp [Nat.min_eq_left (qipM_le d)]))
  rw [this]

/-- **Within-prefix bound.** For `i ≤ m`, `m · d_i ≤ S` (from `Pred m` and `d_i ≤ d_m`). -/
theorem qip_within_prefix (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {i : ℕ} (h2 : i ≤ qipM d) :
    (qipM d : ℤ) * (d ⟨i, by have := qipM_le d; omega⟩ : ℤ) ≤ qipS d := by
  have hpred : qipPred d (qipM d) := qipPred_qipM d hN
  rw [qipPred, qipA_qipM_eq] at hpred
  have hmdm : (qipM d : ℤ) * (d ⟨qipM d, Nat.lt_succ_of_le (qipM_le d)⟩ : ℤ) ≤ qipS d := by omega
  have hdi : (d ⟨i, by have := qipM_le d; omega⟩ : ℤ)
      ≤ (d ⟨qipM d, Nat.lt_succ_of_le (qipM_le d)⟩ : ℤ) := by
    have := hd (show (⟨i, by have := qipM_le d; omega⟩ : Fin (N+1))
        ≤ ⟨qipM d, Nat.lt_succ_of_le (qipM_le d)⟩ from by rw [Fin.le_def]; exact h2)
    exact_mod_cast this
  calc (qipM d : ℤ) * (d ⟨i, _⟩ : ℤ)
      ≤ (qipM d : ℤ) * (d ⟨qipM d, _⟩ : ℤ) := mul_le_mul_of_nonneg_left hdi (by positivity)
    _ ≤ qipS d := hmdm

/-- **`Φ` splits across the `m`-prefix and the tail.** For any integer-valued `e`,
`Φ d e = ∑_{i : (i:ℕ) < m} (e_i − s_i)² + ∑_{i : (i:ℕ) ≥ m} (e_i − s_i)²` — the partition of `Fin N`
into the low coordinates (`qipLow`) and the rest. -/
theorem Phi_split_prefix_tail (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ) :
    Phi d e
      = (∑ i ∈ qipLow d, (e i - qipShift d i) ^ 2)
        + ∑ i ∈ (qipLow d)ᶜ, (e i - qipShift d i) ^ 2 := by
  rw [Phi, ← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (e i - qipShift d i) ^ 2)]

/-! ## The `t`-coordinate and its `qipLow`-sum

On the `m`-face, write `e_i − s_i = t_i + (a − d_0)` with `t_i := e_i + d_{i+1} − a`
(`= e_i − s_i − (a − d_0)`, since `s_i = d_0 − d_{i+1}`). Over the low coordinates `qipLow` the
`t`-total is `δ` when `e` is supported on the prefix (`∑_{qipLow} e = d_0`). -/

/-- The `t`-coordinate `t_i := e_i + d_{i+1} − a` (`= (e_i − s_i) − (a − d_0)`), integer-valued. -/
noncomputable def qipT (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ) (i : Fin N) : ℤ :=
  e i + (d i.succ : ℤ) - qipRound d

/-- `e_i − s_i = t_i + (a − d_0)` pointwise (`s = qipShift`, `a = qipRound`). -/
theorem sub_qipShift_eq_qipT_add (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ) (i : Fin N) :
    e i - qipShift d i = qipT d e i + (qipRound d - (d 0 : ℤ)) := by
  rw [qipShift, qipT]; ring

/-- **The `t`-total over `qipLow` is `δ`** when `e` is supported on the `m`-prefix (`e = 0` off
`qipLow`, so `∑_{qipLow} e = ∑ e = d_0`): `∑_{qipLow} t = d_0 + (S − d_0) − m·a = δ`. -/
theorem sum_qipLow_qipT (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ)
    (hsum : (∑ i ∈ qipLow d, e i) = (d 0 : ℤ)) :
    (∑ i ∈ qipLow d, qipT d e i) = qipDelta d := by
  have hcard : (qipLow d).card = qipM d := qipLow_card d
  have hexpand : (∑ i ∈ qipLow d, qipT d e i)
      = (∑ i ∈ qipLow d, e i) + (∑ i ∈ qipLow d, (d i.succ : ℤ))
        - (qipLow d).card • qipRound d := by
    simp only [qipT]
    rw [Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_const]
  rw [hexpand, hsum, sum_qipLow_dsucc d, hcard, nsmul_eq_mul, qipDelta]; ring

/-! ## The Finset integer-square lower bound

A `Finset`-indexed version of `Core.CThetaExplicit.abs_le_sumSq`: any `ℤ`-function summing to `δ`
over a finite set has `∑ t² ≥ |δ|` (same `|a| ≤ a²` + triangle-inequality proof). Used at the
minimiser to bound `∑_{qipLow}(e_i − s_i)²` below. -/

/-- **Finset lower bound.** For `t : ι → ℤ` and a finite `s`, `|∑_{s} t| ≤ ∑_{s} t²`. -/
theorem abs_sum_le_sumSq {ι : Type*} (s : Finset ι) (t : ι → ℤ) :
    |∑ i ∈ s, t i| ≤ ∑ i ∈ s, (t i) ^ 2 := by
  have habs : ∀ a : ℤ, |a| ≤ a ^ 2 := fun a ↦ by
    rw [Int.abs_eq_natAbs]; exact Int.natAbs_le_self_sq a
  calc |∑ i ∈ s, t i| ≤ ∑ i ∈ s, |t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (t i) ^ 2 := Finset.sum_le_sum (fun i _ ↦ habs (t i))

/-! ## The `qipLow` square expansion

`∑_{qipLow}(e_i − s_i)² = ∑_{qipLow} t_i² + 2(a − d_0)(∑_{qipLow} t_i) + m(a − d_0)²` — the
completed square, with `m = #qipLow`. Specialised at `∑_{qipLow} t = δ` it gives the `m`-face value
`∑ t² + 2(a − d_0)δ + m(a − d_0)²`. -/

/-- **The `qipLow` square expansion.** `∑_{qipLow}(e_i − s_i)² = ∑ t² + 2(a − d_0)(∑ t) +
m(a − d_0)²`, with `t = qipT d e`, `m = #qipLow` (`= qipM d`). Pure square completion; no support
hypothesis. -/
theorem sum_qipLow_sub_qipShift_sq (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ) :
    (∑ i ∈ qipLow d, (e i - qipShift d i) ^ 2)
      = (∑ i ∈ qipLow d, (qipT d e i) ^ 2)
        + 2 * (qipRound d - (d 0 : ℤ)) * (∑ i ∈ qipLow d, qipT d e i)
        + (qipM d : ℤ) * (qipRound d - (d 0 : ℤ)) ^ 2 := by
  have hcard : (qipLow d).card = qipM d := qipLow_card d
  set c := qipRound d - (d 0 : ℤ) with hc
  -- Combine the RHS three sums (the `m·c²` constant becomes `∑_{qipLow} c²`) into one sum.
  have hconst : (qipM d : ℤ) * c ^ 2 = ∑ _i ∈ qipLow d, c ^ 2 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  rw [hconst, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [sub_qipShift_eq_qipT_add, hc]; ring

/-! ## The `Gqip`↔`Φ` transfer on the feasible face

On feasible `e` (`∑ e = d_0`), the square-completion bridge collapses to
`2·G_d(e) = Φ(e) + d_0² − ∑ s_i²`, so minimising `G_d` is minimising `Φ`. The `∑ s_i²` (over all
`Fin N`) is `∑_{i=1}^N (d_i − d_0)²`; cValue uses only the prefix `∑_{i=1}^m`, the difference being
the tail `∑_{i ≥ m} s_i²`. -/

/-- **The `G`↔`Φ` transfer (feasible `e`).** `2·G_d(e) = Φ d (↑e) + d_0² − ∑_i s_i²` for feasible
`e` (`∑ e = d_0`), from `two_Gqipℤ_sub_sq` + `Gqipℤ_eq_Gqip`. -/
theorem two_Gqip_eq_Phi_add (d : Fin (N + 1) → ℕ) {e : Fin N → ℕ} (he : ∑ i, e i = d 0) :
    2 * (Gqip d e : ℤ)
      = Phi d (fun i ↦ (e i : ℤ)) + (d 0 : ℤ) ^ 2 - ∑ i, (qipShift d i) ^ 2 := by
  have hbridge := two_Gqipℤ_sub_sq d (fun i ↦ (e i : ℤ))
  rw [Gqipℤ_eq_Gqip] at hbridge
  have hsumcast : (∑ i, (e i : ℤ)) = (d 0 : ℤ) := by
    rw [← he]; push_cast; ring
  rw [hsumcast] at hbridge
  rw [Phi]
  linarith [hbridge]

/-- **The `qipLow` shift-square sum is cValue's prefix sum.** `∑_{i ∈ qipLow}(s_i)² =
∑_{k=1}^m (d_k − d_0)²` — reindex `qipLow` (0-based `i < m`) to `Icc 1 m` via `i ↦ i+1`
(`s_i = d_0 − d_{i+1}`, so `s_i² = (d_{i+1} − d_0)²`). -/
theorem sum_qipLow_qipShift_sq (d : Fin (N + 1) → ℕ) :
    (∑ i ∈ qipLow d, (qipShift d i) ^ 2)
      = ∑ i ∈ Finset.Icc 1 (qipM d),
          ((d ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ) - (d 0 : ℤ)) ^ 2 := by
  have hmN := qipM_le d
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hm0 : qipM d = 0 := Nat.le_zero.mp hmN
    rw [hm0]; simp [qipLow]
  refine Finset.sum_nbij' (fun i ↦ (i : ℕ) + 1)
    (fun k ↦ (⟨min (k - 1) (N - 1), by omega⟩ : Fin N)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [qipLow, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_Icc]; have := i.isLt; omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [qipLow, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro i hi
    simp only [qipLow, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply Fin.ext; have := i.isLt; simp only; omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    show min (k - 1) (N - 1) + 1 = k
    omega
  · intro i hi
    simp only [qipLow, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hi1 : (i : ℕ) + 1 ≤ N := i.isLt
    rw [qipShift]
    rw [show (⟨min ((i : ℕ) + 1) N, Nat.lt_succ_of_le (min_le_right _ N)⟩ : Fin (N + 1))
        = i.succ from Fin.ext (by simp only [Fin.val_succ, Nat.min_eq_left hi1])]
    ring

/-! ## The tail sum and the `Φ` value on the `m`-face

The closed-form numerator equals `Φ`-value minus the tail constant. Define
`tailSq d := ∑_{i ∈ qipLowᶜ} s_i²`. For a prefix-supported `e` (`e = 0` off `qipLow`) with
`∑_{qipLow} e = d_0`, the split + square-expansion + `∑ t = δ` give
`Φ d (↑e) = ∑_{qipLow} t² + 2(a−d_0)δ + m(a−d_0)² + tailSq d`. -/

/-- The fixed tail contribution `∑_{i ∈ qipLowᶜ} s_i²`. -/
noncomputable def tailSq (d : Fin (N + 1) → ℕ) : ℤ :=
  ∑ i ∈ (qipLow d)ᶜ, (qipShift d i) ^ 2

/-- **`Φ` on a prefix-supported feasible `e`.** If `e = 0` off `qipLow` and `∑_{qipLow} e = d_0`,
then `Φ d (↑e) = ∑_{qipLow} (t_i)² + 2(a−d_0)·δ + m(a−d_0)² + tailSq d`. -/
theorem Phi_on_mface (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ)
    (htail : ∀ i ∈ (qipLow d)ᶜ, e i = 0) (hsum : (∑ i ∈ qipLow d, e i) = (d 0 : ℤ)) :
    Phi d e
      = (∑ i ∈ qipLow d, (qipT d e i) ^ 2)
        + 2 * (qipRound d - (d 0 : ℤ)) * qipDelta d
        + (qipM d : ℤ) * (qipRound d - (d 0 : ℤ)) ^ 2
        + tailSq d := by
  rw [Phi_split_prefix_tail, sum_qipLow_sub_qipShift_sq, sum_qipLow_qipT d e hsum]
  -- the tail sum: e i = 0 off qipLow, so (e_i − s_i)² = s_i².
  have htailsum : (∑ i ∈ (qipLow d)ᶜ, (e i - qipShift d i) ^ 2) = tailSq d := by
    rw [tailSq]
    refine Finset.sum_congr rfl (fun i hi ↦ ?_)
    rw [htail i hi]; ring
  rw [htailsum]

/-! ## The rounding bracket and the in-face nonnegativity

From `a = (2S + m)/(2m)` (Int div): `2m·a + r = 2S + m` with `0 ≤ r < 2m`, hence `2δ = r − m`, so
`−m ≤ 2δ ≤ m − 1`. With the within-prefix bound `m·d_i ≤ S` (`qip_within_prefix`) this gives the
branch-sensitive in-face nonnegativity: `d_i ≤ a` when `δ ≥ 0` and `d_i ≤ a − 1` when `δ < 0`
(the witness `t_i ∈ {0, ±1}` needs `a + t_i − d_i ≥ 0`). -/

/-- `2δ = r − m`, `r := (2S + m) % (2m)`, `0 ≤ r < 2m` (the division residue). Hence `−m ≤ 2δ` and
`2δ ≤ m − 1`. -/
theorem two_qipDelta_bounds (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) :
    (-(qipM d : ℤ) ≤ 2 * qipDelta d) ∧ (2 * qipDelta d ≤ (qipM d : ℤ) - 1) := by
  have hmpos : (0 : ℤ) < 2 * (qipM d : ℤ) := by
    have := qipM_ge_one d hN; positivity
  set S := qipS d
  set m := (qipM d : ℤ) with hmdef
  have hdm := Int.mul_ediv_add_emod (2 * S + m) (2 * m)
  have hr0 : 0 ≤ (2 * S + m) % (2 * m) := Int.emod_nonneg _ (by positivity)
  have hrlt : (2 * S + m) % (2 * m) < 2 * m := Int.emod_lt_of_pos _ hmpos
  have hround : qipRound d = (2 * S + m) / (2 * m) := rfl
  have hdelta : qipDelta d = S - m * qipRound d := rfl
  -- `2δ = r − m`: from `2m·q + r = 2S + m` (hdm), `2δ = 2S − 2m·q = r − m`.
  have hkey : 2 * qipDelta d = (2 * S + m) % (2 * m) - m := by
    rw [hdelta, hround]; linarith [hdm]
  rw [hkey]; constructor <;> omega

/-- **In-face nonnegativity, `δ ≥ 0` branch.** For `i ≤ m`, `d_i ≤ a` (so `a + t_i − d_i ≥ −1`; with
`t_i ≥ 0` it is `≥ 0`). -/
theorem qip_d_le_round (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {i : ℕ} (hi : i ≤ qipM d) :
    (d ⟨i, by have := qipM_le d; omega⟩ : ℤ) ≤ qipRound d := by
  have hwp := qip_within_prefix d hd hN hi
  have hm1 : 1 ≤ qipM d := qipM_ge_one d hN
  have hbd := (two_qipDelta_bounds d hN).2
  have hδ : qipDelta d = qipS d - (qipM d : ℤ) * qipRound d := rfl
  have hmpos : (0 : ℤ) < (qipM d : ℤ) := by exact_mod_cast hm1
  nlinarith [hwp, hbd, hδ, hmpos]

/-- **In-face nonnegativity, `δ < 0` branch.** For `i ≤ m` and `δ < 0`, `d_i ≤ a − 1` (so
`a + t_i − d_i ≥ 0` even when `t_i = −1`). -/
theorem qip_d_le_round_sub_one (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {i : ℕ} (hi : i ≤ qipM d) (hneg : qipDelta d < 0) :
    (d ⟨i, by have := qipM_le d; omega⟩ : ℤ) ≤ qipRound d - 1 := by
  have hwp := qip_within_prefix d hd hN hi
  have hm1 : 1 ≤ qipM d := qipM_ge_one d hN
  have hδ : qipDelta d = qipS d - (qipM d : ℤ) * qipRound d := rfl
  have hmpos : (0 : ℤ) < (qipM d : ℤ) := by exact_mod_cast hm1
  nlinarith [hwp, hδ, hmpos, hneg]

/-! ## The explicit `m`-face minimiser witness

The rounded coordinate `r_i := [i < |δ|]·sgn δ` (the `isLeast_sumSq` witness, indexed on the low
coordinates) has `∑_{qipLow} r = δ` and `∑_{qipLow} r² = |δ|` (since `|δ| ≤ m = #qipLow`). The
in-face witness is `eW_i := (a + r_i − d_{i+1}).toNat` on `qipLow`, `0` off it; `eW ≥ 0` is exact by
the branch-sensitive nonnegativity, so `qipT d (↑eW) i = r_i` and `Gqip d eW = cValue d`. -/

/-- The rounded `t`-coordinate `r_i := [i < |δ|]·sgn δ` (`isLeast_sumSq`'s witness, indexed on
`Fin N`; `sgn δ` spelled by an explicit `δ ≥ 0` branch so the `±1` bounds are immediate). -/
noncomputable def qipRoundT (d : Fin (N + 1) → ℕ) (i : Fin N) : ℤ :=
  if (i : ℕ) < (qipDelta d).natAbs then (if 0 ≤ qipDelta d then 1 else -1) else 0

/-- **Count over `qipLow`.** For `c ≤ m`, `∑_{i ∈ qipLow}(if (i:ℕ) < c then x else 0) = c·x` (the
low coordinates with index `< c` are exactly `c` of them, as `c ≤ m ≤ N`). -/
theorem sum_qipLow_indicator (d : Fin (N + 1) → ℕ) {c : ℕ} (hc : c ≤ qipM d) (x : ℤ) :
    (∑ i ∈ qipLow d, if (i : ℕ) < c then x else 0) = (c : ℤ) * x := by
  have hmN := qipM_le d
  -- Extend the sum to all of `Fin N`: off `qipLow` the index is `≥ m ≥ c`, so the `if` is `0`.
  have hext : (∑ i ∈ qipLow d, if (i : ℕ) < c then x else 0)
      = ∑ i : Fin N, if (i : ℕ) < c then x else 0 := by
    rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ if (i : ℕ) < c then x else 0)]
    have hcompl : (∑ i ∈ (qipLow d)ᶜ, if (i : ℕ) < c then x else 0) = 0 := by
      refine Finset.sum_eq_zero (fun i hi ↦ ?_)
      simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hi
      rw [if_neg (by omega)]
    rw [hcompl, add_zero]
  rw [hext]
  -- Reindex `Fin N → range N`, filter to `range c`, count.
  rw [show (∑ i : Fin N, if (i : ℕ) < c then x else 0)
      = ∑ k ∈ Finset.range N, if k < c then x else 0 from
    Fin.sum_univ_eq_sum_range (fun k ↦ if k < c then x else 0) N]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have hfilter : (Finset.range N).filter (fun k ↦ k < c) = Finset.range c := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilter, Finset.card_range, nsmul_eq_mul]

/-- **`∑_{qipLow} r = δ`** — the rounded witness reaches the residue (`|δ| ≤ m`, `δ.natAbs·sgn δ =
δ`). -/
theorem sum_qipLow_qipRoundT (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ qipLow d, qipRoundT d i) = qipDelta d := by
  have hnat : (qipDelta d).natAbs ≤ qipM d := by
    have := abs_qipDelta_le_m d hN; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  simp only [qipRoundT]
  rw [sum_qipLow_indicator d hnat (if 0 ≤ qipDelta d then (1 : ℤ) else -1)]
  -- `δ.natAbs · (±1) = δ`: `+` branch `δ = δ.natAbs`, `−` branch `δ = −δ.natAbs`.
  by_cases hδ : 0 ≤ qipDelta d
  · rw [if_pos hδ, mul_one, Int.natAbs_of_nonneg hδ]
  · rw [if_neg hδ]
    have hle : qipDelta d ≤ 0 := le_of_lt (not_le.mp hδ)
    have : ((qipDelta d).natAbs : ℤ) = -qipDelta d := Int.ofNat_natAbs_of_nonpos hle
    rw [this]; ring

/-- **`∑_{qipLow} r² = |δ|`** — the rounded witness attains the integer-square optimum. -/
theorem sum_qipLow_qipRoundT_sq (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ qipLow d, (qipRoundT d i) ^ 2) = |qipDelta d| := by
  have hnat : (qipDelta d).natAbs ≤ qipM d := by
    have := abs_qipDelta_le_m d hN; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  have hsq : ∀ i : Fin N, (qipRoundT d i) ^ 2
      = if (i : ℕ) < (qipDelta d).natAbs then (1 : ℤ) else 0 := by
    intro i; simp only [qipRoundT]; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hsq i),
    sum_qipLow_indicator d hnat (1 : ℤ), mul_one, Int.abs_eq_natAbs]

/-- The explicit in-face witness `eW_i := (a + r_i − d_{i+1}).toNat` on `qipLow`, `0` off it. -/
noncomputable def qipWitness (d : Fin (N + 1) → ℕ) : Fin N → ℕ :=
  fun i ↦ if (i : ℕ) < qipM d then (qipRound d + qipRoundT d i - (d i.succ : ℤ)).toNat else 0

/-- The witness vanishes off `qipLow`. -/
theorem qipWitness_tail (d : Fin (N + 1) → ℕ) {i : Fin N} (hi : i ∈ (qipLow d)ᶜ) :
    qipWitness d i = 0 := by
  simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
    not_lt] at hi
  have hni : ¬ (i : ℕ) < qipM d := by omega
  simp only [qipWitness, if_neg hni]

/-- **The bracket is nonnegative on `qipLow`**: `0 ≤ a + r_i − d_{i+1}` for `(i:ℕ) < m` (the
branch-sensitive nonnegativity, with `r_i ∈ {0, ±1}`). -/
theorem qipWitness_bracket_nonneg (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {i : Fin N} (hi : (i : ℕ) < qipM d) :
    0 ≤ qipRound d + qipRoundT d i - (d i.succ : ℤ) := by
  have hdsucc : (d i.succ : ℤ) = (d ⟨(i : ℕ) + 1, by have := qipM_le d; omega⟩ : ℤ) :=
    congrArg (fun x ↦ (d x : ℤ)) (Fin.ext (by simp [Fin.val_succ]))
  by_cases hδ : 0 ≤ qipDelta d
  · -- δ ≥ 0: r_i ≥ 0 and d_{i+1} ≤ a.
    have hr : 0 ≤ qipRoundT d i := by
      simp only [qipRoundT]; split_ifs with h <;> simp_all
    have hle : (d ⟨(i : ℕ) + 1, by have := qipM_le d; omega⟩ : ℤ) ≤ qipRound d :=
      qip_d_le_round d hd hN (by omega)
    rw [hdsucc]; linarith
  · -- δ < 0: r_i ≥ −1 and d_{i+1} ≤ a − 1.
    have hδneg : qipDelta d < 0 := not_le.mp hδ
    have hr : -1 ≤ qipRoundT d i := by
      simp only [qipRoundT]; split_ifs with h <;> simp_all
    have hle : (d ⟨(i : ℕ) + 1, by have := qipM_le d; omega⟩ : ℤ) ≤ qipRound d - 1 :=
      qip_d_le_round_sub_one d hd hN (by omega) hδneg
    rw [hdsucc]; linarith

/-- **The witness `t`-coordinate is `r`.** On `qipLow`, `qipT d (↑eW) i = r_i` (the `.toNat` is
exact by `qipWitness_bracket_nonneg`). -/
theorem qipT_qipWitness (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {i : Fin N} (hi : i ∈ qipLow d) :
    qipT d (fun j ↦ (qipWitness d j : ℤ)) i = qipRoundT d i := by
  have hlt : (i : ℕ) < qipM d := by simpa [qipLow, Finset.mem_filter] using hi
  have hbr := qipWitness_bracket_nonneg d hd hN hlt
  have hval : (qipWitness d i : ℤ) = qipRound d + qipRoundT d i - (d i.succ : ℤ) := by
    simp only [qipWitness, if_pos hlt]; rw [Int.toNat_of_nonneg hbr]
  rw [qipT, hval]; ring

/-- **The witness is feasible** (`∑ eW = d_0`): `∑_{qipLow}(a + r_i − d_{i+1}) = m·a + δ − (S − d_0)
= d_0`. -/
theorem qipWitness_feasible (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N) :
    qipWitness d ∈ qipFeasible d := by
  rw [qipFeasible, Finset.mem_finAntidiagonal]
  -- Work over ℤ, then cast back.
  have hsumZ : (∑ i, (qipWitness d i : ℤ)) = (d 0 : ℤ) := by
    rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (qipWitness d i : ℤ))]
    -- tail: 0
    have htail : (∑ i ∈ (qipLow d)ᶜ, (qipWitness d i : ℤ)) = 0 :=
      Finset.sum_eq_zero (fun i hi ↦ by rw [qipWitness_tail d hi]; rfl)
    rw [htail, add_zero]
    -- prefix: ∑ (a + r_i − d_{i+1}) = m·a + δ − (S − d_0)
    have hprefix : ∀ i ∈ qipLow d, (qipWitness d i : ℤ)
        = qipRound d + qipRoundT d i - (d i.succ : ℤ) := by
      intro i hi
      have hlt : (i : ℕ) < qipM d := by simpa [qipLow, Finset.mem_filter] using hi
      simp only [qipWitness, if_pos hlt]
      rw [Int.toNat_of_nonneg (qipWitness_bracket_nonneg d hd hN hlt)]
    rw [Finset.sum_congr rfl hprefix]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, qipLow_card,
      sum_qipLow_qipRoundT d hN, sum_qipLow_dsucc d, nsmul_eq_mul]
    have hδ : qipDelta d = qipS d - (qipM d : ℤ) * qipRound d := rfl
    rw [hδ]; ring
  have : ((∑ i, qipWitness d i : ℕ) : ℤ) = ((d 0 : ℕ) : ℤ) := by push_cast at hsumZ ⊢; rw [hsumZ]
  exact_mod_cast this

/-! ## The shift-square split and the cValue numerator

`∑_all s² = P + tailSq` (`P =` cValue's prefix sum). Together with `Phi_on_mface` and the integer-
square optimum, both the witness value and the minimiser lower bound reduce to the cValue numerator
`d_0² − P + m(a−d_0)² + 2(a−d_0)δ + |δ|`. -/

/-- **Shift-square split.** `∑_i s_i² = (cValue prefix `P`) + tailSq d`. -/
theorem sum_qipShift_sq_split (d : Fin (N + 1) → ℕ) :
    (∑ i, (qipShift d i) ^ 2)
      = (∑ i ∈ Finset.Icc 1 (qipM d),
            ((d ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ) - (d 0 : ℤ)) ^ 2)
        + tailSq d := by
  rw [← sum_qipLow_qipShift_sq, tailSq,
    Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (qipShift d i) ^ 2)]

/-- **The cValue numerator equals `2·G` at the witness.** `d_0² − P + m(a−d_0)² + 2(a−d_0)δ + |δ|
= 2·G_d(eW)`. The `m`-face value (`Phi_on_mface`) crossing the `G`↔`Φ` transfer. -/
theorem cValueNum_eq_two_Gqip_witness (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N) :
    ((d 0 : ℤ) ^ 2
        - ∑ i ∈ Finset.Icc 1 (qipM d),
            ((d ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ) - (d 0 : ℤ)) ^ 2
        + (qipM d : ℤ) * (qipRound d - (d 0 : ℤ)) ^ 2
        + 2 * (qipRound d - (d 0 : ℤ)) * qipDelta d
        + |qipDelta d|)
      = 2 * (Gqip d (qipWitness d) : ℤ) := by
  set eW := qipWitness d with heW
  have hfeasZ : (∑ i, (eW i : ℤ)) = (d 0 : ℤ) := by
    have := qipWitness_feasible d hd hN
    rw [qipFeasible, Finset.mem_finAntidiagonal] at this
    rw [← this]; push_cast; ring
  -- `∑_{qipLow} ↑eW = d_0` (the tail is 0).
  have hsumLow : (∑ i ∈ qipLow d, (eW i : ℤ)) = (d 0 : ℤ) := by
    rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (eW i : ℤ))] at hfeasZ
    have htail : (∑ i ∈ (qipLow d)ᶜ, (eW i : ℤ)) = 0 :=
      Finset.sum_eq_zero (fun i hi ↦ by simp only [heW, qipWitness_tail d hi, Nat.cast_zero])
    rw [htail, add_zero] at hfeasZ; exact hfeasZ
  -- `2·G eW = Φ(↑eW) + d_0² − ∑ s²`.
  have htransfer := two_Gqip_eq_Phi_add d (e := eW)
    (by have := qipWitness_feasible d hd hN
        rwa [qipFeasible, Finset.mem_finAntidiagonal] at this)
  -- `Φ(↑eW) = ∑(qipT ↑eW)² + 2(a−d_0)δ + m(a−d_0)² + tailSq`, and `∑(qipT ↑eW)² = |δ|`.
  have hface := Phi_on_mface d (fun i ↦ (eW i : ℤ))
    (fun i hi ↦ by simp only [heW, qipWitness_tail d hi, Nat.cast_zero]) hsumLow
  have hqT : (∑ i ∈ qipLow d, (qipT d (fun j ↦ (eW j : ℤ)) i) ^ 2) = |qipDelta d| := by
    rw [Finset.sum_congr rfl (fun i hi ↦ by rw [heW, qipT_qipWitness d hd hN hi]),
      sum_qipLow_qipRoundT_sq d hN]
  rw [hqT] at hface
  rw [htransfer, hface, sum_qipShift_sq_split d]
  ring

/-- **The witness attains cValue.** `cValue d = G_d(eW)` (`N ≥ 1`): the numerator is `2·G_d(eW)`
(`cValueNum_eq_two_Gqip_witness`), so the `Int` division by `2` is exact. -/
theorem cValue_eq_Gqip_witness (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N) :
    cValue d = (Gqip d (qipWitness d) : ℤ) := by
  rw [cValue, cValueNum_eq_two_Gqip_witness d hd hN, Int.mul_ediv_cancel_left _ two_ne_zero]

/-! ## The `Φ`↔`Gqip` minimiser correspondence and the lower bound

`2·G_d(e) = Φ d (↑e) + (d_0² − ∑ s²)` for feasible `e`, with the bracket independent of `e`, so
`G_d` and `Φ` share their feasible-face minimisers. A `Φ`-minimiser drops to the `m`-face
(`qip_minimiser_support_le_m`), where `Φ ≥ |δ| + 2(a−d_0)δ + m(a−d_0)² + tailSq` by the integer-
square lower bound, giving `G_d ≥ cValue` at any `G_d`-minimiser. -/

/-- **The `Gqip`-minimiser lower bound.** A feasible `e` that minimises `G_d` (hence `Φ`) has
`cValue d ≤ G_d(e)` — drop-to-`m` + the integer-square lower bound `abs_sum_le_sumSq`. -/
theorem cValue_le_Gqip_of_min (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {e : Fin N → ℕ} (he : e ∈ qipFeasible d)
    (hmin : ∀ e'' ∈ qipFeasible d, Gqip d e ≤ Gqip d e'') :
    cValue d ≤ (Gqip d e : ℤ) := by
  -- `e` is also a `Φ`-minimiser (the `G`↔`Φ` bracket is `e`-independent on the feasible face).
  have hfeasE : ∑ i, e i = d 0 := by
    simpa [qipFeasible, Finset.mem_finAntidiagonal] using he
  have hPhiMin : ∀ e'' ∈ qipFeasible d,
      Phi d (fun i ↦ (e i : ℤ)) ≤ Phi d (fun i ↦ (e'' i : ℤ)) := by
    intro e'' he''
    have hfeasE'' : ∑ i, e'' i = d 0 := by
      simpa [qipFeasible, Finset.mem_finAntidiagonal] using he''
    have h1 := two_Gqip_eq_Phi_add d hfeasE
    have h2 := two_Gqip_eq_Phi_add d hfeasE''
    have := hmin e'' he''
    -- `2·G e ≤ 2·G e''` ⟹ `Φ(↑e) ≤ Φ(↑e'')` (same `d_0² − ∑s²`).
    have hcast : (Gqip d e : ℤ) ≤ (Gqip d e'' : ℤ) := by exact_mod_cast this
    linarith [h1, h2, hcast]
  -- drop-to-`m`: `e i = 0` off `qipLow`.
  have hdrop := qip_minimiser_support_le_m d hd e he hPhiMin
  have htailE : ∀ i ∈ (qipLow d)ᶜ, (fun j ↦ (e j : ℤ)) i = 0 := by
    intro i hi
    simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hi
    simp only [hdrop i hi, Nat.cast_zero]
  have hsumLow : (∑ i ∈ qipLow d, (e i : ℤ)) = (d 0 : ℤ) := by
    have htail : (∑ i ∈ (qipLow d)ᶜ, (e i : ℤ)) = 0 := Finset.sum_eq_zero htailE
    have huniv : (∑ i, (e i : ℤ)) = (d 0 : ℤ) := by rw [← hfeasE]; push_cast; ring
    rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (e i : ℤ)), htail, add_zero] at huniv
    exact huniv
  -- `Φ(↑e) = ∑(qipT ↑e)² + 2(a−d_0)δ + m(a−d_0)² + tailSq`, and `∑(qipT ↑e)² ≥ |δ|`.
  have hface := Phi_on_mface d (fun i ↦ (e i : ℤ)) htailE hsumLow
  have hlb : |qipDelta d| ≤ ∑ i ∈ qipLow d, (qipT d (fun j ↦ (e j : ℤ)) i) ^ 2 := by
    rw [← sum_qipLow_qipT d (fun j ↦ (e j : ℤ)) hsumLow]
    exact abs_sum_le_sumSq (qipLow d) (qipT d (fun j ↦ (e j : ℤ)))
  -- `2·G e = Φ(↑e) + d_0² − ∑s²`, and cValueNum `= 2·G eW`.
  have htransfer := two_Gqip_eq_Phi_add d hfeasE
  have hwit := cValueNum_eq_two_Gqip_witness d hd hN
  rw [cValue_eq_Gqip_witness d hd hN]
  -- assemble: `2·G e ≥ 2·G eW`, hence `G e ≥ G eW = cValue`.
  have hkey : 2 * (Gqip d (qipWitness d) : ℤ) ≤ 2 * (Gqip d e : ℤ) := by
    rw [← hwit, htransfer, hface, sum_qipShift_sq_split d]
    nlinarith [hlb]
  linarith [hkey]

/-- **The closed form for `C` (Thm 7.10, `r = 0`).** For weakly-increasing `d`, the QIP minimum
equals the explicit closed form `qipMin d = cValue d` (`m`-face assembly: drop-to-`m` +
`isLeast_sumSq` + the `Gqip`↔`Φ` square-completion transfer). -/
theorem qipMin_eq_cValue (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (hne : (qipFeasible d).Nonempty) : qipMin d hne = cValue d := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- `N = 0`: feasibility forces `d_0 = 0`; both sides are `0`.
    subst hN0
    obtain ⟨e, he⟩ := hne.exists_mem
    have hd0 : d 0 = 0 := by
      have : ∑ i, e i = d 0 := by simpa [qipFeasible, Finset.mem_finAntidiagonal] using he
      simpa using this.symm
    have hm0 : qipM d = 0 := Nat.le_zero.mp (qipM_le d)
    have hqipMin : qipMin d hne = 0 := by
      rw [qipMin]
      refine le_antisymm ?_ ?_
      · exact (Finset.inf'_le _ he).trans_eq (by simp [Gqip])
      · exact Finset.le_inf' _ _ (fun b _ ↦ by simp [Gqip])
    have hcVal : cValue d = 0 := by
      have hS : qipS d = (d 0 : ℤ) := by simp [qipS, hm0]
      have hround : qipRound d = 0 := by simp [qipRound, hm0]
      have hdelta : qipDelta d = 0 := by simp [qipDelta, hm0, hround, hS, hd0]
      simp [cValue, hm0, hround, hdelta, hd0]
    rw [hqipMin, hcVal]
  -- `N ≥ 1`: antisymmetry of `≤` (witness) and `≥` (minimiser).
  refine le_antisymm ?_ ?_
  · -- `qipMin ≤ cValue`: the witness `eW` is feasible with `G_d(eW) = cValue`.
    rw [qipMin, cValue_eq_Gqip_witness d hd hN]
    exact Finset.inf'_le _ (qipWitness_feasible d hd hN)
  · -- `cValue ≤ qipMin`: extract the `G_d`-minimiser, apply the lower bound.
    obtain ⟨e₀, he₀mem, he₀eq⟩ := Finset.exists_mem_eq_inf' hne (Gqip d)
    rw [qipMin, he₀eq]
    refine cValue_le_Gqip_of_min d hd hN he₀mem (fun e'' he'' ↦ ?_)
    rw [← he₀eq]; exact Finset.inf'_le _ he''

/-! ## Reusable `m`-face minimiser characterization (for the `θ`-count tide)

A feasible `e` minimises `G_d` (equivalently `e` attains `cValue`) iff it is supported on the
`m`-prefix and its `t`-coordinates over `qipLow` form a `{0, sgn δ}`-valued vector summing to `δ`
with exactly `|δ|` nonzero entries. These lemmas expose the two halves the `θ`-count stands on (the
powerset bijection `e ↦ {i < m : t_i ≠ 0}`), without proving the count. -/

/-- **A minimiser is prefix-supported.** A feasible `e` with `G_d(e) = cValue d` has `e_i = 0` for
every 0-based `i ≥ m` — it minimises `G_d`, hence `Φ`, so drop-to-`m` applies. -/
theorem qipMinimiser_support (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    {e : Fin N → ℕ} (he : e ∈ qipFeasible d) (heq : Gqip d e = cValue d) :
    ∀ i : Fin N, qipM d ≤ (i : ℕ) → e i = 0 := by
  have hfeasE : ∑ i, e i = d 0 := by
    simpa [qipFeasible, Finset.mem_finAntidiagonal] using he
  -- `e` minimises `G_d` (`cValue = qipMin`), hence `Φ`.
  have hPhiMin : ∀ e'' ∈ qipFeasible d,
      Phi d (fun i ↦ (e i : ℤ)) ≤ Phi d (fun i ↦ (e'' i : ℤ)) := by
    intro e'' he''
    have hfeasE'' : ∑ i, e'' i = d 0 := by
      simpa [qipFeasible, Finset.mem_finAntidiagonal] using he''
    have h1 := two_Gqip_eq_Phi_add d hfeasE
    have h2 := two_Gqip_eq_Phi_add d hfeasE''
    -- `G e = cValue ≤ G e''` (cValue is the min, `cValue_le_Gqip_of_min` at the witness chain).
    have hle : (Gqip d e : ℤ) ≤ (Gqip d e'' : ℤ) := by
      rw [heq]
      have : qipMin d ⟨e'', he''⟩ ≤ Gqip d e'' := Finset.inf'_le _ he''
      calc cValue d = qipMin d ⟨e'', he''⟩ := (qipMin_eq_cValue d hd ⟨e'', he''⟩).symm
        _ ≤ Gqip d e'' := this
    linarith [h1, h2, hle]
  exact qip_minimiser_support_le_m d hd e he hPhiMin

/-- **A minimiser attains the integer-square optimum.** A feasible `e` with `G_d(e) = cValue d`
(`N ≥ 1`) has `∑_{qipLow}(t_i)² = |δ|` for `t = qipT d (↑e)` — the equality case of the lower bound,
the entry point to the `{0, sgn δ}`-valued characterization (and so the `C(m, |δ|)` count). -/
theorem qipMinimiser_sumSq (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {e : Fin N → ℕ} (he : e ∈ qipFeasible d) (heq : Gqip d e = cValue d) :
    (∑ i ∈ qipLow d, (qipT d (fun j ↦ (e j : ℤ)) i) ^ 2) = |qipDelta d| := by
  have hfeasE : ∑ i, e i = d 0 := by
    simpa [qipFeasible, Finset.mem_finAntidiagonal] using he
  have hdrop := qipMinimiser_support d hd he heq
  have htailE : ∀ i ∈ (qipLow d)ᶜ, (fun j ↦ (e j : ℤ)) i = 0 := by
    intro i hi
    simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hi
    simp only [hdrop i hi, Nat.cast_zero]
  have hsumLow : (∑ i ∈ qipLow d, (e i : ℤ)) = (d 0 : ℤ) := by
    have htail : (∑ i ∈ (qipLow d)ᶜ, (e i : ℤ)) = 0 := Finset.sum_eq_zero htailE
    have huniv : (∑ i, (e i : ℤ)) = (d 0 : ℤ) := by rw [← hfeasE]; push_cast; ring
    rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (e i : ℤ)), htail, add_zero] at huniv
    exact huniv
  -- `∑ t = δ` (prefix support), and the lower bound `|δ| ≤ ∑ t²` holds.
  have hsumT := sum_qipLow_qipT d (fun j ↦ (e j : ℤ)) hsumLow
  have hlb : |qipDelta d| ≤ ∑ i ∈ qipLow d, (qipT d (fun j ↦ (e j : ℤ)) i) ^ 2 := by
    rw [← hsumT]; exact abs_sum_le_sumSq (qipLow d) (qipT d (fun j ↦ (e j : ℤ)))
  -- Equality from `G e = cValue`: `2·G e = Φ(↑e) + d_0² − ∑s²` forces `∑ t² = |δ|`.
  have htransfer := two_Gqip_eq_Phi_add d hfeasE
  have hface := Phi_on_mface d (fun i ↦ (e i : ℤ)) htailE hsumLow
  have hwit := cValueNum_eq_two_Gqip_witness d hd hN
  -- `2·cValue = 2·G eW = cValueNum`; and `2·G e = ∑ t² + (rest)`; with `G e = cValue` ⟹ `∑t²=|δ|`.
  have h2cval : (2 : ℤ) * cValue d = 2 * (Gqip d (qipWitness d) : ℤ) := by
    rw [cValue_eq_Gqip_witness d hd hN]
  have h2ge : 2 * (Gqip d e : ℤ)
      = (∑ i ∈ qipLow d, (qipT d (fun j ↦ (e j : ℤ)) i) ^ 2)
        + 2 * (qipRound d - (d 0 : ℤ)) * qipDelta d
        + (qipM d : ℤ) * (qipRound d - (d 0 : ℤ)) ^ 2
        + tailSq d + (d 0 : ℤ) ^ 2 - ∑ i, (qipShift d i) ^ 2 := by
    rw [htransfer, hface]
  have hgecast : (Gqip d e : ℤ) = cValue d := by exact_mod_cast heq
  -- From `G e = cValue = G eW` and the `Phi` value, the sum-of-squares is `|δ|`.
  rw [hgecast, cValue_eq_Gqip_witness d hd hN, ← hwit, sum_qipShift_sq_split d] at h2ge
  linarith [h2ge]

/-! ## The integer-square equality case (`{0, sgn δ}`-valued characterization)

A feasible integer vector over a finite set `s` (`∑_s t = δ`) **attaining** the lower bound
`∑_s t² = |δ|` is exactly `{0, sgn δ}`-valued with precisely `|δ|` nonzero entries: completing
`∑(t² − |t|) = 0` forces each `t_i² = |t_i|` (so `t_i ∈ {−1, 0, 1}`), and then `∑ t = δ`,
`∑ |t| = |δ|` pin the nonzero entries to the common sign `sgn δ`. -/

/-- **Pointwise integer-square equality.** `t² = |t|` (for `t : ℤ`) forces `t ∈ {−1, 0, 1}`. -/
theorem int_sq_eq_abs_cases {t : ℤ} (h : t ^ 2 = |t|) : t = -1 ∨ t = 0 ∨ t = 1 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht] at h
    have hfac : t * (t - 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (by omega))
  · rw [abs_of_neg ht] at h
    have hfac : t * (t + 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hfac with h0 | h1
    · omega
    · exact Or.inl (by omega)

/-- **The integer-square equality characterization.** A feasible `t : ι → ℤ` over a finite set `s`
(`∑_s t = δ`) that attains `∑_s t² = |δ|` is `{0, sgn δ}`-valued with exactly `|δ|` nonzero entries:
`(∀ i ∈ s, t i = 0 ∨ t i = sgn δ)` and `#{i ∈ s : t i ≠ 0} = |δ|`. -/
theorem sumSq_eq_abs_characterization {ι : Type*} (s : Finset ι) (t : ι → ℤ) (δ : ℤ)
    (hsum : (∑ i ∈ s, t i) = δ) (hsq : (∑ i ∈ s, (t i) ^ 2) = |δ|) :
    (∀ i ∈ s, t i = 0 ∨ t i = δ.sign) ∧
      (s.filter (fun i ↦ t i ≠ 0)).card = δ.natAbs := by
  classical
  have habs : ∀ a : ℤ, |a| ≤ a ^ 2 := fun a ↦ by
    rw [Int.abs_eq_natAbs]; exact Int.natAbs_le_self_sq a
  -- `∑ |t| ≤ ∑ t² = |δ|` and `|δ| = |∑ t| ≤ ∑ |t|`, so `∑ |t| = |δ|` and each `t² = |t|`.
  have hsumabs_le : (∑ i ∈ s, |t i|) ≤ |δ| := by
    rw [← hsq]; exact Finset.sum_le_sum (fun i _ ↦ habs (t i))
  have hsumabs_ge : |δ| ≤ ∑ i ∈ s, |t i| := by
    rw [← hsum]; exact Finset.abs_sum_le_sum_abs _ _
  have hsumabs : (∑ i ∈ s, |t i|) = |δ| := le_antisymm hsumabs_le hsumabs_ge
  have hzero : (∑ i ∈ s, ((t i) ^ 2 - |t i|)) = 0 := by
    rw [Finset.sum_sub_distrib, hsq, hsumabs]; ring
  have hnn : ∀ i ∈ s, 0 ≤ (t i) ^ 2 - |t i| := fun i _ ↦ by linarith [habs (t i)]
  have htri : ∀ i ∈ s, t i = -1 ∨ t i = 0 ∨ t i = 1 := by
    intro i hi
    have heq : (t i) ^ 2 - |t i| = 0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i hi
    exact int_sq_eq_abs_cases (by linarith [heq])
  -- Split `s` into `t = 1` / `t = −1`; `δ = a − b`, `|δ| = a + b`, nonzero count `= a + b`.
  have hsplit : (δ : ℤ)
      = ((s.filter (fun i ↦ t i = 1)).card : ℤ) - (s.filter (fun i ↦ t i = -1)).card := by
    rw [← hsum, Finset.card_filter, Finset.card_filter]; push_cast
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl
    intro i hi; rcases htri i hi with h | h | h <;> simp [h]
  have hsplitabs : (|δ| : ℤ)
      = ((s.filter (fun i ↦ t i = 1)).card : ℤ) + (s.filter (fun i ↦ t i = -1)).card := by
    rw [← hsumabs, Finset.card_filter, Finset.card_filter]; push_cast
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
    intro i hi; rcases htri i hi with h | h | h <;> simp [h]
  set a := (s.filter (fun i ↦ t i = 1)).card with ha
  set b := (s.filter (fun i ↦ t i = -1)).card with hb
  have hnonzero : (s.filter (fun i ↦ t i ≠ 0)).card = a + b := by
    rw [ha, hb, show (s.filter (fun i ↦ t i ≠ 0))
        = s.filter (fun i ↦ t i = 1) ∪ s.filter (fun i ↦ t i = -1) from ?_]
    · rw [Finset.card_union_of_disjoint (by rw [Finset.disjoint_filter]; intro i _ h1; omega)]
    · ext i; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨his, hne⟩; rcases htri i his with h | h | h
        · exact Or.inr ⟨his, h⟩
        · exact absurd h hne
        · exact Or.inl ⟨his, h⟩
      · rintro (⟨his, h⟩ | ⟨his, h⟩) <;> exact ⟨his, by omega⟩
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rcases htri i hi with h | h | h
    · refine Or.inr ?_
      have hbpos : 0 < b := by
        rw [hb, Finset.card_pos]; exact ⟨i, by rw [Finset.mem_filter]; exact ⟨hi, h⟩⟩
      have hδneg : δ < 0 := by rcases abs_cases δ with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
      rw [h, Int.sign_eq_neg_one_of_neg hδneg]
    · exact Or.inl h
    · refine Or.inr ?_
      have hapos : 0 < a := by
        rw [ha, Finset.card_pos]; exact ⟨i, by rw [Finset.mem_filter]; exact ⟨hi, h⟩⟩
      have hδpos : 0 < δ := by rcases abs_cases δ with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
      rw [h, Int.sign_eq_one_of_pos hδpos]
  · rw [hnonzero]
    have : (a : ℤ) + b = δ.natAbs := by rw [← hsplitabs, Int.abs_eq_natAbs]
    exact_mod_cast this

/-! ## The minimiser ↔ powerset bijection (the `θ`-count)

The minimiser set biject onto `powersetCard |δ| (qipLow d)` via `e ↦ {i ∈ qipLow : t_i ≠ 0}`,
`t = qipT d (↑e)`. The inverse rebuilds the in-face witness on the chosen support `A`:
`eOfSupport A i := (a + [i ∈ A]·sgn δ − d_{i+1}).toNat` on `qipLow`, `0` off it. Both directions
reuse the in-face nonnegativity (`qip_d_le_round` / `qip_d_le_round_sub_one`) and the value
assembly. -/

/-- The in-face witness on a chosen support `A ⊆ qipLow`: `eOfSupport A i := (a + [i ∈ A]·sgn δ −
d_{i+1}).toNat` for `(i:ℕ) < m`, `0` off the prefix. -/
noncomputable def eOfSupport (d : Fin (N + 1) → ℕ) (A : Finset (Fin N)) : Fin N → ℕ :=
  fun i ↦ if (i : ℕ) < qipM d
    then (qipRound d + (if i ∈ A then (qipDelta d).sign else 0) - (d i.succ : ℤ)).toNat else 0

/-- The chosen-support `t`-coordinate `[i ∈ A]·sgn δ` is `{0, ±1}`-valued, `≥ 0` when `δ ≥ 0` and
`≥ −1` when `δ < 0`. -/
theorem eOfSupport_bracket_nonneg (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    (A : Finset (Fin N)) {i : Fin N} (hi : (i : ℕ) < qipM d) :
    0 ≤ qipRound d + (if i ∈ A then (qipDelta d).sign else 0) - (d i.succ : ℤ) := by
  have hdsucc : (d i.succ : ℤ) = (d ⟨(i : ℕ) + 1, by have := qipM_le d; omega⟩ : ℤ) :=
    congrArg (fun x ↦ (d x : ℤ)) (Fin.ext (by simp [Fin.val_succ]))
  by_cases hδ : 0 ≤ qipDelta d
  · have hr : 0 ≤ (if i ∈ A then (qipDelta d).sign else 0) := by
      split_ifs with h
      · rcases lt_trichotomy (qipDelta d) 0 with h1 | h1 | h1
        · omega
        · simp [h1]
        · rw [Int.sign_eq_one_of_pos h1]; norm_num
      · rfl
    have hle : (d ⟨(i : ℕ) + 1, by have := qipM_le d; omega⟩ : ℤ) ≤ qipRound d :=
      qip_d_le_round d hd hN (by omega)
    rw [hdsucc]; linarith
  · have hδneg : qipDelta d < 0 := not_le.mp hδ
    have hr : -1 ≤ (if i ∈ A then (qipDelta d).sign else 0) := by
      split_ifs with h
      · rw [Int.sign_eq_neg_one_of_neg hδneg]
      · norm_num
    have hle : (d ⟨(i : ℕ) + 1, by have := qipM_le d; omega⟩ : ℤ) ≤ qipRound d - 1 :=
      qip_d_le_round_sub_one d hd hN (by omega) hδneg
    rw [hdsucc]; linarith

/-- `eOfSupport` vanishes off `qipLow`. -/
theorem eOfSupport_tail (d : Fin (N + 1) → ℕ) (A : Finset (Fin N)) {i : Fin N}
    (hi : i ∈ (qipLow d)ᶜ) : eOfSupport d A i = 0 := by
  simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
  simp only [eOfSupport, if_neg (by omega : ¬ (i : ℕ) < qipM d)]

/-- The `t`-coordinate of `eOfSupport A` on `qipLow` is `[i ∈ A]·sgn δ` (`.toNat` exact). -/
theorem qipT_eOfSupport (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    (A : Finset (Fin N)) {i : Fin N} (hi : i ∈ qipLow d) :
    qipT d (fun j ↦ (eOfSupport d A j : ℤ)) i
      = (if i ∈ A then (qipDelta d).sign else 0) := by
  have hlt : (i : ℕ) < qipM d := by simpa [qipLow, Finset.mem_filter] using hi
  have hval : (eOfSupport d A i : ℤ)
      = qipRound d + (if i ∈ A then (qipDelta d).sign else 0) - (d i.succ : ℤ) := by
    simp only [eOfSupport, if_pos hlt]
    rw [Int.toNat_of_nonneg (eOfSupport_bracket_nonneg d hd hN A hlt)]
  rw [qipT, hval]; ring

/-- `eOfSupport A` is feasible (`∑ = d_0`) when `#A = |δ|` and `A ⊆ qipLow`: `m·a + |δ|·sgn δ − (S −
d_0) = m·a + δ − S + d_0 = d_0`. -/
theorem eOfSupport_feasible (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {A : Finset (Fin N)} (hA : A ⊆ qipLow d) (hcard : A.card = (qipDelta d).natAbs) :
    eOfSupport d A ∈ qipFeasible d := by
  rw [qipFeasible, Finset.mem_finAntidiagonal]
  have hsumZ : (∑ i, (eOfSupport d A i : ℤ)) = (d 0 : ℤ) := by
    rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (eOfSupport d A i : ℤ))]
    have htail : (∑ i ∈ (qipLow d)ᶜ, (eOfSupport d A i : ℤ)) = 0 :=
      Finset.sum_eq_zero (fun i hi ↦ by rw [eOfSupport_tail d A hi]; rfl)
    rw [htail, add_zero]
    have hprefix : ∀ i ∈ qipLow d, (eOfSupport d A i : ℤ)
        = qipRound d + (if i ∈ A then (qipDelta d).sign else 0) - (d i.succ : ℤ) := by
      intro i hi
      have hlt : (i : ℕ) < qipM d := by simpa [qipLow, Finset.mem_filter] using hi
      simp only [eOfSupport, if_pos hlt]
      rw [Int.toNat_of_nonneg (eOfSupport_bracket_nonneg d hd hN A hlt)]
    rw [Finset.sum_congr rfl hprefix, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, qipLow_card, sum_qipLow_dsucc d, nsmul_eq_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA, Finset.sum_const, nsmul_eq_mul, hcard]
    have hsgn : ((qipDelta d).natAbs : ℤ) * (qipDelta d).sign = qipDelta d := by
      rw [mul_comm, Int.sign_mul_natAbs]
    have hδ : qipDelta d = qipS d - (qipM d : ℤ) * qipRound d := rfl
    rw [hsgn]; rw [hδ]; ring
  have : ((∑ i, eOfSupport d A i : ℕ) : ℤ) = ((d 0 : ℕ) : ℤ) := by push_cast at hsumZ ⊢; rw [hsumZ]
  exact_mod_cast this

/-- `eOfSupport A` attains `cValue` (`#A = |δ|`, `A ⊆ qipLow`): same `m`-face value assembly as the
canonical witness, with `∑_{qipLow}(t_i)² = #A = |δ|` (each chosen `t_i = sgn δ`, `sgn δ ² = 1`). -/
theorem Gqip_eOfSupport (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 1 ≤ N)
    {A : Finset (Fin N)} (hA : A ⊆ qipLow d) (hcard : A.card = (qipDelta d).natAbs) :
    Gqip d (eOfSupport d A) = cValue d := by
  set e := eOfSupport d A with he
  have hfeas := eOfSupport_feasible d hd hN hA hcard
  have hsumE : ∑ i, e i = d 0 := by
    rw [qipFeasible, Finset.mem_finAntidiagonal] at hfeas; exact hfeas
  have htailE : ∀ i ∈ (qipLow d)ᶜ, (fun j ↦ (e j : ℤ)) i = 0 :=
    fun i hi ↦ by simp only [he, eOfSupport_tail d A hi, Nat.cast_zero]
  have hsumLow : (∑ i ∈ qipLow d, (e i : ℤ)) = (d 0 : ℤ) := by
    have htail : (∑ i ∈ (qipLow d)ᶜ, (e i : ℤ)) = 0 := Finset.sum_eq_zero htailE
    have huniv : (∑ i, (e i : ℤ)) = (d 0 : ℤ) := by rw [← hsumE]; push_cast; ring
    rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (e i : ℤ)), htail, add_zero] at huniv
    exact huniv
  -- `∑_{qipLow}(t_i)² = #A · sgn δ² = #A = |δ|`.
  have hsq : (∑ i ∈ qipLow d, (qipT d (fun j ↦ (e j : ℤ)) i) ^ 2) = |qipDelta d| := by
    have hsqpt : ∀ i ∈ qipLow d, (qipT d (fun j ↦ (e j : ℤ)) i) ^ 2
        = (if i ∈ A then ((qipDelta d).sign) ^ 2 else 0) := by
      intro i hi; rw [he, qipT_eOfSupport d hd hN A hi]; split_ifs <;> ring
    rw [Finset.sum_congr rfl hsqpt, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA,
      Finset.sum_const, nsmul_eq_mul, hcard]
    -- `|δ|.natAbs · sgn δ ² = |δ|`.
    rcases eq_or_ne (qipDelta d) 0 with hδ0 | hδ0
    · simp [hδ0]
    · have hsgnsq : (qipDelta d).sign ^ 2 = 1 := by
        rcases lt_trichotomy (qipDelta d) 0 with h1 | h1 | h1
        · rw [Int.sign_eq_neg_one_of_neg h1]; norm_num
        · exact absurd h1 hδ0
        · rw [Int.sign_eq_one_of_pos h1]; norm_num
      rw [hsgnsq, mul_one, Int.abs_eq_natAbs]
  -- Assemble via `Phi_on_mface` + the `G`↔`Φ` transfer (same as the canonical witness).
  have htransfer := two_Gqip_eq_Phi_add d hsumE
  have hface := Phi_on_mface d (fun i ↦ (e i : ℤ)) htailE hsumLow
  rw [hsq] at hface
  have hwit := cValueNum_eq_two_Gqip_witness d hd hN
  have h2 : 2 * (Gqip d e : ℤ) = 2 * cValue d := by
    rw [cValue_eq_Gqip_witness d hd hN, ← hwit, htransfer, hface, sum_qipShift_sq_split d]; ring
  have : (Gqip d e : ℤ) = cValue d := by linarith [h2]
  exact_mod_cast this

/-- **The closed form for `θ` (Thm 7.10, `r = 0`).** For weakly-increasing `d`, the number of QIP
minimisers is `θ = C(m, |δ|)`: the minimisers biject onto the `|δ|`-subsets of the `m`-prefix
`qipLow` via `e ↦ {i ∈ qipLow : (qipT d ↑e) i ≠ 0}`, with inverse `A ↦ eOfSupport d A`. -/
theorem qipNumMinimisers_eq_cTheta (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (hne : (qipFeasible d).Nonempty) :
    ((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).card = cTheta d := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- `N = 0`: the empty function is the unique feasible point; `m = 0`, `|δ| = 0`, `C(0,0) = 1`.
    subst hN0
    have hm0 : qipM d = 0 := Nat.le_zero.mp (qipM_le d)
    -- feasibility (`N = 0`) forces `d 0 = 0`: the empty sum is `0`.
    have hd0 : d 0 = 0 := by
      obtain ⟨e, he⟩ := hne.exists_mem
      have : ∑ i, e i = d 0 := by simpa [qipFeasible, Finset.mem_finAntidiagonal] using he
      simpa using this.symm
    have hδ : qipDelta d = 0 := by
      have hS : qipS d = (d 0 : ℤ) := by simp [qipS, hm0]
      have hround : qipRound d = 0 := by simp [qipRound, hm0]
      simp [qipDelta, hm0, hround, hS, hd0]
    have hcard : ((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a _ b _; exact Subsingleton.elim a b
    have hpos : ((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).Nonempty := by
      obtain ⟨e₀, he₀, he₀eq⟩ := Finset.exists_mem_eq_inf' hne (Gqip d)
      exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀, by rw [qipMin, he₀eq]⟩⟩
    have hcardpos : 1 ≤ ((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).card :=
      hpos.card_pos
    have : ((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).card = 1 := by omega
    rw [this, cTheta, hm0, hδ]; rfl
  -- `N ≥ 1`: the bijection `e ↦ {i ∈ qipLow : (qipT ↑e) i ≠ 0}` ↔ `powersetCard |δ| qipLow`.
  rw [cTheta, ← qipLow_card d, ← Finset.card_powersetCard]
  set M := (qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne) with hM
  -- forward `e ↦ A_e`, inverse `A ↦ eOfSupport d A`.
  refine Finset.card_bij'
    (fun e _ ↦ (qipLow d).filter (fun i ↦ qipT d (fun j ↦ (e j : ℤ)) i ≠ 0))
    (fun A _ ↦ eOfSupport d A) ?_ ?_ ?_ ?_
  · -- `A_e ∈ powersetCard |δ| qipLow`: subset clear, card `= |δ|` by the characterization.
    intro e he
    rw [hM, Finset.mem_filter] at he
    have heq : Gqip d e = cValue d := by rw [he.2, qipMin_eq_cValue d hd hne]
    have hsumT := sum_qipLow_qipT d (fun j ↦ (e j : ℤ)) (by
      have hfeasE : ∑ i, e i = d 0 := by
        simpa [qipFeasible, Finset.mem_finAntidiagonal] using he.1
      have hdrop := qipMinimiser_support d hd he.1 heq
      have htail : (∑ i ∈ (qipLow d)ᶜ, (e i : ℤ)) = 0 := Finset.sum_eq_zero (fun i hi ↦ by
        simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] at hi
        simp only [hdrop i hi, Nat.cast_zero])
      have huniv : (∑ i, (e i : ℤ)) = (d 0 : ℤ) := by rw [← hfeasE]; push_cast; ring
      rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (e i : ℤ)), htail, add_zero] at huniv
      exact huniv)
    have hsqT := qipMinimiser_sumSq d hd hN he.1 heq
    have hchar := sumSq_eq_abs_characterization (qipLow d)
      (qipT d (fun j ↦ (e j : ℤ))) (qipDelta d) hsumT hsqT
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hchar.2⟩
  · -- `eOfSupport d A ∈ M`: feasible + attains `cValue = qipMin`.
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    rw [hM, Finset.mem_filter]
    have hfeas := eOfSupport_feasible d hd hN hA.1 hA.2
    refine ⟨hfeas, ?_⟩
    rw [Gqip_eOfSupport d hd hN hA.1 hA.2, qipMin_eq_cValue d hd hne]
  · -- left inverse: `eOfSupport d A_e = e` for a minimiser `e`.
    intro e he
    rw [hM, Finset.mem_filter] at he
    have heq : Gqip d e = cValue d := by rw [he.2, qipMin_eq_cValue d hd hne]
    have hdrop := qipMinimiser_support d hd he.1 heq
    -- `t`-vector is `{0, sgn δ}`-valued (characterization), so `A_e` recovers exactly the nonzeros.
    have hfeasE : ∑ i, e i = d 0 := by
      simpa [qipFeasible, Finset.mem_finAntidiagonal] using he.1
    have hsumLow : (∑ i ∈ qipLow d, (e i : ℤ)) = (d 0 : ℤ) := by
      have htail : (∑ i ∈ (qipLow d)ᶜ, (e i : ℤ)) = 0 := Finset.sum_eq_zero (fun i hi ↦ by
        simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] at hi
        simp only [hdrop i hi, Nat.cast_zero])
      have huniv : (∑ i, (e i : ℤ)) = (d 0 : ℤ) := by rw [← hfeasE]; push_cast; ring
      rw [← Finset.sum_add_sum_compl (qipLow d) (fun i ↦ (e i : ℤ)), htail, add_zero] at huniv
      exact huniv
    have hsumT := sum_qipLow_qipT d (fun j ↦ (e j : ℤ)) hsumLow
    have hsqT := qipMinimiser_sumSq d hd hN he.1 heq
    have hchar := (sumSq_eq_abs_characterization (qipLow d)
      (qipT d (fun j ↦ (e j : ℤ))) (qipDelta d) hsumT hsqT).1
    -- pointwise: `eOfSupport d A_e i = e i` for every `i`.
    funext i
    by_cases hilow : (i : ℕ) < qipM d
    · have hiL : i ∈ qipLow d := by simp [qipLow, Finset.mem_filter, hilow]
      have hAe : i ∈ (qipLow d).filter (fun i ↦ qipT d (fun j ↦ (e j : ℤ)) i ≠ 0)
          ↔ qipT d (fun j ↦ (e j : ℤ)) i ≠ 0 := by
        simp [Finset.mem_filter, hiL]
      -- value of `eOfSupport` at `i`: `(a + [t_i ≠ 0]·sgn δ − d_{i+1}).toNat`.
      have hval : (qipRound d
          + (if i ∈ (qipLow d).filter (fun i ↦ qipT d (fun j ↦ (e j : ℤ)) i ≠ 0)
              then (qipDelta d).sign else 0) - (d i.succ : ℤ))
          = (e i : ℤ) := by
        have hti := hchar i hiL
        have htdef : qipT d (fun j ↦ (e j : ℤ)) i = (e i : ℤ) + (d i.succ : ℤ) - qipRound d := rfl
        by_cases hz : qipT d (fun j ↦ (e j : ℤ)) i = 0
        · rw [if_neg (by rw [hAe]; exact fun h ↦ h hz)]
          rw [htdef] at hz; linarith [hz]
        · rw [if_pos (by rw [hAe]; exact hz)]
          rcases hti with h0 | hsgn
          · exact absurd h0 hz
          · rw [hsgn] at htdef; linarith [htdef]
      simp only [eOfSupport, if_pos hilow]
      rw [hval]; exact Int.toNat_natCast (e i)
    · have hcompl : i ∈ (qipLow d)ᶜ := by
        simp only [qipLow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        omega
      exact (eOfSupport_tail d _ hcompl).trans (hdrop i (by omega)).symm
  · -- right inverse: `A_{eOfSupport d A} = A` for `A ⊆ qipLow`, `#A = |δ|`.
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hiL, hne⟩
      rw [qipT_eOfSupport d hd hN A hiL] at hne
      by_contra hiA
      rw [if_neg hiA] at hne; exact hne rfl
    · intro hiA
      have hiL : i ∈ qipLow d := hA.1 hiA
      refine ⟨hiL, ?_⟩
      rw [qipT_eOfSupport d hd hN A hiL, if_pos hiA]
      -- `sgn δ ≠ 0` since `#A = |δ| > 0` (A nonempty).
      have hδne : qipDelta d ≠ 0 := by
        intro h0
        have hcard0 : A.card = 0 := by rw [hA.2, h0]; rfl
        rw [Finset.card_eq_zero.mp hcard0] at hiA
        exact absurd hiA (by simp)
      rcases lt_trichotomy (qipDelta d) 0 with h1 | h1 | h1
      · rw [Int.sign_eq_neg_one_of_neg h1]; norm_num
      · exact absurd h1 hδne
      · rw [Int.sign_eq_one_of_pos h1]; norm_num

/-! ## Witnesses (the closed-form objects compute) — non-vacuity for the definitions

The closed-form objects evaluate to the paper's numbers. `(2,2,2)` (Ex 6.2): `m = 2`, `a = 3`,
`δ = 0`, so `C = 3`, `θ = 1`. The Ex 6.3 rearrangement `d639 = (8,8,11,11,11,13,13,13,15)`:
`m = 4`, `a = 12`, `δ = 1`, so `C = 55`, `θ = 4` — matching brute-force `qipMin` and the paper. -/

section Witness

/-- **`(2,2,2)`: `cValue = 3`** (Ex 6.2; `m = 2`, `a = 3`, `δ = 0`). -/
theorem cValue_d222 : cValue d222 = 3 := by decide +kernel

/-- **`(2,2,2)`: `cTheta = 1`** (the unique top component). -/
theorem cTheta_d222 : cTheta d222 = 1 := by decide +kernel

/-- **Ex 6.3 `d639`: `a = 12`, `δ = 1`** (the rounding centre and residue). -/
theorem qipRound_qipDelta_d639 : qipRound d639 = 12 ∧ qipDelta d639 = 1 := by
  constructor <;> decide +kernel

/-- **Ex 6.3 `d639`: `cValue = 55`** (matching the paper's `C`). -/
theorem cValue_d639 : cValue d639 = 55 := by decide +kernel

/-- **Ex 6.3 `d639`: `cTheta = 4`** (matching the paper's `θ`). -/
theorem cTheta_d639 : cTheta d639 = 4 := by decide +kernel

end Witness

end DLNFibre.Core

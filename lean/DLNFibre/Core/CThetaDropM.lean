import DLNFibre.Core.CThetaExplicit

/-!
# `DLNFibre.Core.CThetaDropM` — the drop-to-`m` active-support reduction (the wall)

Lehalleur–Rimányi 2024 Theorem 7.10 (`r = 0`) computes the combinatorial codimension `C` by
minimising the integer distance `Φ(e) := ∑_i (e_i − s_i)²` (`s_i = qipShift d i = d_0 − d_{i+1}`,
the square-completion target of `Core.CThetaExplicit.two_Gqipℤ_sub_sq`) over the feasible face
`{ e : Fin N → ℕ | ∑ e = d_0 }`. The **wall** of that computation is a support reduction: a
minimiser of `Φ` is supported on the first `m` coordinates only, where `m` is pinned by an
explicit antitone arithmetic threshold.

For a weakly-increasing dimension vector `d` (`Monotone d`), set (paper `d'_i = d i`, `i = 0..N`)

$$ A_l := \Bigl(\textstyle\sum_{i=0}^{l} d_i\Bigr) - l\,d_l , \qquad
   \mathrm{Pred}(l) := A_l \ge 0, \qquad m := \max\{\, l \le N : A_l \ge 0 \,\}. $$

**Lemma 1 (well-definedness).** `A_1 = d_0 ≥ 0` (so `m ≥ 1`) and `A_{l+1} = A_l − l(d_{l+1} − d_l)`
is non-increasing, so `{l : A_l ≥ 0}` is the prefix `{1,…,m}` (`qipM` via `Nat.findGreatest`).

**Lemma 2 (separation).** If `m < N` then `m · d_{m+1} > S` where `S := ∑_{i=0}^m d_i` — the integer
negation of `Pred(m+1)`; carried as `m · d_{m+1} − S ≥ 1` (no division).

**The wall (`qip_unit_transfer_decreases`).** Any feasible `e` with `e_k ≥ 1` for some 0-based
`k ≥ m` is beaten by the single-unit transfer `k → j` (`j = argmin_{<m}` of the shifted coordinate
`u_i := e_i − d_0 + d_{i+1}`): `Φ(e') = Φ(e) + 2(u_j − u_k + 1) < Φ(e)`, since `u_k − u_j ≥ 2` by
the integer min-≤-average bound and Lemma 2. Hence (`qip_minimiser_support_le_m`) every
`Φ`-minimiser on the feasible face has `e_i = 0` for 0-based `i ≥ m` (paper `i > m`).

**Index discipline.** Lean `e i` = paper `e_{i+1}`; paper `i > m` ⟺ 0-based `Fin N` index `≥ m`.
The reduction is to the `m`-face; the rounding/value-assembly step is a separate downstream tide
that must run AFTER this, stated on the `m`-face only (the certificate's ordering obligation).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## 0. The distance objective `Φ` -/

/-- The square-completion objective `Φ(e) := ∑_i (e_i − s_i)²`, with `s_i = qipShift d i`, on an
integer-valued `e`. Minimising `Φ` over the feasible face `∑ e = d_0` is minimising `Gqip`
(`Core.CThetaExplicit.two_Gqipℤ_sub_sq`). -/
def Phi (d : Fin (N + 1) → ℕ) (e : Fin N → ℤ) : ℤ :=
  ∑ i, (e i - qipShift d i) ^ 2

/-! ## 1. The threshold `m` and Lemma 1 (well-definedness) -/

/-- The integer `A_l := (∑_{i=0}^{l} d_i) − l · d_l`, reading `d` at the clamped index `min l N`
(so `A_l` is total in `l : ℕ`; on `l ≤ N` the clamp is the identity). -/
def qipA (d : Fin (N + 1) → ℕ) (l : ℕ) : ℤ :=
  (∑ i ∈ Finset.range (l + 1), (d ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ))
    - (l : ℤ) * (d ⟨min l N, Nat.lt_succ_of_le (min_le_right l N)⟩ : ℤ)

/-- The drop predicate `Pred(l) := A_l ≥ 0` (decidable: a `ℤ` inequality). -/
def qipPred (d : Fin (N + 1) → ℕ) (l : ℕ) : Prop := 0 ≤ qipA d l

instance (d : Fin (N + 1) → ℕ) : DecidablePred (qipPred d) :=
  fun l ↦ inferInstanceAs (Decidable (0 ≤ qipA d l))

/-- The active-support threshold `m := max { l ≤ N : A_l ≥ 0 }` (`Nat.findGreatest`). -/
noncomputable def qipM (d : Fin (N + 1) → ℕ) : ℕ := Nat.findGreatest (qipPred d) N

/-- `A_1 = d_0` (so `Pred 1` always holds; the qualifying set is nonempty). -/
theorem qipA_one (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) : qipA d 1 = (d 0 : ℤ) := by
  unfold qipA
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : (d ⟨min 0 N, Nat.lt_succ_of_le (min_le_right 0 N)⟩ : ℤ) = (d 0 : ℤ) :=
    congrArg (fun x ↦ (d x : ℤ)) (Fin.ext (by simp))
  have h1 : (d ⟨min 1 N, Nat.lt_succ_of_le (min_le_right 1 N)⟩ : ℤ)
      = (d ⟨1, by omega⟩ : ℤ) :=
    congrArg (fun x ↦ (d x : ℤ)) (Fin.ext (by simp [Nat.min_eq_left hN]))
  rw [h0, h1]; ring

/-- `Pred 1` holds (`A_1 = d_0 ≥ 0`) when `1 ≤ N`. -/
theorem qipPred_one (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) : qipPred d 1 := by
  rw [qipPred, qipA_one d hN]; positivity

/-- `m ≥ 1` (the prefix is nonempty). -/
theorem qipM_ge_one (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) : 1 ≤ qipM d :=
  Nat.le_findGreatest hN (qipPred_one d hN)

/-- `m ≤ N`. -/
theorem qipM_le (d : Fin (N + 1) → ℕ) : qipM d ≤ N := Nat.findGreatest_le N

/-- `¬Pred(l)` for `qipM d < l ≤ N` (`m` is the greatest qualifying index). -/
theorem not_qipPred_of_gt_qipM (d : Fin (N + 1) → ℕ) {l : ℕ} (h : qipM d < l) (h' : l ≤ N) :
    ¬ qipPred d l := Nat.findGreatest_is_greatest h h'

/-- `Pred(m)` holds: `m` itself qualifies (`A_m ≥ 0`). -/
theorem qipPred_qipM (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) : qipPred d (qipM d) :=
  Nat.findGreatest_spec hN (qipPred_one d hN)

/-! ## 2. The strict separation lemma -/

/-- The partial sum `S := ∑_{i=0}^{m} d_i` (paper `S_m`), over `ℤ` with the clamped index. -/
noncomputable def qipS (d : Fin (N + 1) → ℕ) : ℤ :=
  ∑ i ∈ Finset.range (qipM d + 1), (d ⟨min i N, Nat.lt_succ_of_le (min_le_right i N)⟩ : ℤ)

/-- On `qipM d < N`, `A_{m+1} = S − m · d_{m+1}` (the `(m+1)`-th `A` reads `S + d_{m+1}` over the
extended range, minus `(m+1)·d_{m+1}`). -/
theorem qipA_succ_qipM (d : Fin (N + 1) → ℕ) (hm : qipM d < N) :
    qipA d (qipM d + 1) = qipS d - (qipM d : ℤ) * (d ⟨qipM d + 1, by omega⟩ : ℤ) := by
  unfold qipA qipS
  rw [Finset.sum_range_succ]
  have hd1 : (d ⟨min (qipM d + 1) N, Nat.lt_succ_of_le (min_le_right (qipM d + 1) N)⟩ : ℤ)
      = (d ⟨qipM d + 1, by omega⟩ : ℤ) :=
    congrArg (fun x ↦ (d x : ℤ)) (Fin.ext (by simp [Nat.min_eq_left (by omega : qipM d + 1 ≤ N)]))
  rw [hd1]; push_cast; ring

/-- **Separation (Lemma 2), integer form.** If `m < N` then `m · d_{m+1} − S ≥ 1` — equivalently
`m · d_{m+1} > S`. This is the integer negation of `Pred(m+1)`. -/
theorem qip_separation (d : Fin (N + 1) → ℕ) (hm : qipM d < N) :
    qipS d + 1 ≤ (qipM d : ℤ) * (d ⟨qipM d + 1, by omega⟩ : ℤ) := by
  have hneg : ¬ qipPred d (qipM d + 1) := not_qipPred_of_gt_qipM d (by omega) (by omega)
  rw [qipPred, qipA_succ_qipM d hm, not_le] at hneg
  omega

/-! ## 3. The unit-transfer construction (the wall) -/

/-- The shifted coordinate `u_i := e_i − d_0 + d_{i+1}` (`= e_i − s_i`, `s = qipShift`). -/
def qipU (d : Fin (N + 1) → ℕ) (e : Fin N → ℕ) (i : Fin N) : ℤ :=
  (e i : ℤ) - (d 0 : ℤ) + (d i.succ : ℤ)

/-- The "low" coordinates `{ i : Fin N | (i:ℕ) < m }`. -/
noncomputable def qipLow (d : Fin (N + 1) → ℕ) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)).filter (fun i ↦ (i : ℕ) < qipM d)

/-- `qipLow` is nonempty when `1 ≤ m` (it contains the 0-based index `0`). -/
theorem qipLow_nonempty (d : Fin (N + 1) → ℕ) (hN : 1 ≤ N) (h1 : 1 ≤ qipM d) :
    (qipLow d).Nonempty := by
  refine ⟨⟨0, hN⟩, ?_⟩
  simp only [qipLow, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h1

/-- `#(qipLow d) = m` (since `m ≤ N`: the low filter has exactly `m` elements). -/
theorem qipLow_card (d : Fin (N + 1) → ℕ) : (qipLow d).card = qipM d := by
  have hmN := qipM_le d
  rw [qipLow]
  have h : (Finset.filter (fun i : Fin N ↦ (i : ℕ) < qipM d) Finset.univ)
      = (Finset.range (qipM d)).attachFin
          (fun k hk => by simp only [Finset.mem_range] at hk; omega) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
      Finset.mem_range]
  rw [h, Finset.card_attachFin, Finset.card_range]

/-- `∑_{i ∈ qipLow} d_{i+1} = S − d_0` (the within-prefix sum of `d`). -/
theorem sum_qipLow_dsucc (d : Fin (N + 1) → ℕ) :
    (∑ i ∈ qipLow d, (d i.succ : ℤ)) = qipS d - (d 0 : ℤ) := by
  have hmN := qipM_le d
  -- reindex `qipLow` (filter of `Fin N`) to `range m`, and `qipS` (range (m+1)) split off `0`.
  set g : ℕ → ℤ := fun k ↦ (d ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : ℤ) with hg
  have hqipS : qipS d = ∑ i ∈ Finset.range (qipM d + 1), g i := rfl
  rw [hqipS, Finset.sum_range_succ']
  have h0 : g 0 = (d 0 : ℤ) := by simp [hg]
  rw [h0, add_sub_cancel_right]
  -- LHS: sum over the filtered `Fin N`; rewrite the summand via `g`, reindex to `range N`.
  rw [qipLow, Finset.sum_filter]
  have hsummand : ∀ i : Fin N, (if (i : ℕ) < qipM d then (d i.succ : ℤ) else 0)
      = (if (i : ℕ) < qipM d then g ((i : ℕ) + 1) else 0) := by
    intro i
    have : g ((i : ℕ) + 1) = (d i.succ : ℤ) := by
      simp only [hg, Nat.min_eq_left (by have := i.isLt; omega : (i : ℕ) + 1 ≤ N)]
      exact congrArg (fun x ↦ (d x : ℤ)) (Fin.ext (by simp [Fin.val_succ]))
    rw [this]
  rw [Finset.sum_congr rfl (fun i _ ↦ hsummand i)]
  rw [show (∑ i : Fin N, if (i : ℕ) < qipM d then g ((i : ℕ) + 1) else 0)
      = ∑ k ∈ Finset.range N, if k < qipM d then g (k + 1) else 0 from
    Fin.sum_univ_eq_sum_range (fun k ↦ if k < qipM d then g (k + 1) else 0) N]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : (Finset.range N).filter (fun k ↦ k < qipM d) = Finset.range (qipM d) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilter]

/-- **Two-point sum surgery.** Two `ℤ`-functions agreeing off `{j, k}` (`j ≠ k`) and with equal
`{j, k}`-totals have equal full sums. -/
theorem sum_eq_of_two_point {f g : Fin N → ℤ} {j k : Fin N} (hjk : j ≠ k)
    (hpair : f j + f k = g j + g k) (hoth : ∀ i, i ≠ j → i ≠ k → f i = g i) :
    (∑ i, f i) = ∑ i, g i := by
  classical
  have key : (∑ i, (f i - g i)) = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ i = j ∨ i = k)]
    have h2 : (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ (i = j ∨ i = k)), (f i - g i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
      rw [hoth i hi.1 hi.2, sub_self]
    have h1 : (∑ i ∈ Finset.univ.filter (fun i ↦ i = j ∨ i = k), (f i - g i))
        = (f j - g j) + (f k - g k) := by
      rw [show (Finset.univ.filter (fun i ↦ i = j ∨ i = k)) = {j, k} by
        ext i; simp [Finset.mem_insert, Finset.mem_singleton, eq_comm]]
      rw [Finset.sum_pair hjk]
    rw [h1, h2, add_zero]; linarith [hpair]
  linarith [Finset.sum_sub_distrib (f := f) (g := g) (s := (Finset.univ : Finset (Fin N))), key]

/-- **Pair-sum collapse.** A `ℤ`-function vanishing off `{j, k}` (`j ≠ k`) sums to `F j + F k`. -/
theorem sum_eq_pair_of_zero {F : Fin N → ℤ} {j k : Fin N} (hjk : j ≠ k)
    (h : ∀ i, i ≠ j → i ≠ k → F i = 0) : (∑ i, F i) = F j + F k := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ i = j ∨ i = k)]
  have h2 : (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ (i = j ∨ i = k)), F i) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
    exact h i hi.1 hi.2
  have h1 : (∑ i ∈ Finset.univ.filter (fun i ↦ i = j ∨ i = k), F i) = F j + F k := by
    rw [show (Finset.univ.filter (fun i ↦ i = j ∨ i = k)) = {j, k} by
      ext i; simp [Finset.mem_insert, Finset.mem_singleton, eq_comm]]
    rw [Finset.sum_pair hjk]
  rw [h1, h2, add_zero]

/-- The unit-transfer vector `e' = e + 1_j − 1_k` (`j ≠ k`), as a ℕ-function. -/
noncomputable def qipTransfer (e : Fin N → ℕ) (j k : Fin N) : Fin N → ℕ :=
  Function.update (Function.update e j (e j + 1)) k (e k - 1)

/-- The transfer vector at `j` (with `j ≠ k`): `e_j + 1`. -/
theorem qipTransfer_j {e : Fin N → ℕ} {j k : Fin N} (hjk : j ≠ k) :
    qipTransfer e j k j = e j + 1 := by
  rw [qipTransfer, Function.update_of_ne hjk, Function.update_self]

/-- The transfer vector at `k`: `e_k − 1`. -/
theorem qipTransfer_k {e : Fin N → ℕ} {j k : Fin N} :
    qipTransfer e j k k = e k - 1 := by
  rw [qipTransfer, Function.update_self]

/-- The transfer vector off `{j, k}`: unchanged. -/
theorem qipTransfer_other {e : Fin N → ℕ} {j k i : Fin N} (hij : i ≠ j) (hik : i ≠ k) :
    qipTransfer e j k i = e i := by
  rw [qipTransfer, Function.update_of_ne hik, Function.update_of_ne hij]

/-- **The wall — strict-decrease transfer.** For weakly-increasing `d` and feasible `e`, if some
0-based coordinate `k ≥ m` carries `e_k ≥ 1`, the explicit single-unit transfer `k → j`
(`j = argmin` of `u` over `qipLow`) yields a feasible `e'` with `Φ(e') < Φ(e)`. The decrease is
`Φ(e') − Φ(e) = 2(u_j − u_k + 1) ≤ −2`, with `u_k − u_j ≥ 2` from the integer min-≤-average bound
and the separation `m·d_{m+1} − S ≥ 1`. -/
theorem qip_unit_transfer_decreases (d : Fin (N + 1) → ℕ) (hd : Monotone d) (e : Fin N → ℕ)
    (hfeas : e ∈ qipFeasible d) {k : Fin N} (hk : qipM d ≤ (k : ℕ)) (hek : 1 ≤ e k) :
    ∃ e' ∈ qipFeasible d, Phi d (fun i ↦ (e' i : ℤ)) < Phi d (fun i ↦ (e i : ℤ)) := by
  classical
  have hN : 1 ≤ N := by have := k.isLt; omega
  have hm1 : 1 ≤ qipM d := qipM_ge_one d hN
  have hmN : qipM d < N := by have := k.isLt; omega
  -- feasibility as a ℕ-sum
  have hsum : ∑ i, e i = d 0 := by simpa [qipFeasible, Finset.mem_finAntidiagonal] using hfeas
  -- step 2: pick the argmin `j` over qipLow
  obtain ⟨j, hjmem, hjmin⟩ :=
    Finset.exists_min_image (qipLow d) (qipU d e) (qipLow_nonempty d hN hm1)
  have hjlt : (j : ℕ) < qipM d := by
    simpa [qipLow, Finset.mem_filter] using hjmem
  have hjk : j ≠ k := fun h ↦ by rw [h] at hjlt; omega
  -- step 3: the transfer vector and its feasibility
  set e' := qipTransfer e j k with he'
  have hej : e' j = e j + 1 := qipTransfer_j hjk
  have hek' : e' k = e k - 1 := qipTransfer_k
  have hoth : ∀ i, i ≠ j → i ≠ k → e' i = e i := fun i hij hik ↦ qipTransfer_other hij hik
  -- ℤ-casts of the changed coords (no ℕ truncation: `e k ≥ 1`)
  have hejZ : (e' j : ℤ) = (e j : ℤ) + 1 := by rw [hej]; push_cast; ring
  have hekZ : (e' k : ℤ) = (e k : ℤ) - 1 := by rw [hek']; rw [Nat.cast_sub hek]; ring
  have he'feas : e' ∈ qipFeasible d := by
    rw [qipFeasible, Finset.mem_finAntidiagonal]
    have hZ : (∑ i, (e' i : ℤ)) = (∑ i, (e i : ℤ)) := by
      refine sum_eq_of_two_point hjk ?_ (fun i hij hik ↦ by rw [hoth i hij hik])
      rw [hejZ, hekZ]; ring
    have : ((∑ i, e' i : ℕ) : ℤ) = ((d 0 : ℕ) : ℤ) := by
      push_cast at hZ ⊢; rw [hZ]; rw [← hsum]; push_cast; ring
    exact_mod_cast this
  refine ⟨e', he'feas, ?_⟩
  -- step 4: cost change Φ(e') − Φ(e) = 2 (u_j − u_k + 1)
  -- u i = e i − s i = qipU; note qipShift d i = d 0 − d i.succ, so e i − qipShift = qipU.
  have hu : ∀ i : Fin N, (e i : ℤ) - qipShift d i = qipU d e i := by
    intro i; rw [qipShift, qipU]; ring
  have hcost : Phi d (fun i ↦ (e' i : ℤ)) - Phi d (fun i ↦ (e i : ℤ))
      = 2 * (qipU d e j - qipU d e k + 1) := by
    unfold Phi
    rw [← Finset.sum_sub_distrib]
    simp only []
    -- the per-coordinate difference vanishes off {j,k}; on {j,k} it is the explicit value.
    rw [sum_eq_pair_of_zero hjk (fun i hij hik ↦ by
      show (((e' i : ℤ)) - qipShift d i) ^ 2 - (((e i : ℤ)) - qipShift d i) ^ 2 = 0
      rw [hoth i hij hik]; ring)]
    rw [hejZ, hekZ]
    -- ((u_j+1)² − u_j²) + ((u_k−1)² − u_k²) = 2(u_j − u_k + 1)
    have e1 : (e j : ℤ) + 1 - qipShift d j = qipU d e j + 1 := by
      rw [show (e j : ℤ) + 1 - qipShift d j = ((e j : ℤ) - qipShift d j) + 1 by ring, hu j]
    have e2 : (e k : ℤ) - 1 - qipShift d k = qipU d e k - 1 := by
      rw [show (e k : ℤ) - 1 - qipShift d k = ((e k : ℤ) - qipShift d k) - 1 by ring, hu k]
    rw [e1, e2, hu j, hu k]; ring
  -- step 5: the integer gap `u_k − u_j ≥ 2`.
  set m := qipM d with hmdef
  -- (a) min ≤ average, integer form: `m · u_j ≤ ∑_{qipLow} u`.
  have hcard : (qipLow d).card = m := qipLow_card d
  have havg : (m : ℤ) * qipU d e j ≤ ∑ i ∈ qipLow d, qipU d e i := by
    have := Finset.card_nsmul_le_sum (qipLow d) (qipU d e) (qipU d e j)
      (fun i hi ↦ hjmin i hi)
    rw [hcard, nsmul_eq_mul] at this; exact this
  -- (b) the qipLow `u`-sum value: `∑ u = (∑_{qipLow} e) + (S − d_0) − m·d_0`.
  have hsumU : (∑ i ∈ qipLow d, qipU d e i)
      = (∑ i ∈ qipLow d, (e i : ℤ)) + (qipS d - (d 0 : ℤ)) - (m : ℤ) * (d 0 : ℤ) := by
    rw [← sum_qipLow_dsucc d]
    rw [show (∑ i ∈ qipLow d, qipU d e i)
        = ∑ i ∈ qipLow d, ((e i : ℤ) + (d i.succ : ℤ) - (d 0 : ℤ)) from
      Finset.sum_congr rfl (fun i _ ↦ by rw [qipU]; ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  -- (c) `∑_{qipLow} e ≤ d_0` (e ≥ 0, qipLow ⊆ univ).
  have hsumE : (∑ i ∈ qipLow d, (e i : ℤ)) ≤ (d 0 : ℤ) := by
    rw [← hsum]; push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ ↦ by positivity)
  -- combine (a)(b)(c): `m · u_j ≤ S − m·d_0`.
  have hujBound : (m : ℤ) * qipU d e j ≤ qipS d - (m : ℤ) * (d 0 : ℤ) := by
    calc (m : ℤ) * qipU d e j ≤ ∑ i ∈ qipLow d, qipU d e i := havg
      _ = (∑ i ∈ qipLow d, (e i : ℤ)) + (qipS d - (d 0 : ℤ)) - (m : ℤ) * (d 0 : ℤ) := hsumU
      _ ≤ (d 0 : ℤ) + (qipS d - (d 0 : ℤ)) - (m : ℤ) * (d 0 : ℤ) := by linarith [hsumE]
      _ = qipS d - (m : ℤ) * (d 0 : ℤ) := by ring
  -- lower bound on `u_k`: `u_k ≥ 1 − d_0 + d_{m+1}` (e_k ≥ 1; d_{k+1} ≥ d_{m+1}).
  have hdk : (d ⟨m + 1, by omega⟩ : ℤ) ≤ (d k.succ : ℤ) := by
    have : (d ⟨m + 1, by omega⟩ : ℕ) ≤ d k.succ :=
      hd (by rw [Fin.le_def, Fin.val_succ]; simp; omega)
    exact_mod_cast this
  have hukLow : (1 : ℤ) - (d 0 : ℤ) + (d ⟨m + 1, by omega⟩ : ℤ) ≤ qipU d e k := by
    have hek1 : (1 : ℤ) ≤ (e k : ℤ) := by exact_mod_cast hek
    rw [qipU]; linarith [hek1, hdk]
  -- `m · u_k ≥ m·(1 − d_0 + d_{m+1})`, and `m·d_{m+1} − S ≥ 1` (separation).
  have hsep : qipS d + 1 ≤ (m : ℤ) * (d ⟨m + 1, by omega⟩ : ℤ) := qip_separation d hmN
  have hmpos : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm1
  have hukBound : (m : ℤ) * (1 - (d 0 : ℤ) + (d ⟨m + 1, by omega⟩ : ℤ)) ≤ (m : ℤ) * qipU d e k :=
    mul_le_mul_of_nonneg_left hukLow (by linarith)
  -- `m·(u_k − u_j) ≥ m + 1`.
  have hgapM : (m : ℤ) + 1 ≤ (m : ℤ) * (qipU d e k - qipU d e j) := by
    have expand : (m : ℤ) * (qipU d e k - qipU d e j)
        = (m : ℤ) * qipU d e k - (m : ℤ) * qipU d e j := by ring
    rw [expand]
    nlinarith [hukBound, hujBound, hsep, hmpos]
  -- divide by `m ≥ 1`: `u_k − u_j ≥ 2`.
  have hgap : (2 : ℤ) ≤ qipU d e k - qipU d e j := by
    by_contra h
    rw [not_le] at h
    have hle1 : qipU d e k - qipU d e j ≤ 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hle1 (by linarith : (0 : ℤ) ≤ (m : ℤ)), hgapM, hmpos]
  -- step 6: conclude `Φ(e') < Φ(e)`.
  have : Phi d (fun i ↦ (e' i : ℤ)) - Phi d (fun i ↦ (e i : ℤ)) ≤ -2 := by
    rw [hcost]; linarith [hgap]
  linarith [this]

/-! ## 4. The drop-to-`m` support reduction -/

/-- **The wall (drop-to-`m`).** For weakly-increasing `d`, every `Φ`-minimiser `e` on the feasible
face `{∑ e = d_0}` has `e_i = 0` for every 0-based coordinate `i ≥ m` (paper `i > m`). Proved by
contradiction: a nonzero coordinate at `i ≥ m` would admit the strict-decrease unit transfer
(`qip_unit_transfer_decreases`), contradicting minimality. The reduction is to the `m`-face; the
rounding/value-assembly step is a separate downstream tide stated on the `m`-face only. -/
theorem qip_minimiser_support_le_m (d : Fin (N + 1) → ℕ) (hd : Monotone d) (e : Fin N → ℕ)
    (hfeas : e ∈ qipFeasible d)
    (hmin : ∀ e'' ∈ qipFeasible d, Phi d (fun i ↦ (e i : ℤ)) ≤ Phi d (fun i ↦ (e'' i : ℤ))) :
    ∀ i : Fin N, qipM d ≤ (i : ℕ) → e i = 0 := by
  intro i hi
  by_contra hne
  have hei : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr hne
  obtain ⟨e', he'feas, hlt⟩ := qip_unit_transfer_decreases d hd e hfeas hi hei
  exact absurd (hmin e' he'feas) (not_le.mpr hlt)

/-! ## Witnesses (non-vacuity)

`m` fires at concrete data. For `(2,2,2)` (Ex 6.2): `A = (A_1, A_2) = (2, 2)`, both `≥ 0`, so
`m = N = 2` — no drop, support is all of `{1, 2}`. For the Ex 6.3 rearrangement
`d' = (8,8,11,11,11,13,13,13,15)`: `A = (8,5,5,5,−3,−3,−3,−17)`, so `m = 4` (the drop), and the
separation `m·d'_{m+1} − S = 4·13 − 49 = 3 > 0` holds (here `S = ∑_{0..4} d' = 49`). -/

section Witness

/-- `(2,2,2)`: the threshold `m = N = 2` — no drop, the minimiser support is the full `{1, 2}`. -/
theorem qipM_d222_eq_two : qipM d222 = 2 := by decide +kernel

/-- Ex 6.3 rearrangement `d' = (8,8,11,11,11,13,13,13,15)` is weakly increasing. -/
abbrev d639 : Fin 9 → ℕ := ![8, 8, 11, 11, 11, 13, 13, 13, 15]

/-- `d639` is weakly increasing (the QIP hypothesis). -/
theorem d639_monotone : Monotone d639 := by decide

/-- **Ex 6.3: the threshold `m = 4`** — the active support drops from `N = 8` to `4`
(`A = (8,5,5,5,−3,−3,−3,−17)`, last nonnegative at `l = 4`). -/
theorem qipM_d639_eq_four : qipM d639 = 4 := by decide +kernel

/-- **Ex 6.3: the strict separation** `m · d'_{m+1} > S` holds (`4·13 = 52 > 49 = S`), the integer
witness `qipS d639 + 1 ≤ qipM d639 · d'_5` of `qip_separation`. -/
theorem qip_separation_d639 :
    qipS d639 + 1 ≤ (qipM d639 : ℤ) * (d639 ⟨qipM d639 + 1, by decide⟩ : ℤ) :=
  qip_separation d639 (by rw [qipM_d639_eq_four]; decide)

end Witness

end DLNFibre.Core

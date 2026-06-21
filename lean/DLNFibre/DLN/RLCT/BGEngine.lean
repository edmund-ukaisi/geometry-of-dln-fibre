import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# `BGEngine` — backward-greedy "min-suffix realizer" over `ℤ`

A self-contained, abstract engine. The widths are a `List ℤ` (`b`, length `n`); the pool is a
`Multiset ℤ` (`R`, card `n`). `Dom b R` asserts the ascending-sorted `R` pointwise-dominates the
ascending-sorted `b`. We encode `Dom` via the equivalent **head-count** form
`∀ τ, (R.filter (· < τ)).card ≤ (b.filter (· < τ)).card`: at every threshold `τ`, `R` has no more
elements below `τ` than `b` does. For equal cardinalities this is exactly sorted pointwise
domination `sortedAsc R [i] ≥ sortedAsc b [i] ∀ i` (a standard order-statistics equivalence, stated
here but **not proven** — the engine never needs the sorted form); we work with the count form
because it commutes cleanly with `erase`.

`ENGINE-2` is the one-step closure: erasing the minimal pool element `≥ b.getLast` and dropping the
last width preserves `Dom`. `ENGINE-1` is the backward greedy built on top of it.
-/

namespace DLNFibre.DLN.RLCT.BGEngine

open scoped BigOperators
open Multiset

/-- Head-count: the number of elements of `M` strictly below `τ`. -/
def cLt (M : Multiset ℤ) (τ : ℤ) : ℕ := (M.filter (· < τ)).card

/-- `Dom b R`: equal cardinalities and `R` head-count-dominated by `b` at every threshold. -/
def Dom (b : List ℤ) (R : Multiset ℤ) : Prop :=
  R.card = b.length ∧ ∀ τ : ℤ, cLt R τ ≤ cLt (b : Multiset ℤ) τ

/-- `cLt` as a `countP`: head-count is the predicate-count of `(· < τ)`. -/
theorem cLt_eq_countP (M : Multiset ℤ) (τ : ℤ) : cLt M τ = M.countP (· < τ) :=
  (countP_eq_card_filter _ M).symm

/-- Erasing a member splits the head-count off by the threshold indicator on that member. -/
theorem cLt_erase (M : Multiset ℤ) (a : ℤ) (τ : ℤ) (ha : a ∈ M) :
    cLt M τ = cLt (M.erase a) τ + (if a < τ then 1 else 0) := by
  conv_lhs => rw [cLt_eq_countP, ← cons_erase ha, countP_cons]
  rw [cLt_eq_countP]

/-- The head-count is monotone in the threshold. -/
theorem cLt_mono (M : Multiset ℤ) {σ τ : ℤ} (h : σ ≤ τ) : cLt M σ ≤ cLt M τ :=
  card_le_card (monotone_filter_right M fun _ hw => lt_of_lt_of_le hw h)

/-! ## The pick: the minimal pool element `≥ t` -/

/-- The candidate set: distinct pool values that are `≥ t`. -/
def pickSet (t : ℤ) (R : Multiset ℤ) : Finset ℤ := R.toFinset.filter (t ≤ ·)

/-- The pick `v`: the minimal pool value `≥ t` (junk default `t` if none exists). -/
noncomputable def pick (t : ℤ) (R : Multiset ℤ) : ℤ :=
  if h : (pickSet t R).Nonempty then (pickSet t R).min' h else t

/-- The candidate set is nonempty iff some pool element is `≥ t`. -/
theorem pickSet_nonempty_iff {t : ℤ} {R : Multiset ℤ} :
    (pickSet t R).Nonempty ↔ ∃ w ∈ R, t ≤ w := by
  simp only [pickSet, Finset.filter_nonempty_iff, Multiset.mem_toFinset]

/-- When some pool element is `≥ t`, the pick lies in the pool. -/
theorem pick_mem {t : ℤ} {R : Multiset ℤ} (h : ∃ w ∈ R, t ≤ w) : pick t R ∈ R := by
  have hne : (pickSet t R).Nonempty := pickSet_nonempty_iff.mpr h
  rw [pick, dif_pos hne]
  have := (pickSet t R).min'_mem hne
  simp only [pickSet, Finset.mem_filter, Multiset.mem_toFinset] at this
  exact this.1

/-- When some pool element is `≥ t`, the pick satisfies `t ≤ pick`. -/
theorem le_pick {t : ℤ} {R : Multiset ℤ} (h : ∃ w ∈ R, t ≤ w) : t ≤ pick t R := by
  have hne : (pickSet t R).Nonempty := pickSet_nonempty_iff.mpr h
  rw [pick, dif_pos hne]
  have := (pickSet t R).min'_mem hne
  simp only [pickSet, Finset.mem_filter, Multiset.mem_toFinset] at this
  exact this.2

/-- The pick is minimal among pool elements `≥ t`. -/
theorem pick_le {t : ℤ} {R : Multiset ℤ} (h : ∃ w ∈ R, t ≤ w)
    {w : ℤ} (hw : w ∈ R) (htw : t ≤ w) : pick t R ≤ w := by
  have hne : (pickSet t R).Nonempty := pickSet_nonempty_iff.mpr h
  rw [pick, dif_pos hne]
  refine (pickSet t R).min'_le w ?_
  simp only [pickSet, Finset.mem_filter, Multiset.mem_toFinset]
  exact ⟨hw, htw⟩

/-! ## ENGINE-2: the one-step closure -/

/-- Dropping the last width is erasing its value from the width-multiset. -/
theorem dropLast_coe_erase (l : List ℤ) (h : l ≠ []) :
    (l.dropLast : Multiset ℤ) = (l : Multiset ℤ).erase (l.getLast h) := by
  have hsplit : l = l.dropLast ++ [l.getLast h] := (List.dropLast_append_getLast h).symm
  set a := l.getLast h with ha
  clear_value a
  have hco : (l : Multiset ℤ) = (l.dropLast : Multiset ℤ) + ([a] : Multiset ℤ) := by
    conv_lhs => rw [hsplit]
    exact (coe_add _ _).symm
  rw [hco, coe_singleton, erase_add_right_pos _ (mem_singleton_self _), erase_singleton,
    Multiset.add_zero]

/-- The head-count of `b` at its last value is strictly below `b.length` (that value excluded). -/
theorem cLt_getLast_lt {b : List ℤ} (h : b ≠ []) :
    cLt (b : Multiset ℤ) (b.getLast h) < b.length := by
  have hmem : b.getLast h ∈ (b : Multiset ℤ) := by
    simp only [mem_coe]; exact List.getLast_mem h
  have hstep := cLt_erase (b : Multiset ℤ) (b.getLast h) (b.getLast h) hmem
  have hcard : card ((b : Multiset ℤ).erase (b.getLast h)) + 1 = b.length := by
    rw [card_erase_add_one hmem, coe_card]
  have hle : cLt ((b : Multiset ℤ).erase (b.getLast h)) (b.getLast h)
      ≤ card ((b : Multiset ℤ).erase (b.getLast h)) := by
    rw [cLt_eq_countP]; exact countP_le_card _ _
  rw [if_neg (lt_irrefl _)] at hstep
  omega

/-- Under `Dom` with `b ≠ []`, some pool element is `≥ b.getLast`. -/
theorem pick_exists {b : List ℤ} {R : Multiset ℤ} (hD : Dom b R) (h : b ≠ []) :
    ∃ w ∈ R, b.getLast h ≤ w := by
  by_contra hcon
  -- every pool element is `< b.getLast`, so `cLt R (getLast) = R.card`
  have hall : ∀ w ∈ R, w < b.getLast h := by
    intro w hw; by_contra hge; exact hcon ⟨w, hw, not_lt.mp hge⟩
  have hfull : cLt R (b.getLast h) = R.card := by
    rw [cLt_eq_countP]; exact countP_eq_card.mpr hall
  have hdom := hD.2 (b.getLast h)
  have hlt := cLt_getLast_lt (b := b) h
  rw [hfull, hD.1] at hdom
  omega

/-- **ENGINE-2 (closure).** Erasing the minimal pool element `≥ b.getLast` and dropping the last
width preserves `Dom`. Here `pick (b.getLast h) R` is the smallest pool element `≥ b.getLast`. -/
theorem engine2_closure {b : List ℤ} {R : Multiset ℤ} (hD : Dom b R) (h : b ≠ []) :
    Dom b.dropLast (R.erase (pick (b.getLast h) R)) := by
  set t := b.getLast h with ht
  set v := pick t R with hv
  have hex : ∃ w ∈ R, t ≤ w := pick_exists hD h
  have hvmem : v ∈ R := pick_mem hex
  have htv : t ≤ v := le_pick hex
  have hvmin : ∀ w ∈ R, t ≤ w → v ≤ w := fun w hw htw => pick_le hex hw htw
  have htmem : t ∈ (b : Multiset ℤ) := by simp only [mem_coe, ht]; exact List.getLast_mem h
  refine ⟨?_, ?_⟩
  · -- cardinalities
    have hlen : (b.dropLast).length + 1 = b.length := by
      conv_rhs => rw [← List.dropLast_append_getLast h]
      rw [List.length_append, List.length_singleton]
    have hcard : (R.erase v).card = (b.dropLast).length := by
      rw [card_erase_of_mem hvmem, hD.1, ← hlen, Nat.pred_succ]
    exact hcard
  · -- head-count domination, per threshold τ
    intro τ
    rw [dropLast_coe_erase b h, ← ht]
    -- forward splits via cLt_erase
    have hRsplit := cLt_erase R v τ hvmem
    have hbsplit := cLt_erase (b : Multiset ℤ) t τ htmem
    have hdom := hD.2 τ
    by_cases hτt : τ ≤ t
    · -- τ ≤ t: both indicators true (v ≥ t ≥ ... so v < τ false; t < τ false)
      rw [if_neg (by omega : ¬ v < τ)] at hRsplit
      rw [if_neg (by omega : ¬ t < τ)] at hbsplit
      omega
    · rw [not_le] at hτt  -- t < τ
      by_cases hτv : τ ≤ v
      · -- t < τ ≤ v: no R-element in [t, v); cLt R τ = cLt R t, and t∈b excluded from cLt b τ
        rw [if_neg (by omega : ¬ v < τ)] at hRsplit
        rw [if_pos (by omega : t < τ)] at hbsplit
        -- key: cLt R τ = cLt R t  (no R-element lies in [t, τ): if t ≤ w then v ≤ w, but τ ≤ v)
        have hRtt : cLt R τ = cLt R t := by
          simp only [cLt]
          refine congrArg card (filter_congr ?_)
          intro w hw
          constructor
          · intro hwτ
            by_contra hwt
            have : t ≤ w := not_lt.mp hwt
            have := hvmin w hw this
            omega
          · intro hwt; omega
        -- t∈b and t<τ: cLt b τ ≥ cLt b t + 1 (the value t counts at τ but not at t)
        have hbtt : cLt (b : Multiset ℤ) t + 1 ≤ cLt (b : Multiset ℤ) τ := by
          have e1 := cLt_erase (b : Multiset ℤ) t t htmem
          rw [if_neg (lt_irrefl _)] at e1
          have e2 := cLt_erase (b : Multiset ℤ) t τ htmem
          rw [if_pos (by omega : t < τ)] at e2
          have hmono := cLt_mono ((b : Multiset ℤ).erase t) (le_of_lt hτt)
          omega
        have hdomt := hD.2 t
        omega
      · rw [not_le] at hτv  -- v < τ
        rw [if_pos (by omega : v < τ)] at hRsplit
        rw [if_pos (by omega : t < τ)] at hbsplit
        omega

/-! ## ENGINE-1: the backward greedy realizer -/

/-- The backward greedy: place, right to left, the minimal pool element `≥` each width. The output
is in position order `q₀, …, q_{n-1}`; `q_{n-1}` (placed first) is the pick for the last width. -/
noncomputable def backwardGreedy (b : List ℤ) (R : Multiset ℤ) : List ℤ :=
  if h : b = [] then []
  else backwardGreedy b.dropLast (R.erase (pick (b.getLast h) R)) ++ [pick (b.getLast h) R]
termination_by b.length
decreasing_by
  rw [List.length_dropLast]
  have : 0 < b.length := List.length_pos_of_ne_nil h
  omega

/-- Unfolding lemma for `backwardGreedy` on a nonempty list. -/
theorem backwardGreedy_cons {b : List ℤ} (h : b ≠ []) (R : Multiset ℤ) :
    backwardGreedy b R
      = backwardGreedy b.dropLast (R.erase (pick (b.getLast h) R)) ++ [pick (b.getLast h) R] := by
  rw [backwardGreedy]; simp only [dif_neg h]

/-- **ENGINE-1(a).** The greedy output is a permutation of the pool. -/
theorem backwardGreedy_perm {b : List ℤ} {R : Multiset ℤ} (hD : Dom b R) :
    (backwardGreedy b R : Multiset ℤ) = R := by
  by_cases h : b = []
  · subst h
    rw [backwardGreedy]
    have : R.card = 0 := by simpa using hD.1
    simp [coe_nil, (card_eq_zero.mp this).symm]
  · have hex : ∃ w ∈ R, b.getLast h ≤ w := pick_exists hD h
    have hvmem : pick (b.getLast h) R ∈ R := pick_mem hex
    rw [backwardGreedy_cons h]
    have hIH := backwardGreedy_perm (engine2_closure hD h)
    rw [show ((backwardGreedy b.dropLast (R.erase (pick (b.getLast h) R)) ++
        [pick (b.getLast h) R] : List ℤ) : Multiset ℤ)
        = (backwardGreedy b.dropLast (R.erase (pick (b.getLast h) R)) : Multiset ℤ)
          + {pick (b.getLast h) R} from by rw [← coe_add]; rfl]
    rw [hIH, Multiset.add_comm, singleton_add, cons_erase hvmem]
termination_by b.length
decreasing_by
  rw [List.length_dropLast]
  have : 0 < b.length := List.length_pos_of_ne_nil h
  omega

/-- **ENGINE-1(b), length.** The greedy output has the same length as `b`. -/
theorem backwardGreedy_length {b : List ℤ} {R : Multiset ℤ} (hD : Dom b R) :
    (backwardGreedy b R).length = b.length := by
  have h := backwardGreedy_perm hD
  have : card (backwardGreedy b R : Multiset ℤ) = card R := by rw [h]
  rw [coe_card] at this
  rw [this, hD.1]

/-- **ENGINE-1(b), positional.** Each placed value is `≥` its width. -/
theorem backwardGreedy_ge {b : List ℤ} {R : Multiset ℤ} (hD : Dom b R) :
    ∀ j (hj : j < b.length),
      b[j] ≤ (backwardGreedy b R)[j]'(by rw [backwardGreedy_length hD]; exact hj) := by
  by_cases h : b = []
  · subst h; intro j hj; simp at hj
  · intro j hj
    have hex : ∃ w ∈ R, b.getLast h ≤ w := pick_exists hD h
    have hdom2 := engine2_closure hD h
    have hlen2 : (b.dropLast).length + 1 = b.length := by
      conv_rhs => rw [← List.dropLast_append_getLast h]
      rw [List.length_append, List.length_singleton]
    set q' := backwardGreedy b.dropLast (R.erase (pick (b.getLast h) R)) with hq'
    have hq'len : q'.length = (b.dropLast).length := backwardGreedy_length hdom2
    set v := pick (b.getLast h) R with hv
    have hcons : backwardGreedy b R = q' ++ [v] := backwardGreedy_cons h R
    -- transport the indexed access across `hcons`
    have htrans := List.getElem_of_eq hcons (i := j)
      (by rw [backwardGreedy_length hD]; exact hj)
    by_cases hjlast : j < (b.dropLast).length
    · -- left part: reduce to the IH on b.dropLast
      have hIH := backwardGreedy_ge hdom2 j hjlast
      have hbj : b[j] = (b.dropLast)[j] := (List.getElem_dropLast hjlast).symm
      have happ : (q' ++ [v])[j]'(by simp [hq'len]; omega) = q'[j]'(by rw [hq'len]; exact hjlast) :=
        List.getElem_append_left (by rw [hq'len]; exact hjlast)
      rw [hbj]
      rw [show (backwardGreedy b R)[j]'(by rw [backwardGreedy_length hD]; exact hj)
            = q'[j]'(by rw [hq'len]; exact hjlast) from htrans.trans happ]
      exact hIH
    · -- last position j = b.length - 1: the pick `v ≥ b.getLast`
      have hjeq : j = (b.dropLast).length := by omega
      have hblast : b[j] = b.getLast h := by
        rw [List.getLast_eq_getElem h]; congr 1; omega
      have hidx : j = q'.length := by rw [hq'len]; exact hjeq
      have happ : (q' ++ [v])[j]'(by simp [hq'len]; omega) = v := by
        rw [List.getElem_append_right (by rw [hidx])]; simp [hidx]
      rw [hblast]
      rw [show (backwardGreedy b R)[j]'(by rw [backwardGreedy_length hD]; exact hj)
            = v from htrans.trans happ]
      exact le_pick hex
termination_by b.length
decreasing_by
  rw [List.length_dropLast]
  have : 0 < b.length := List.length_pos_of_ne_nil h
  omega

/-! ## ENGINE-1(c): suffix-sum helpers -/

/-- Suffix sum past a concatenated tail singleton: drop commutes, then `+ a`. -/
theorem suffixSum_concat (q : List ℤ) (a : ℤ) {j : ℕ} (hj : j ≤ q.length) :
    ((q ++ [a]).drop j).sum = (q.drop j).sum + a := by
  rw [List.drop_append_of_le_length hj, List.sum_append]; simp

/-- The multiset of a `++ cons` is the sum of the two part-multisets plus the inserted singleton. -/
theorem coe_append_cons (a b : List ℤ) (x : ℤ) :
    ((a ++ x :: b : List ℤ) : Multiset ℤ) = (a : Multiset ℤ) + (b : Multiset ℤ) + {x} := by
  ext c
  simp only [coe_count, List.count_append, List.count_cons, count_add, count_singleton, beq_iff_eq]
  rcases eq_or_ne c x with h | h <;> simp [h, eq_comm] <;> omega

/-- The multiset of a list decomposed at position `k`: `↑l = ↑(take k) + ↑(drop (k+1)) + {l[k]}`. -/
theorem coe_decomp (p : List ℤ) (k : ℕ) (x : ℤ)
    (hd : p = p.take k ++ x :: p.drop (k + 1)) :
    (p : Multiset ℤ) = (p.take k : Multiset ℤ) + (p.drop (k + 1) : Multiset ℤ) + {x} := by
  have hco : (p : Multiset ℤ) = ((p.take k ++ x :: p.drop (k + 1) : List ℤ) : Multiset ℤ) :=
    congrArg _ hd
  rw [hco, coe_append_cons]

/-- The multiset of a `set` is the original with the old value erased and the new one added. -/
theorem set_coe_erase (p : List ℤ) (k : ℕ) (u : ℤ) (hk : k < p.length) :
    ((p.set k u : List ℤ) : Multiset ℤ) = ((p : Multiset ℤ).erase p[k]) + {u} := by
  have hset : p.set k u = (p.set k u).take k ++ u :: (p.set k u).drop (k + 1) := by
    rw [List.take_set_of_le (le_refl k), List.drop_set_of_lt (Nat.lt_succ_self k)]
    rw [List.set_eq_take_append_cons_drop]; simp [hk]
  have hsetmul := coe_decomp (p.set k u) k u hset
  have hcdrop : (p.set k u).drop (k + 1) = p.drop (k + 1) :=
    List.drop_set_of_lt (by omega)
  have hctake : (p.set k u).take k = p.take k := List.take_set_of_le (le_refl k)
  rw [hctake, hcdrop] at hsetmul
  have horig : p = p.take k ++ p[k] :: p.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k p, ← List.getElem_cons_drop hk]
  have hpmul := coe_decomp p k p[k] horig
  have herase : (p : Multiset ℤ).erase p[k]
      = (p.take k : Multiset ℤ) + (p.drop (k + 1) : Multiset ℤ) := by
    rw [hpmul, erase_add_right_pos _ (mem_singleton_self _)]; simp
  rw [hsetmul, herase]

/-- Setting one entry to value `u` changes the sum by `u` minus the old entry. -/
theorem sum_set_value (L : List ℤ) (n : ℕ) (u : ℤ) (hn : n < L.length) :
    (L.set n u).sum = L.sum + u - L[n] := by
  have hLself : L.sum
      = (List.take n L).sum + L[n] + (List.drop (n + 1) L).sum := by
    conv_lhs => rw [show L = L.set n L[n] from (List.set_getElem_self hn).symm]
    rw [List.sum_set L n L[n], if_pos (show n < L.length from hn)]
  rw [List.sum_set L n u, if_pos hn, hLself]; ring

/-- The swap inequality: erasing the deficit `v` and adding the larger `u` at position `k` (which
holds `v`) keeps `(p♯.drop j).sum + v ≤ (p.drop j).sum + u`, where `p♯ = p.set k u`. -/
theorem suffixSum_swap_le (p : List ℤ) (k j : ℕ) (u v : ℤ) (hk : k < p.length)
    (hpk : p[k] = v) (hvu : v ≤ u) :
    ((p.set k u).drop j).sum + v ≤ (p.drop j).sum + u := by
  rw [List.drop_set]
  by_cases hkj : k < j
  · rw [if_pos hkj]; linarith
  · rw [if_neg hkj]
    have hlt : k - j < (p.drop j).length := by rw [List.length_drop]; omega
    have hget : (p.drop j)[k - j]'hlt = v := by
      have hidx : j + (k - j) = k := by rw [List.length_drop] at hlt; omega
      have h1 : (p.drop j)[k - j]'hlt = p[j + (k - j)]'(by omega) := List.getElem_drop ..
      simp only [hidx] at h1
      rw [h1]; exact hpk
    rw [sum_set_value (p.drop j) (k - j) u hlt, hget]; linarith

/-! ## ENGINE-1(c): min-suffix-optimality -/

/-- Re-add the larger value after the double erase: `(R.erase u).erase v + {u} = R.erase v`. -/
theorem erase_erase_add {R : Multiset ℤ} {u v : ℤ} (huv : u ≠ v) (hu : u ∈ R) :
    (R.erase u).erase v + {u} = R.erase v := by
  ext c
  simp only [count_add, count_singleton]
  rcases eq_or_ne c u with rfl | hcu <;> rcases eq_or_ne c v with rfl | hcv <;>
    simp_all [count_erase_self, count_erase_of_ne, Multiset.one_le_count_iff_mem]

/-- A competitor for `(b, R)` has the same length as `b`. -/
theorem competitor_length {b : List ℤ} {R : Multiset ℤ} (hD : Dom b R)
    {p : List ℤ} (hp : (p : Multiset ℤ) = R) : p.length = b.length := by
  have : card (p : Multiset ℤ) = card R := by rw [hp]
  rw [coe_card] at this; rw [this, hD.1]

/-- Feasibility of a competitor `p` for widths `b`: each entry dominates its width. -/
def Feasible (b p : List ℤ) : Prop := ∀ i (hb : i < b.length) (hp : i < p.length), b[i] ≤ p[i]

/-- **ENGINE-1(c).** The greedy minimises every suffix sum over all feasible arrangements: for any
permutation `p` of `R` that pointwise dominates `b`, and any `j`, the greedy's suffix sum is `≤`. -/
theorem backwardGreedy_suffix_le {b : List ℤ} {R : Multiset ℤ} (hD : Dom b R) :
    ∀ p : List ℤ, (p : Multiset ℤ) = R → Feasible b p →
      ∀ j, ((backwardGreedy b R).drop j).sum ≤ (p.drop j).sum := by
  intro p hp hfeas j
  by_cases h : b = []
  · -- both lists empty: trivially equal (both sums are 0)
    subst h
    have hpnil : p = [] := by
      have : card (p : Multiset ℤ) = 0 := by rw [hp]; simpa using hD.1
      rw [coe_card, List.length_eq_zero_iff] at this; exact this
    rw [backwardGreedy]; simp [hpnil]
  · -- recursion: peel the last position
    have hbpos : 0 < b.length := List.length_pos_of_ne_nil h
    have hplen : p.length = b.length := competitor_length hD hp
    have hpne : p ≠ [] := by rw [← List.length_pos_iff]; omega
    set t := b.getLast h with ht
    set v := pick t R with hv
    have hex : ∃ w ∈ R, t ≤ w := pick_exists hD h
    have hvmem : v ∈ R := pick_mem hex
    have hvmin : ∀ w ∈ R, t ≤ w → v ≤ w := fun w hw htw => pick_le hex hw htw
    -- competitor's last value `u` and prefix `p'`
    set u := p.getLast hpne with hu
    set p' := p.dropLast with hp'def
    have hpsplit : p = p' ++ [u] := (List.dropLast_append_getLast hpne).symm
    -- feasibility at the last position: `t ≤ u`
    have htu : t ≤ u := by
      have hlast := hfeas (b.length - 1) (by omega) (by omega)
      rw [List.getLast_eq_getElem h] at ht
      have hpu : p[b.length - 1]'(by omega) = u := by
        rw [hu, List.getLast_eq_getElem hpne]
        congr 1; omega
      rw [ht, ← hpu]; exact hlast
    have huR : u ∈ R := by
      rw [← hp]; rw [mem_coe, hu]; exact List.getLast_mem hpne
    have hvu : v ≤ u := hvmin u huR htu
    -- greedy unfolds; suffix splice via `suffixSum_concat`
    have hgcons : backwardGreedy b R = backwardGreedy b.dropLast (R.erase v) ++ [v] :=
      backwardGreedy_cons h R
    set q' := backwardGreedy b.dropLast (R.erase v) with hq'def
    have hdom2 : Dom b.dropLast (R.erase v) := engine2_closure hD h
    have hq'len : q'.length = (b.dropLast).length := backwardGreedy_length hdom2
    have hp'add : (p : Multiset ℤ) = (p' : Multiset ℤ) + {u} := by
      have hcc : ((p' ++ u :: ([] : List ℤ) : List ℤ) : Multiset ℤ)
          = (p' : Multiset ℤ) + (([] : List ℤ) : Multiset ℤ) + {u} := coe_append_cons _ _ _
      have hpco : (p : Multiset ℤ) = ((p' ++ u :: ([] : List ℤ) : List ℤ) : Multiset ℤ) :=
        congrArg _ hpsplit
      rw [hpco, hcc]; simp
    have hp'mul : (p' : Multiset ℤ) = R.erase u := by
      rw [← hp, hp'add, add_comm, singleton_add, erase_cons_head]
    have hp'len : p'.length = (b.dropLast).length := by
      rw [hp'def, List.length_dropLast, hplen, List.length_dropLast]
    -- feasibility of `p'` for `b.dropLast` (each surviving position keeps `b[i] ≤ p[i]`)
    have hbdl_len : (b.dropLast).length = b.length - 1 := List.length_dropLast
    have hp'feas : Feasible b.dropLast p' := by
      intro i hbi hpi
      have hib : i < b.length := by rw [hbdl_len] at hbi; omega
      have hip : i < p.length := by rw [hp'len, hbdl_len] at hpi; omega
      have hb' : (b.dropLast)[i]'hbi = b[i]'hib := List.getElem_dropLast hbi
      have hp'' : p'[i]'hpi = p[i]'hip := List.getElem_dropLast hpi
      rw [hb', hp'']; exact hfeas i hib hip
    -- suffix splice for the competitor: `(p.drop j).sum = (p'.drop j).sum + u` when `j ≤ p'.length`
    have hsuffix_p : ∀ j, j ≤ p'.length → (p.drop j).sum = (p'.drop j).sum + u := by
      intro j hj
      conv_lhs => rw [hpsplit]
      exact suffixSum_concat p' u hj
    have hsuffix_q : ∀ j, j ≤ q'.length → ((backwardGreedy b R).drop j).sum
        = (q'.drop j).sum + v := by
      intro j hj
      conv_lhs => rw [hgcons]
      exact suffixSum_concat q' v hj
    -- the swapped competitor for `(b.dropLast, R.erase v)` and its IH bound
    -- key step: `q'.drop j' .sum + v ≤ p'.drop j' .sum + u` for every `j'`
    have hstep : ∀ j', (q'.drop j').sum + v ≤ (p'.drop j').sum + u := by
      intro j'
      by_cases huv : u = v
      · -- no swap: `p'` is already a competitor for `R.erase v`
        have hp'mulv : (p' : Multiset ℤ) = R.erase v := by rw [hp'mul, huv]
        have hIH := backwardGreedy_suffix_le hdom2 p' hp'mulv hp'feas j'
        rw [← hq'def] at hIH; rw [huv]; linarith
      · -- swap one `v` in `p'` for `u`, getting `p♯` with multiset `R.erase v`
        have hvne : v ≠ u := Ne.symm huv
        have hvp' : v ∈ p' := by
          rw [← mem_coe, hp'mul]; exact (mem_erase_of_ne hvne).mpr hvmem
        set k := p'.idxOf v with hk
        have hklt : k < p'.length := List.idxOf_lt_length_iff.mpr hvp'
        have hpk : p'[k]'hklt = v := List.getElem_idxOf hklt
        set ph := p'.set k u with hph
        have hphlen : ph.length = p'.length := List.length_set
        have hphmul : (ph : Multiset ℤ) = R.erase v := by
          rw [hph, set_coe_erase p' k u hklt, hpk, hp'mul, erase_erase_add (Ne.symm hvne) huR]
        have hphfeas : Feasible b.dropLast ph := by
          intro i hbi hpi
          have hpi' : i < p'.length := by rw [← hphlen]; exact hpi
          by_cases hik : i = k
          · -- the swapped position: width ≤ p'[k]=v ≤ u = ph[k]
            subst hik
            have hph_i : ph[k]'hpi = u := List.getElem_set_self _
            rw [hph_i]
            calc (b.dropLast)[k]'hbi ≤ p'[k]'hpi' := hp'feas k hbi hpi'
              _ = v := hpk
              _ ≤ u := hvu
          · -- unchanged position: ph[i] = p'[i]
            have hph_i : ph[i]'hpi = p'[i]'hpi' := List.getElem_set_ne (Ne.symm hik) _
            rw [hph_i]; exact hp'feas i hbi hpi'
        have hIH := backwardGreedy_suffix_le hdom2 ph hphmul hphfeas j'
        rw [← hq'def] at hIH
        -- IH : `q'` suffix ≤ `ph` suffix; swap : `ph` suffix `+ v` ≤ `p'` suffix `+ u`
        have hswap := suffixSum_swap_le p' k j' u v hklt hpk hvu
        rw [← hph] at hswap
        linarith
    -- conclude: splice `hstep` through the suffix decompositions
    by_cases hjle : j ≤ (b.dropLast).length
    · have hjq : j ≤ q'.length := by rw [hq'len]; exact hjle
      have hjp : j ≤ p'.length := by rw [hp'len]; exact hjle
      rw [hsuffix_q j hjq, hsuffix_p j hjp]
      have := hstep j; linarith
    · -- `j > n-1`: both suffixes are empty
      rw [not_le] at hjle
      have hjbig : b.length ≤ j := by rw [hbdl_len] at hjle; omega
      have hq0 : ((backwardGreedy b R).drop j).sum = 0 := by
        rw [List.drop_eq_nil_of_le (by rw [backwardGreedy_length hD]; omega)]; simp
      have hp0 : (p.drop j).sum = 0 := by
        rw [List.drop_eq_nil_of_le (by rw [hplen]; omega)]; simp
      rw [hq0, hp0]
termination_by b.length
decreasing_by
  all_goals (rw [List.length_dropLast]; have : 0 < b.length := List.length_pos_of_ne_nil h; omega)

end DLNFibre.DLN.RLCT.BGEngine

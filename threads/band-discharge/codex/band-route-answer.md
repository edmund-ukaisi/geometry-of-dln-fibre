**Ranking**
1. **A, but encode `forwardMax` proof-free**: ~160-260 lines, low risk. `Classical` kills decidability; no exchange theorem; winner.
2. **D: black-box witness lemma** `∃ p, perm ∧ feasible ∧ prefix_good`: ~35-70 band-glue lines if already proved; otherwise just A hidden behind one lemma.
3. **B direct on `backwardGreedy`**: ~350-600 lines, medium/high risk. Right-recursion fights first-prefix arithmetic; likely redoes witness logic implicitly.
4. **C abstract exchange**: ~600-1000 lines, high risk. Avoids `Decidable`, but buys list-position swap/erase bookkeeping.

**Winner Skeleton**
```lean
noncomputable section
open Classical

def liveCand (t : ℤ) (bs : List ℤ) (R : Multiset ℤ) : Finset ℤ := by
  classical
  exact R.toFinset.filter (fun w => t ≤ w ∧ Dom bs (R.erase w))

def forwardHead (t : ℤ) (bs : List ℤ) (R : Multiset ℤ) : ℤ := by
  classical
  exact if hs : (liveCand t bs R).Nonempty
    then (liveCand t bs R).max' hs
    else 0

def forwardMax : List ℤ → Multiset ℤ → List ℤ
| [], _ => []
| t :: bs, R =>
    let w := forwardHead t bs R
    w :: forwardMax bs (R.erase w)
termination_by b R => b.length
decreasing_by simp

lemma feasible_perm_dom
    {b p : List ℤ} {S : Multiset ℤ}
    (hpS : (p : Multiset ℤ) = S)
    (hlen : p.length = b.length)
    (hfeas : Feasible b p) :
    Dom b S := by
  -- count proof: p[i] < τ implies b[i] < τ by hfeas + lt_of_le_of_lt.
  -- Use your cLt/list-count API; no greedy math here.
  sorry

lemma liveCand_nonempty {t bs R} (h : Dom (t :: bs) R) :
    (liveCand t bs R).Nonempty := by
  let q := backwardGreedy (t :: bs) R
  have hlen := backwardGreedy_length h
  have hperm := backwardGreedy_perm h
  -- take w = q[0], tail = q.drop 1 / q.tail.
  -- hge at index 0 gives t ≤ w.
  -- hge at succ indices gives Feasible bs q.tail.
  -- hperm gives (q.tail : Multiset ℤ) = R.erase w.
  -- Then feasible_perm_dom gives Dom bs (R.erase w).
  -- Finish by Finset.mem_filter + Multiset.mem_toFinset
  sorry

lemma forwardHead_live {t bs R} (h : Dom (t :: bs) R) :
    forwardHead t bs R ∈ liveCand t bs R := by
  classical
  unfold forwardHead
  have hs := liveCand_nonempty h
  -- simp [hs]; exact Finset.max'_mem ...  -- verify exact lemma name
  sorry

lemma forwardHead_ge {t bs R} (h : Dom (t :: bs) R) :
    t ≤ forwardHead t bs R := by
  exact (Finset.mem_filter.mp (forwardHead_live h)).2.1

lemma forwardHead_dom {t bs R} (h : Dom (t :: bs) R) :
    Dom bs (R.erase (forwardHead t bs R)) := by
  exact (Finset.mem_filter.mp (forwardHead_live h)).2.2

lemma live_le_forwardHead {t bs R u}
    (h : Dom (t :: bs) R)
    (huR : u ∈ R) (htu : t ≤ u) (huD : Dom bs (R.erase u)) :
    u ≤ forwardHead t bs R := by
  classical
  have hu : u ∈ liveCand t bs R := by
    -- simp [liveCand, huR, htu, huD]
    sorry
  unfold forwardHead
  have hs := liveCand_nonempty h
  -- simp [hs]; exact Finset.le_max' ... hu  -- verify exact lemma name
  sorry

lemma forwardMax_perm {b R} (h : Dom b R) :
    (forwardMax b R : Multiset ℤ) = R := by
  induction b generalizing R with
  | nil =>
      -- h.1 : R.card = 0; use lemma of form Multiset.card_eq_zero.mp
      sorry
  | cons t bs ih =>
      set w := forwardHead t bs R
      have hwD : Dom bs (R.erase w) := by simpa [w] using forwardHead_dom h
      have htail := ih hwD
      have hwR : w ∈ R := by
        exact (Finset.mem_filter.mp (by simpa [w] using forwardHead_live h)).1
      -- simp [forwardMax, w, htail, hwR]; use erase-cons lemma, verify name.
      sorry

lemma forwardMax_feasible {b R} (h : Dom b R) :
    Feasible b (forwardMax b R) := by
  induction b generalizing R with
  | nil => intro i hb hp; cases hb
  | cons t bs ih =>
      intro i hb hp
      cases i with
      | zero => simpa [forwardMax] using forwardHead_ge h
      | succ i =>
          -- reduce indexing through cons; apply ih (forwardHead_dom h)
          sorry

lemma forwardMax_prefix_band (M) (j : Fin L) :
    let p := forwardMax (Mwidths M) (Ymulti M)
    (∑ i in Finset.range (j.val + 2), Mseq M i) - (admBound M j : ℤ)
      ≤ (p.take (j.val + 1)).sum := by
  -- Stronger theorem by induction on k = selected prefix length.
  -- Step for t :: bs: rewrite take on cons, use IH on bs/R.erase w,
  -- and lower-bound w via live_le_forwardHead.
  -- The live candidate and numeric lower bound are exactly good_floor_core.
  sorry

lemma band (M) (j : Fin L) :
    (∑ i in Finset.range (j.val + 2), Mseq M i) - (admBound M j : ℤ)
      ≤ ∑ i in Finset.range (j.val + 1), qStar M i := by
  let b := Mwidths M
  let R := Ymulti M
  let q := backwardGreedy b R
  let p := forwardMax b R
  have hpR : (p : Multiset ℤ) = R := forwardMax_perm hDom
  have hpF : Feasible b p := forwardMax_feasible hDom
  have hsuf := backwardGreedy_suffix_le hDom p hpR hpF (j.val + 1)
  have hpref := forwardMax_prefix_band M j
  -- Convert prefix lower for p to drop upper for p using:
  -- List.take_append_drop, List.sum_append, total sum from hpR.
  -- Then hsuf gives drop upper for q.
  -- Convert q drop upper back to q prefix lower using total sum from backwardGreedy_perm.
  -- Convert `∑ range, qStar` to `(q.take _).sum` by local lemma:
  --   sum_range_getD_eq_take_sum, proved by induction using Finset.sum_range_succ.
  linarith
```

**Biggest Gotcha**
Do **not** make `forwardMax` take `h : Dom b R` as an argument. Proof-dependent recursive choices will make rewrites brittle. Define the total proof-free function with an empty fallback, then prove specs only under `Dom`. The `Classical` decidability issue disappears, and all later simp/induction steps see the same head value.
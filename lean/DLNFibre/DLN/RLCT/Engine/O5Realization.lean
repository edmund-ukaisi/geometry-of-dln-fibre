import DLNFibre.DLN.RLCT.Engine.ClearableReify
import DLNFibre.DLN.RLCT.Engine.NumDivFlatBound
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverPath

/-!
# `DLNFibre.DLN.RLCT.Engine.O5Realization` — the o5-∈ realization arc (cert §3 + §4)

Proof of the o5-∈ crux `o5_core` (a realized `Mval`-minimizer), pnp-o5 cert §3–4.

* **§3 (this file): every `Mval`-minimizer of `Adm` is `Clearable`** — the envelope-splice: a
  non-clearable admissible profile has a strictly cheaper admissible sibling (replace its
  pre-saturation prefix by the running-min envelope, which contributes `0` to `Mval` while the
  differing prefix contributes `> 0`). Hence `tStar M` is Clearable.
* **§4 (the flagged brick, D§ii/iii): a Clearable profile is realized** as a `t̃ = 0` leaf divisor —
  the steering rule + anchor descent invariant, reusing the banked pull-ordering. This closes
  `o5_core` (`EngineConstruction`, sorried).

MINIMIZER-ONLY (`tStar`), NOT `⊇ Clearable-Adm` (R7 = `realizedProfiles_eq_clearableAdm`).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ}

/-- **On the admissible cone, every coord is bounded by the running-min width**
`a m ≤ widthMinUpto M (m+1) = min(M⁽¹⁾ … M⁽ᵐ⁺¹⁾)` — the cert's `aⁱ ≤ r_{i+1}` bound, DERIVED from
weak-decrease + the block bounds of `admPred` (for each `i ≤ m+1`, `a m ≤ a_{i-1} ≤ M i`). -/
theorem adm_le_widthMinUpto (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (ha : a ∈ Adm M) (m : Fin L) :
    a m ≤ widthMinUpto M (m.val + 1) := by
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le m.val) m.isLt
  have hone : ((1 : Fin (L + 1)) : ℕ) = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hbound, hdec, _⟩ := (Finset.mem_filter.1 ha).2
  rw [widthMinUpto, Finset.le_inf'_iff]
  intro i hi
  rw [Finset.mem_filter] at hi
  have hile : (i : ℕ) ≤ m.val + 1 := hi.2
  by_cases hi0 : (i : ℕ) = 0
  · have h0m : (⟨0, hL⟩ : Fin L) ≤ m := by simp [Fin.le_def]
    have hdm := hdec ⟨0, hL⟩ m h0m
    have hb0 := hbound ⟨0, hL⟩
    rw [admBound, if_pos rfl] at hb0
    have hle0 : a m ≤ M 0 := le_trans hdm (le_trans hb0 (min_le_left _ _))
    have hiM : M i = M 0 := by congr 1; exact Fin.ext (by rw [hi0]; rfl)
    omega
  · have him1 : i.val - 1 < L := by omega
    have hle : (⟨i.val - 1, him1⟩ : Fin L) ≤ m := by simp only [Fin.le_def]; omega
    have hdm := hdec ⟨i.val - 1, him1⟩ m hle
    have hb := hbound ⟨i.val - 1, him1⟩
    by_cases hi1 : i.val - 1 = 0
    · rw [admBound, if_pos hi1] at hb
      have hival : (i : ℕ) = 1 := by omega
      have hiM : M i = M 1 := congrArg M (Fin.ext (by rw [hival, hone]))
      have hle1 : a m ≤ M 1 := le_trans hdm (le_trans hb (min_le_right _ _))
      omega
    · rw [admBound, if_neg hi1] at hb
      have hiM : M (⟨i.val - 1, him1⟩ : Fin L).succ = M i := by
        congr 1; apply Fin.ext; simp only [Fin.val_succ]; omega
      rw [hiM] at hb
      exact le_trans hdm hb

/-- Each `Mval` summand is `≥ 0` on the admissible cone (both factors nonneg: weak-decrease gives
`T k ≤ tPrev`, the block bound gives `T k ≤ M k.succ`). -/
theorem mval_term_nonneg (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (k : Fin L) :
    0 ≤ (tPrev M T k - (T k : ℤ)) * ((M k.succ : ℤ) - (T k : ℤ)) := by
  have h1 : (0 : ℤ) ≤ tPrev M T k - (T k : ℤ) := by
    have := tStar_le_tPrev M T hT k; linarith
  have h2 : (0 : ℤ) ≤ (M k.succ : ℤ) - (T k : ℤ) := by
    have := tStar_le_Msucc M T hT k; linarith
  exact mul_nonneg h1 h2

/-- **The envelope value** at coord `k` — `widthMinUpto M (k+1) = r_{k+2}` (`= runMinWidth M k`);
the componentwise-maximal `Mval`-zeroing prefix. -/
def envVal (M : Fin (L + 1) → ℕ) (k : Fin L) : ℕ := widthMinUpto M (k.val + 1)

/-- **Prefix forces envelope** (cert §3 step 2, the induction): if every `Mval` summand up to `i`
vanishes on an admissible `T`, then `T` equals the running-min envelope up to `i`. Strong induction on
`k`: the summand `(tPrev − T_k)(M_{k+1} − T_k) = 0` gives `T_k = tPrev_k` or `T_k = M_{k+1}`; with the
IH `T_{k-1} = widthMinUpto M k` (so `tPrev_k = widthMinUpto M k`) and the bound `T_k ≤ widthMinUpto M
(k+1) = min(widthMinUpto M k, M_{k+1})`, either case forces `T_k = widthMinUpto M (k+1) = envVal k`. -/
theorem prefix_forces_env (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (i : ℕ)
    (hz : ∀ k : Fin L, k.val ≤ i → (tPrev M T k - (T k : ℤ)) * ((M k.succ : ℤ) - (T k : ℤ)) = 0) :
    ∀ k : Fin L, k.val ≤ i → T k = envVal M k := by
  have key : ∀ n : ℕ, ∀ k : Fin L, k.val = n → k.val ≤ i → T k = envVal M k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hkn hk
      have hzk := hz k hk
      rcases mul_eq_zero.1 hzk with hfac | hfac
      · -- `tPrev_k = T_k`
        have htp : tPrev M T k = (T k : ℤ) := by linarith
        by_cases hk0 : k.val = 0
        · -- `tPrev_0 = M 0`, and `widthMinUpto M 1 ≤ M 0`
          have htp0 : tPrev M T k = (M 0 : ℤ) := by unfold tPrev; rw [if_pos hk0]
          have hle : widthMinUpto M (k.val + 1) ≤ M 0 := by
            have : widthMinUpto M (k.val + 1) ≤ widthMinUpto M 0 :=
              widthMinUpto_mono M (Nat.zero_le _)
            rwa [widthMinUpto_zero] at this
          have heq : (T k : ℤ) = (M 0 : ℤ) := by rw [← htp0, htp]
          have hTk : T k = M 0 := by exact_mod_cast heq
          have hb := adm_le_widthMinUpto M T hT k
          show T k = widthMinUpto M (k.val + 1); omega
        · -- `tPrev_k = T_{k-1} = widthMinUpto M k` (IH); `widthMinUpto M (k+1) = min(·, M_{k+1})`
          have hkm1 : k.val - 1 < L := by omega
          have hIH : T ⟨k.val - 1, hkm1⟩ = envVal M ⟨k.val - 1, hkm1⟩ :=
            ih (k.val - 1) (by omega) ⟨k.val - 1, hkm1⟩ rfl (Nat.le_trans (Nat.sub_le k.val 1) hk)
          have henv1 : envVal M ⟨k.val - 1, hkm1⟩ = widthMinUpto M k.val := by
            unfold envVal; congr 1; simp only; omega
          have htpk : tPrev M T k = (widthMinUpto M k.val : ℤ) := by
            unfold tPrev; rw [if_neg hk0]
            have hh : T ⟨k.val - 1, by omega⟩ = widthMinUpto M k.val := by rw [hIH, henv1]
            exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hh
          have hsucc : widthMinUpto M (k.val + 1)
              = min (widthMinUpto M k.val) (M ⟨k.val + 1, by omega⟩) :=
            widthMinUpto_succ M (by omega)
          have hTk : T k = widthMinUpto M k.val := by
            have heq : (T k : ℤ) = (widthMinUpto M k.val : ℤ) := by rw [← htpk, htp]
            exact_mod_cast heq
          have hTkle := adm_le_widthMinUpto M T hT k
          rw [hsucc] at hTkle
          show T k = widthMinUpto M (k.val + 1); rw [hsucc, hTk]; omega
      · -- `M_{k+1} = T_k`, so `T_k = M_{k+1} ≥ widthMinUpto M (k+1)`
        have hms : (M k.succ : ℤ) = (T k : ℤ) := by linarith
        have hsuccM : M k.succ = M ⟨k.val + 1, by omega⟩ := congrArg M (Fin.ext (by simp))
        have hsucc : widthMinUpto M (k.val + 1)
            = min (widthMinUpto M k.val) (M ⟨k.val + 1, by omega⟩) :=
          widthMinUpto_succ M (by omega)
        have hTk : T k = M ⟨k.val + 1, by omega⟩ := by
          have heq : (T k : ℤ) = (M ⟨k.val + 1, by omega⟩ : ℤ) := by rw [← hms, hsuccM]
          exact_mod_cast heq
        have hle := adm_le_widthMinUpto M T hT k
        show T k = widthMinUpto M (k.val + 1); rw [hsucc]; omega
  intro k hk
  exact key k.val k rfl hk

/-- The envelope value is within its block bound: `envVal M k ≤ admBound M k`. Via the banked
`runMinWidth_le_admBound` bridge (`envVal M k = widthMinUpto M (k+1) = runMinWidth M k`), avoiding the
`OfNat Fin` literal reduction the direct `k = 0` split hit. -/
theorem envVal_le_admBound (M : Fin (L + 1) → ℕ) (k : Fin L) : envVal M k ≤ admBound M k := by
  simpa only [envVal, runMinWidth_eq_widthMinUpto] using runMinWidth_le_admBound M k

/-- **The envelope-spliced profile** (cert §3 step 3): the running-min envelope on coords `≤ i`, the
original `a` beyond. Replacing a non-clearable prefix by the envelope is the strictly-cheaper sibling. -/
def spliceEnv (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (i : ℕ) : Fin L → ℕ :=
  fun k => if k.val ≤ i then widthMinUpto M (k.val + 1) else a k

/-- Every coord of the splice is `≤` the envelope value (equality on `≤ i`; `a k ≤ envVal` beyond, by
`adm_le_widthMinUpto`). -/
theorem spliceEnv_le_envVal (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (ha : a ∈ Adm M) (i : ℕ)
    (k : Fin L) : spliceEnv M a i k ≤ envVal M k := by
  unfold spliceEnv envVal
  by_cases hk : k.val ≤ i
  · rw [if_pos hk]
  · rw [if_neg hk]; exact adm_le_widthMinUpto M a ha k

/-- **The envelope splice is admissible** (cert §3 step 3a). Block bounds: each coord `≤ envVal ≤
admBound`. Weak-decrease: envelope-antitone on the prefix, `a`-antitone beyond, and at the seam the
saturated descent (`a i = widthMinUpto M j.val = envVal i > a j ≥ a k'`) keeps it monotone. Last
coord `0`: `L−1 > i` (since `j = i+1 ≤ L−1`), so it is `a (L−1) = 0`. -/
theorem spliceEnv_mem_Adm (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (ha : a ∈ Adm M) {i j : Fin L}
    (hij : i.val + 1 = j.val) (hdesc : a j < a i) (hsat : a i = widthMinUpto M j.val) :
    spliceEnv M a i.val ∈ Adm M := by
  obtain ⟨_, hdec, hlast⟩ := (Finset.mem_filter.1 ha).2
  -- envVal at i equals a i (saturation): envVal M i = widthMinUpto M (i+1) = widthMinUpto M j.val
  have henvi : envVal M i = a i := by unfold envVal; rw [show i.val + 1 = j.val from hij, ← hsat]
  have hbb : ∀ k : Fin L, spliceEnv M a i.val k ≤ admBound M k := fun k =>
    le_trans (spliceEnv_le_envVal M a ha i.val k) (envVal_le_admBound M k)
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, hbb, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro k; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hbb k)
  · -- weak-decrease
    intro p q hpq
    have hpqv : p.val ≤ q.val := hpq
    unfold spliceEnv
    by_cases hqi : q.val ≤ i.val
    · -- both in the envelope prefix: envelope antitone
      rw [if_pos (le_trans hpqv hqi), if_pos hqi]
      exact widthMinUpto_mono M (by omega)
    · rw [if_neg hqi]
      by_cases hpi : p.val ≤ i.val
      · -- seam: p in prefix, q beyond. a q ≤ a j ≤ a i = widthMinUpto M j.val ≤ widthMinUpto M (p+1)
        rw [if_pos hpi]
        have hqj : j ≤ q := by rw [Fin.le_def]; omega
        calc a q ≤ a j := hdec j q hqj
          _ ≤ a i := Nat.le_of_lt hdesc
          _ = widthMinUpto M j.val := hsat
          _ ≤ widthMinUpto M (p.val + 1) := widthMinUpto_mono M (by omega)
      · -- both beyond: a antitone
        rw [if_neg hpi]; exact hdec p q hpq
  · -- last coord 0
    intro k hk
    have hik : i.val < k.val := by omega
    unfold spliceEnv; rw [if_neg (by omega)]; exact hlast k hk

/-- **Envelope summand vanishes** (cert §3 step 1): on the splice prefix (`k ≤ i`), the `k`th `Mval`
summand is `0` — `spliceEnv k = widthMinUpto M (k+1) = min(widthMinUpto M k, M k.succ)` kills one
factor (its predecessor is `widthMinUpto M k`). -/
theorem spliceEnv_term_zero (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (i : ℕ) (k : Fin L)
    (hk : k.val ≤ i) :
    (tPrev M (spliceEnv M a i) k - (spliceEnv M a i k : ℤ))
      * ((M k.succ : ℤ) - (spliceEnv M a i k : ℤ)) = 0 := by
  have hsk : spliceEnv M a i k = widthMinUpto M (k.val + 1) := by unfold spliceEnv; rw [if_pos hk]
  have htp : tPrev M (spliceEnv M a i) k = (widthMinUpto M k.val : ℤ) := by
    unfold tPrev
    by_cases hk0 : k.val = 0
    · rw [if_pos hk0, hk0]; exact_mod_cast (widthMinUpto_zero M).symm
    · rw [if_neg hk0]
      have hcond : (⟨k.val - 1, by omega⟩ : Fin L).val ≤ i := by simp only [Fin.val_mk]; omega
      have hval : (⟨k.val - 1, by omega⟩ : Fin L).val + 1 = k.val := by simp only [Fin.val_mk]; omega
      have hsplit : spliceEnv M a i ⟨k.val - 1, by omega⟩ = widthMinUpto M k.val := by
        unfold spliceEnv; rw [if_pos hcond, hval]
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hsplit
  have hsucc : widthMinUpto M (k.val + 1)
      = min (widthMinUpto M k.val) (M k.succ) := by
    rw [show M k.succ = M (⟨k.val + 1, by omega⟩ : Fin (L + 1)) from
        congrArg M (Fin.ext (by simp))]
    exact widthMinUpto_succ M (by omega)
  rw [hsk, htp, hsucc]
  push_cast [Nat.cast_min]
  rcases le_total (widthMinUpto M k.val : ℤ) (M k.succ : ℤ) with h | h
  · rw [min_eq_left h]; ring
  · rw [min_eq_right h]; ring

/-- **Beyond the splice the summand is unchanged** (cert §3 step 3b): for `k > i` the splice equals `a`
there, and at the seam `k = j` the predecessor `spliceEnv i = widthMinUpto M j.val = a i` by
saturation, so `tPrev` matches too. -/
theorem spliceEnv_term_eq (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) {i j : Fin L}
    (hij : i.val + 1 = j.val) (hsat : a i = widthMinUpto M j.val) (k : Fin L) (hk : i.val < k.val) :
    (tPrev M (spliceEnv M a i.val) k - (spliceEnv M a i.val k : ℤ))
      * ((M k.succ : ℤ) - (spliceEnv M a i.val k : ℤ))
    = (tPrev M a k - (a k : ℤ)) * ((M k.succ : ℤ) - (a k : ℤ)) := by
  have hsk : spliceEnv M a i.val k = a k := by unfold spliceEnv; rw [if_neg (by omega)]
  have htp : tPrev M (spliceEnv M a i.val) k = tPrev M a k := by
    unfold tPrev
    by_cases hk0 : k.val = 0
    · rw [if_pos hk0, if_pos hk0]
    · rw [if_neg hk0, if_neg hk0]
      by_cases hj : k.val = j.val
      · -- seam: predecessor is the splice's coord i = envVal i = a i
        have hpred : spliceEnv M a i.val ⟨k.val - 1, by omega⟩ = a i := by
          unfold spliceEnv; rw [if_pos (by simp only; omega)]
          have : (⟨k.val - 1, by omega⟩ : Fin L).val + 1 = j.val := by simp only; omega
          rw [show widthMinUpto M ((⟨k.val - 1, by omega⟩ : Fin L).val + 1) = widthMinUpto M j.val
                from by rw [this], ← hsat]
        have hai : a ⟨k.val - 1, by omega⟩ = a i := by congr 1; apply Fin.ext; simp only; omega
        rw [hpred, hai]
      · -- k > j: predecessor is beyond i, so splice = a there
        have hpred : spliceEnv M a i.val ⟨k.val - 1, by omega⟩ = a ⟨k.val - 1, by omega⟩ := by
          unfold spliceEnv; rw [if_neg (by simp only; omega)]
        rw [hpred]
  rw [hsk, htp]

/-- **The envelope splice is strictly cheaper** (cert §3 step 3c): for a non-clearable admissible `a`
with a saturated descent at `(i, j)` and a bad prefix coord, `Mval (spliceEnv M a i) < Mval a`. The
prefix summands drop to `0` (`spliceEnv_term_zero`) from a `> 0` bad coord (contrapositive of
`prefix_forces_env`); boundary + suffix are unchanged (`spliceEnv_term_eq`). -/
theorem mval_spliceEnv_lt (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (ha : a ∈ Adm M) {i j : Fin L}
    (hij : i.val + 1 = j.val) (hsat : a i = widthMinUpto M j.val)
    (hbad : ∃ m : Fin L, m.val ≤ i.val ∧ a m ≠ widthMinUpto M (m.val + 1)) :
    Mval M (spliceEnv M a i.val) < Mval M a := by
  unfold Mval
  refine Finset.sum_lt_sum (fun k _ => ?_) ?_
  · by_cases hk : k.val ≤ i.val
    · rw [spliceEnv_term_zero M a i.val k hk]; exact mval_term_nonneg M a ha k
    · exact le_of_eq (spliceEnv_term_eq M a hij hsat k (by omega))
  · -- ∃ k ≤ i with the a-summand strictly positive (else prefix_forces_env forces the envelope at m)
    obtain ⟨m, hmi, hmne⟩ := hbad
    by_contra hcon
    push_neg at hcon
    have hz : ∀ k : Fin L, k.val ≤ i.val →
        (tPrev M a k - (a k : ℤ)) * ((M k.succ : ℤ) - (a k : ℤ)) = 0 := by
      intro k hk
      have hle := hcon k (Finset.mem_univ k)
      by_cases hki : k.val ≤ i.val
      · rw [spliceEnv_term_zero M a i.val k hki] at hle
        exact le_antisymm hle (mval_term_nonneg M a ha k)
      · exact absurd hk hki
    have := prefix_forces_env M a ha i.val hz m hmi
    exact hmne this

/-- **Every `Mval`-minimizer of `Adm` is `Clearable`** (cert §3, the envelope-splice corollary): if `a`
is admissible and minimizes `Mval` over `Adm`, then `a` is `Clearable`. A non-clearable `a` has a
strictly cheaper admissible sibling (`mval_spliceEnv_lt` + `spliceEnv_mem_Adm`), contradicting
minimality. Kept over `ℤ`; no `0 < L` needed (`L = 0` is vacuously clearable). -/
theorem clearable_of_minimizer (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (ha : a ∈ Adm M)
    (hmin : ∀ b ∈ Adm M, Mval M a ≤ Mval M b) : Clearable M a := by
  intro i j hij hdesc hsat m hmi
  by_contra hne
  have hbad : ∃ m : Fin L, m.val ≤ i.val ∧ a m ≠ widthMinUpto M (m.val + 1) := ⟨m, hmi, hne⟩
  have hlt := mval_spliceEnv_lt M a ha hij hsat hbad
  have hmem := spliceEnv_mem_Adm M a ha hij hdesc hsat
  exact absurd (hmin _ hmem) (not_le.mpr hlt)

/-- **`tStar M` is `Clearable`** (cert §3, the load-bearing instance): the banked `Mval`-minimizer is
clearable, so its realization (§4) gives `minAdm ∈ terminalExponents`. -/
theorem clearable_tStar (M : Fin (L + 1) → ℕ) : Clearable M (tStar M) :=
  clearable_of_minimizer M (tStar M) (tStar_mem M) (fun b hb => by
    rw [Mval_tStar_eq_inf']; exact Finset.inf'_le _ hb)

/-! ## §4 — realizing the clearable minimizer `tStar` as a `t̃ = 0` leaf divisor

The construction-tracing half (cert §4). `tStar M` is `Clearable` (`clearable_tStar`, §3), so the
steering rule `R(tStar)` (take case-1(1) iff the target level `ℓ > tStar^S`, else 1(2); case-2/rollover
forced) traces a deterministic root→leaf path IN THE BUILT TREE (the fixed Def-4-minimal chooser
`conOracle`; item-1: no non-minimal pick is ever needed) whose terminal leaf carries `tStar` as a
`t̃ = 0` analytic divisor. The anchor-descent invariant (cert §4, Lean-ready) tracks one divisor `A`:
born by case-2 at layer `b(tStar)`, maintained (plateau/descent) through the clearing layers, becoming
`t̃ = 0` with profile `tStar` at the leaf. The one flagged brick — the intra-layer pull-ordering (`A`
lands at EXACTLY `tStar^S`, Def-4-least at its level) — reuses the banked o4 `LiveHeadDom` /
`chooserTotalOnChain_of_sameLevel` / `step1_dominates`. -/

/-- **Reading a `t̃ = 0` divisor off the terminal leaf.** If a state `s` carries a divisor `A` with
`s.divTilde A = 0` and profile `a` (the flat dimension is positive, forced by `A`'s existence via the
`numDiv ≤ flatDim` invariant), then the leaf `leafOfState M s` has an analytic index with profile `a`
(`leafOfState`'s analytic side enumerates exactly the `t̃ = 0` sublist via `t0Indices`). -/
theorem leafOfState_carries {M : Fin (L + 1) → ℕ} (s : ConState L) (hfd : 0 < flatDim M)
    {a : Fin L → ℕ} (A : Fin s.numDiv) (hA0 : s.divTilde A = 0) (hAa : s.divProfile A = a) :
    ∃ k : Fin (leafOfState M s).numDiv, (leafOfState M s).divProfile k = a := by
  have hmem : A ∈ t0Indices s := (mem_t0Indices s A).mpr hA0
  obtain ⟨i, hi⟩ := List.get_of_mem hmem
  unfold leafOfState; rw [dif_pos hfd]; dsimp only
  exact ⟨i, by rw [hi, hAa]⟩

/-- **A step's child-subtree leaves are among the parent's leaves** (the existential navigator, the
branch part of `leaves_isFullMono` reversed): if `conOracle M s` steps with child `c ∈ children`, every
leaf of `buildTree … c.child` is a leaf of `buildTree … s`. Chains a witness up the steered path. -/
theorem childLeaves_subset (M : Fin (L + 1) → ℕ) (s : ConState L) {node : StepData M}
    {children : List (StepChild M s)} {hnode hlayer hstep}
    (hoc : conOracle M s = ConDecision.step node children hnode hlayer hstep)
    {c : StepChild M s} (hc : c ∈ children) :
    ResolutionTree.leaves (buildTree M (conOracle M) c.child) ⊆
      ResolutionTree.leaves (buildTree M (conOracle M) s) := by
  intro l hl
  rw [buildTree_step M (conOracle M) s node children hoc, ResolutionTree.leaves, edgesLeaves_eq,
      List.mem_flatMap]
  exact ⟨Edge.mk c.ecase c.esubst (buildTree M (conOracle M) c.child),
    List.mem_map.2 ⟨c, hc, rfl⟩, hl⟩

/-- **Positive widths ⟹ positive running-min width** `0 < widthMinUpto M n` (the inf' of positive
widths). Load-bearing for the anchor descent: the rollover threshold never traps the anchor. -/
theorem widthMinUpto_pos {M : Fin (L + 1) → ℕ} (hMpos : ∀ i, 0 < M i) (n : ℕ) :
    0 < widthMinUpto M n :=
  (Finset.lt_inf'_iff _).2 (fun i _ => hMpos i)

/-- **Post-birth suffix stays below the envelope** (cert §1/§4, the `Clearable` arithmetic). Once an
admissible clearable `a` drops strictly below the running-min envelope at coord `b`
(`a b < widthMinUpto M (b+1)`), it stays strictly below at every later coord `d ≥ b`. Otherwise the
envelope is re-touched at some `d ≥ b`; take the LAST re-touch `e` (it exists, `≥ d`, and `e ≠ L−1`
since `a^L = 0 < envelope` by positive widths); at `e+1` the profile strictly descends from the
saturated `a e`, so `Clearable e (e+1)` forces `a b` (with `b ≤ e`) back onto the envelope —
contradiction. -/
theorem clearable_suffix_lt_runMinWidth {M : Fin (L + 1) → ℕ} {a : Fin L → ℕ}
    (ha : a ∈ Adm M) (hc : Clearable M a) (hMpos : ∀ i, 0 < M i) {b d : Fin L}
    (hb : a b < widthMinUpto M (b.val + 1)) (hbd : b ≤ d) :
    a d < widthMinUpto M (d.val + 1) := by
  obtain ⟨_, hdec, hlast⟩ := (Finset.mem_filter.1 ha).2
  by_contra hcon
  push_neg at hcon
  have hd_eq : a d = widthMinUpto M (d.val + 1) :=
    le_antisymm (adm_le_widthMinUpto M a ha d) hcon
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le d.val) d.isLt
  -- the LAST coord where `a` re-touches the envelope, at or after `d`.
  obtain ⟨e, hemem, hemax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun e : Fin L => d ≤ e ∧ a e = widthMinUpto M (e.val + 1)))
    (fun e => e.val)
    ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, hd_eq⟩⟩
  obtain ⟨-, hde, he_env⟩ := Finset.mem_filter.mp hemem
  -- `e ≠ L−1`: the last coord is `0 < envelope`.
  have henvpos : 0 < widthMinUpto M ((L - 1) + 1) := widthMinUpto_pos hMpos _
  have he_ne_last : e.val ≠ L - 1 := by
    intro h
    have hz : widthMinUpto M (e.val + 1) = 0 := by rw [← he_env]; exact hlast e h
    rw [h] at hz; omega
  have hej : e.val + 1 < L := by omega
  set j : Fin L := ⟨e.val + 1, hej⟩ with hj
  have hjval : (j : ℕ) = e.val + 1 := by rw [hj]
  have hej_le : e ≤ j := by rw [Fin.le_def, hjval]; omega
  -- `a j < a e` (strict): else `j` re-touches the envelope, contradicting `e = max`.
  have haj_lt : a j < a e := by
    rcases lt_or_eq_of_le (hdec e j hej_le) with h | h
    · exact h
    · exfalso
      have h1 : widthMinUpto M (j.val + 1) ≤ widthMinUpto M (e.val + 1) :=
        widthMinUpto_mono M (by rw [hjval]; omega)
      have h2 : a j ≤ widthMinUpto M (j.val + 1) := adm_le_widthMinUpto M a ha j
      have hjenv : a j = widthMinUpto M (j.val + 1) := by rw [h, he_env] at h2 ⊢; omega
      have hjmem : j ∈ Finset.univ.filter
          (fun e : Fin L => d ≤ e ∧ a e = widthMinUpto M (e.val + 1)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans hde hej_le, hjenv⟩
      have hle := hemax j hjmem
      rw [hjval] at hle; omega
  -- `Clearable e (e+1)` then forces `a b = envelope`, contradicting `hb`.
  have hcl := hc e j (by rw [hj]) haj_lt (by rw [hj]; exact he_env)
  have hbenv := hcl b (le_trans (Fin.le_def.mp hbd) (Fin.le_def.mp hde))
  omega

/-! ### The 3-phase steering invariant (`SteerInv`), cert §4 / both design consults

The `conRel`-WF induction carries `SteerInv M a s`: the state satisfies the banked cone-goodness
(`OracleInv` + `NumDivInv`) and exactly one of three phases along the `R(a)` steered path — `pre`
(the envelope diagonal being laid, no anchor yet), `anchored` (the anchor `A` present, head `= a`,
descending), or `done` (terminal, `A`'s profile IS `a`). The load-bearing strengthening over the cert's
anchor-only form is the **level-coverage** clause (every level `≤ a^layer` is occupied) — it forces the
anchor's pull at exactly `cleared = a^layer` (both consults; the cert's anchor-only invariant is too
weak). -/

/-- The anchor's target profile at layer `S`, level `q`: `a` on the frozen head (`< S`), flat `q` on
the tail (`≥ S`). At the terminal layer `cut a L q = a` on every coord. -/
def cut (a : Fin L → ℕ) (S q : ℕ) : Fin L → ℕ := fun p => if (p : ℕ) < S then a p else q

/-- **Rollover re-index of a landed anchor**: `cut a m (a^m) = cut a (m+1) (a^m)` — the flat tail
value `a^m` becomes the frozen coord `m` at the next layer (the new coord `m` reads `a m` either way). -/
theorem cut_succ_self (a : Fin L → ℕ) {m : ℕ} (hm : m < L) :
    cut a m (a ⟨m, hm⟩) = cut a (m + 1) (a ⟨m, hm⟩) := by
  funext p; unfold cut
  by_cases hp : (p : ℕ) < m
  · rw [if_pos hp, if_pos (by omega)]
  · by_cases hp1 : (p : ℕ) < m + 1
    · rw [if_neg hp, if_pos hp1]; exact congrArg a (Fin.ext (by omega : m = (p : ℕ)))
    · rw [if_neg hp, if_neg hp1]

/-- **Phase 1 — pre-birth**: the head is the running-min envelope, `cleared` has not passed `a^layer`,
and every level below `cleared` is occupied (the diagonal being laid down; no anchor yet). -/
def SteerPre (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (s : ConState L) : Prop :=
  ∃ hm : s.layer < L,
    (∀ i : Fin L, (i : ℕ) < s.layer → a i = runMinWidth M i) ∧
      s.cleared ≤ a ⟨s.layer, hm⟩ ∧
      (∀ q : ℕ, q < s.cleared → ∃ k : Fin s.numDiv, s.divTilde k = q)

/-- **Phase 2 — post-birth**: the anchor `A` is present with profile `cut a layer q` (head `= a`, flat
tail `= q`) and level `q`; the whole suffix is strictly below the envelope; every level `≤ a^layer` is
occupied (LowCover — the pull-forcing clause); `a^layer ≤ q < widthMinUpto layer` (the anchor is live);
and `A` is either LANDED (`q = a^layer`) or PENDING (`q = a^{layer-1} > a^layer`, `cleared ≤ a^layer`). -/
def SteerAnchored (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (s : ConState L) : Prop :=
  ∃ hm : s.layer < L,
    (∀ i : Fin L, s.layer ≤ (i : ℕ) → a i < widthMinUpto M ((i : ℕ) + 1)) ∧
      (∀ q : ℕ, q ≤ a ⟨s.layer, hm⟩ → ∃ k : Fin s.numDiv, s.divTilde k = q) ∧
        ∃ A : Fin s.numDiv, ∃ q : ℕ,
          s.divProfile A = cut a s.layer q ∧ s.divTilde A = q ∧
            a ⟨s.layer, hm⟩ ≤ q ∧ q < widthMinUpto M s.layer ∧
              (q = a ⟨s.layer, hm⟩ ∨
                (∃ hm1 : s.layer - 1 < L, q = a ⟨s.layer - 1, hm1⟩ ∧
                  a ⟨s.layer, hm⟩ < q ∧ s.cleared ≤ a ⟨s.layer, hm⟩))

/-- **Phase 3 — done**: at the terminal layer the anchor's profile IS `a` (level `0`). -/
def SteerDone (a : Fin L → ℕ) (s : ConState L) : Prop :=
  L ≤ s.layer ∧ ∃ A : Fin s.numDiv, s.divProfile A = a ∧ s.divTilde A = 0

/-- **The steering invariant** carried through the `conRel`-WF fold: cone-goodness (`OracleInv` +
`NumDivInv`) plus exactly one steering phase. -/
def SteerInv (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (s : ConState L) : Prop :=
  OracleInv M s ∧ NumDivInv M s ∧
    (SteerPre M a s ∨ SteerAnchored M a s ∨ SteerDone a s)

/-- **A cone-good state that terminates has `L ≤ layer`** — rules out the chooser fallback terminal:
the other terminal route needs `chooseMin = none` at an occupied target level, impossible on a
`SameLevelChainInv` state (`chooserTotalOnChain_of_sameLevel`). Mirrors `conOracle_terminal_leaf`'s
dispatch, deriving a contradiction in every non-`L ≤ layer` branch. -/
theorem conOracle_terminal_le {M : Fin (L + 1) → ℕ} {s : ConState L} (hslc : SameLevelChainInv s)
    {l' : LeafData M} {hl'} (h : conOracle M s = ConDecision.terminal l' hl') : L ≤ s.layer := by
  by_contra hcon
  by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
  · rw [show conOracle M s = rolloverDecision M s (le_of_lt (not_le.mp hcon)) h2 from by
      unfold conOracle; rw [dif_neg hcon, dif_pos h2]] at h
    simp only [rolloverDecision, reduceCtorEq] at h
  · have hcap : s.cleared < layerCap M :=
      lt_of_lt_of_le (not_le.mp h2) (widthMinUpto_le_layerCap M _)
    rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
        if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
        then some (s.divTilde k) else none)).min? with _ | target
    · rw [show conOracle M s = case2Decision M s (widthMinUpto M s.layer - s.cleared)
          (M ⟨s.layer + 1, by omega⟩ - s.cleared) hcap from by
        unfold conOracle; rw [dif_neg hcon, dif_neg h2]; split <;> simp_all only [reduceCtorEq]] at h
      simp only [case2Decision, reduceCtorEq] at h
    · obtain ⟨hmemtar, _⟩ := List.min?_eq_some_iff'.mp hmin
      rw [List.mem_filterMap] at hmemtar
      obtain ⟨k0, _, hk0⟩ := hmemtar
      have hdt : s.divTilde k0 = target := by
        by_cases hc : s.cleared + 1 ≤ s.divTilde k0 ∧ s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
        · rw [if_pos hc] at hk0; exact Option.some.inj hk0
        · rw [if_neg hc] at hk0; exact absurd hk0 (by simp)
      rcases hf : chooseMin s target with _ | f
      · have htot := chooserTotalOnChain_of_sameLevel s hslc target ⟨k0, hdt⟩
        rw [hf] at htot; simp at htot
      · have htar : s.cleared + 1 ≤ target := by
          by_cases hc : s.cleared + 1 ≤ s.divTilde k0 ∧ s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
          · rw [if_pos hc] at hk0; have := Option.some.inj hk0; omega
          · rw [if_neg hc] at hk0; exact absurd hk0 (by simp)
        have htgt : s.divTilde f = target := (chooseMin_spec s target hf).1
        rw [show conOracle M s = case1Decision M s f (target - s.cleared)
            (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, by omega⟩ - s.cleared)
            (not_le.mp hcon) (by omega) (by rw [htgt]; omega) hcap from by
          unfold conOracle; rw [dif_neg hcon, dif_neg h2]
          split <;> simp_all only [reduceCtorEq, Option.some.injEq]
          all_goals (try subst_vars)
          all_goals (try (split <;> simp_all only [reduceCtorEq, Option.some.injEq]))] at h
        simp only [case1Decision, reduceCtorEq] at h

/-- **`SteerInv` holds at the root** — cone-goodness (banked) + phase `pre` (vacuous at layer `0`,
cleared `0`; needs `0 < L` for the `layer < L` witness). The base of the steered fold. -/
theorem SteerInv_conRoot (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (hL : 0 < L) :
    SteerInv M a (conRoot : ConState L) := by
  refine ⟨OracleInv_conRoot, NumDivInv_conRoot, Or.inl ⟨hL, ?_, ?_, ?_⟩⟩
  · intro i hi; exact absurd hi (Nat.not_lt_zero _)
  · exact Nat.zero_le _
  · intro q hq; exact absurd hq (Nat.not_lt_zero _)

/-- **The `R(a)`-steered child preserves `SteerInv`** (the phase-maintenance core, cert §4). At a step
state, select the child `conOracle` emits along the steering rule (case-1(1) iff the target level
`> a^layer`, else case-1(2); rollover/case-2 forced) and re-establish `SteerInv` at it. The
level-coverage clause forces the anchor's pull at exactly `cleared = a^layer` (the descent case).
CRUX (sorried): the per-phase per-transition maintenance — birth (case-2 at `cleared = a^layer`),
plateau/descent (case-1), transport (append via `Fin.castSucc`), rollover (landed→pending). -/
theorem exists_steered_child (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (ha : a ∈ Adm M)
    (hc : Clearable M a) (hMpos : ∀ i, 0 < M i) {s : ConState L} (hinv : SteerInv M a s)
    (hlt : s.layer < L) :
    ∃ c ∈ (conOracle M s).stepChildren, SteerInv M a c.child := by
  obtain ⟨inv, hnd, hphase⟩ := hinv
  have h1 : ¬ L ≤ s.layer := not_le.mpr hlt
  -- OracleInv / NumDivInv for any emitted child are free (banked); only the PHASE is the content.
  suffices h : ∃ c ∈ (conOracle M s).stepChildren,
      (SteerPre M a c.child ∨ SteerAnchored M a c.child ∨ SteerDone a c.child) by
    obtain ⟨c, hcmem, hp⟩ := h
    exact ⟨c, hcmem, OracleInv_conOracle_stepChildren s inv c hcmem,
      NumDivInv_conOracle_stepChildren s hnd c hcmem, hp⟩
  by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
  · -- ROLLOVER (forced): the single child `s.stepRollover`.
    rw [show conOracle M s = rolloverDecision M s (le_of_lt hlt) h2 from by
      unfold conOracle; rw [dif_neg h1, dif_pos h2]]
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    show SteerPre M a s.stepRollover ∨ SteerAnchored M a s.stepRollover ∨ SteerDone a s.stepRollover
    obtain ⟨-, hdec, hlast⟩ := (Finset.mem_filter.1 ha).2
    have ham : a ⟨s.layer, hlt⟩ ≤ widthMinUpto M (s.layer + 1) := adm_le_widthMinUpto M a ha ⟨s.layer, hlt⟩
    have hdecm : ∀ (h : s.layer + 1 < L), a ⟨s.layer + 1, h⟩ ≤ a ⟨s.layer, hlt⟩ := fun h =>
      hdec ⟨s.layer, hlt⟩ ⟨s.layer + 1, h⟩ (Fin.mk_le_mk.mpr (Nat.le_succ _))
    rcases hphase with hpre | hanch | hdone
    · -- PRE: `a^m = envelope` forced by `widthMinUpto(m+1) ≤ cleared ≤ a^m ≤ widthMinUpto(m+1)`.
      obtain ⟨_, henv, hcl_le, -⟩ := hpre
      have haeq : a ⟨s.layer, hlt⟩ = widthMinUpto M (s.layer + 1) :=
        le_antisymm ham (le_trans h2 hcl_le)
      have hmL : s.layer + 1 < L := by
        rcases Nat.lt_or_ge (s.layer + 1) L with h | h
        · exact h
        · exfalso
          have hz : a ⟨s.layer, hlt⟩ = 0 := hlast _ (by omega : s.layer = L - 1)
          have hpos := widthMinUpto_pos hMpos (s.layer + 1)
          omega
      refine Or.inl ⟨hmL, ?_, Nat.zero_le _, fun q hq => absurd hq (Nat.not_lt_zero _)⟩
      intro i hi
      by_cases him : (i : ℕ) < s.layer
      · exact henv i him
      · have hisl : (i : ℕ) < s.layer + 1 := hi
        have hie : i = ⟨s.layer, hlt⟩ := Fin.ext (by omega : (i : ℕ) = s.layer)
        rw [hie, runMinWidth_eq_widthMinUpto]; exact haeq
    · -- ANCHORED: pending impossible (suffix `< envelope`); landed → pending/landed at `m+1`, or done.
      obtain ⟨_, hsuf, hcov, A, q, hAprof, hAq, hqge, hqlt, hlp⟩ := hanch
      have hsufm : a ⟨s.layer, hlt⟩ < widthMinUpto M (s.layer + 1) := hsuf ⟨s.layer, hlt⟩ (le_refl _)
      have hland : q = a ⟨s.layer, hlt⟩ := by
        rcases hlp with hl | ⟨_, -, -, hcl⟩
        · exact hl
        · exact absurd (le_trans h2 hcl) (not_le.mpr hsufm)
      by_cases hmL : s.layer + 1 < L
      · refine Or.inr (Or.inl ⟨hmL, fun i hi => hsuf i (by have : s.layer + 1 ≤ (i : ℕ) := hi; omega),
          ?_, A, a ⟨s.layer, hlt⟩, ?_, ?_, hdecm hmL, hsufm, ?_⟩)
        · intro q' hq'; exact hcov q' (le_trans hq' (hdecm hmL))
        · show s.divProfile A = _; rw [hAprof, hland]; exact cut_succ_self a hlt
        · show s.divTilde A = _; rw [hAq, hland]
        · rcases lt_or_eq_of_le (hdecm hmL) with hlt' | heq'
          · exact Or.inr ⟨(by omega : s.layer + 1 - 1 < L),
              congrArg a (Fin.ext (by omega : s.layer = s.layer + 1 - 1)), hlt', Nat.zero_le _⟩
          · exact Or.inl heq'.symm
      · have hmlL : s.layer + 1 = L := by omega
        refine Or.inr (Or.inr ⟨(by omega : L ≤ s.layer + 1), A, ?_, ?_⟩)
        · show s.divProfile A = a
          rw [hAprof, hland]
          funext p; unfold cut
          by_cases hp : (p : ℕ) < s.layer
          · rw [if_pos hp]
          · rw [if_neg hp]
            exact congrArg a (Fin.ext (by have := p.isLt; omega : s.layer = (p : ℕ)))
        · show s.divTilde A = 0; rw [hAq, hland]; exact hlast _ (by omega : s.layer = L - 1)
    · exact absurd hdone.1 (by omega)
  · have hcap : s.cleared < layerCap M :=
      lt_of_lt_of_le (not_le.mp h2) (widthMinUpto_le_layerCap M _)
    rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
        if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
        then some (s.divTilde k) else none)).min? with _ | target
    · -- CASE-2 (forced): the single appended child.
      rw [show conOracle M s = case2Decision M s (widthMinUpto M s.layer - s.cleared)
          (M ⟨s.layer + 1, by omega⟩ - s.cleared) hcap from by
        unfold conOracle; rw [dif_neg h1, dif_neg h2]; split <;> simp_all only [reduceCtorEq]]
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      show SteerPre M a (s.stepAppendAdvance (widthMinUpto M s.layer - s.cleared)
          (fun p => runMinWidth M p)) ∨
        SteerAnchored M a (s.stepAppendAdvance (widthMinUpto M s.layer - s.cleared)
          (fun p => runMinWidth M p)) ∨
        SteerDone a (s.stepAppendAdvance (widthMinUpto M s.layer - s.cleared)
          (fun p => runMinWidth M p))
      sorry
    · rcases hf : chooseMin s target with _ | f
      · -- chooser fallback: impossible on a `SameLevelChainInv` state.
        exfalso
        obtain ⟨hmemtar, _⟩ := List.min?_eq_some_iff'.mp hmin
        rw [List.mem_filterMap] at hmemtar
        obtain ⟨k0, _, hk0⟩ := hmemtar
        have hdt : s.divTilde k0 = target := by
          by_cases hcc : s.cleared + 1 ≤ s.divTilde k0 ∧ s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
          · rw [if_pos hcc] at hk0; exact Option.some.inj hk0
          · rw [if_neg hcc] at hk0; exact absurd hk0 (by simp)
        have htot := chooserTotalOnChain_of_sameLevel s inv.slc target ⟨k0, hdt⟩
        rw [hf] at htot; simp at htot
      · -- CASE-1: two children; steer 1(1) iff `target > a^layer`, else 1(2).
        have htar : s.cleared + 1 ≤ target := by
          obtain ⟨hmemtar, _⟩ := List.min?_eq_some_iff'.mp hmin
          rw [List.mem_filterMap] at hmemtar
          obtain ⟨k0, _, hk0⟩ := hmemtar
          by_cases hcc : s.cleared + 1 ≤ s.divTilde k0 ∧ s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
          · rw [if_pos hcc] at hk0; have := Option.some.inj hk0; omega
          · rw [if_neg hcc] at hk0; exact absurd hk0 (by simp)
        have htgt : s.divTilde f = target := (chooseMin_spec s target hf).1
        rw [show conOracle M s = case1Decision M s f (target - s.cleared)
            (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, by omega⟩ - s.cleared)
            (not_le.mp h1) (by omega) (by rw [htgt]; omega) hcap from by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq, Option.some.injEq]
          all_goals (try subst_vars)
          all_goals (try (split <;> simp_all only [reduceCtorEq, Option.some.injEq]))]
        simp only [case1Decision, ConDecision.stepChildren]
        by_cases hsteer : a ⟨s.layer, hlt⟩ < target
        · -- 1(1): the merge child (first).
          refine ⟨_, List.mem_cons_self, ?_⟩
          sorry
        · -- 1(2): the split child (second).
          refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
          sorry

/-- **The steered leaf fold** (cert §4, the `conRel`-WF induction): from `SteerInv M a s`, some leaf of
`buildTree M (conOracle M) s` carries `a` as an analytic divisor profile. At a terminal, `SteerInv`
gives phase `done` (the other phases need `layer < L`, excluded by `conOracle_terminal_le`), whose
anchor reads off via `leafOfState_carries`; at a step, `exists_steered_child` picks the steered child
and `childLeaves_subset` chains its realized leaf up. -/
theorem realize_aux (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (ha : a ∈ Adm M) (hc : Clearable M a)
    (hMpos : ∀ i, 0 < M i) (s : ConState L) (hinv : SteerInv M a s) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) s),
      ∃ k : Fin l.numDiv, l.divProfile k = a := by
  induction s using (conRel_wf M).induction with
  | _ s ih =>
    cases hoc : conOracle M s with
    | terminal l' hleaf =>
      have hle : L ≤ s.layer := conOracle_terminal_le hinv.1.slc hoc
      rcases hinv.2.2 with hpre | hanch | hdone
      · exfalso; obtain ⟨hm, _⟩ := hpre; omega
      · exfalso; obtain ⟨hm, _⟩ := hanch; omega
      · obtain ⟨-, A, hAprof, hA0⟩ := hdone
        have hfd : 0 < flatDim M :=
          lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le A.val) A.isLt)
            (numDiv_le_flatDim_of_inv hinv.2.1)
        obtain ⟨k, hk⟩ := leafOfState_carries s hfd A hA0 hAprof
        refine ⟨leafOfState M s, ?_, k, hk⟩
        rw [buildTree_terminal M (conOracle M) s l' hleaf hoc, conOracle_terminal_leaf s hoc]
        simp [ResolutionTree.leaves]
    | step node children hnode hlayer hstep =>
      have hlt : s.layer < L := by
        by_contra hcon
        rw [show conOracle M s = oracleTerminal M s from by
          unfold conOracle; rw [dif_pos (not_lt.mp hcon)]] at hoc
        simp only [oracleTerminal, reduceCtorEq] at hoc
      obtain ⟨c, hcmem, hcinv⟩ := exists_steered_child M a ha hc hMpos hinv hlt
      rw [hoc] at hcmem
      simp only [ConDecision.stepChildren] at hcmem
      obtain ⟨l, hl, k, hk⟩ := ih c.child c.hdesc hcinv
      exact ⟨l, childLeaves_subset M s hoc hcmem hl, k, hk⟩

/-- **`tStar M` is realized as a `t̃ = 0` leaf-divisor profile of the built tree** (cert §4, the
anchor-descent along the `R(tStar)` steering path). MINIMIZER-ONLY: this is `tStar`, not general
`Clearable-Adm` (= R7). The `t̃ = 0` is automatic (`tStar ∈ Adm`, last coord `0`).

**POSITIVE WIDTHS ARE REQUIRED** (`hMpos : ∀ i, 0 < M i`; caveat next to the claim): the achievability
half is FALSE at a zero width. Witness `M = ![2,2,0]`: `tStar M = (2,0)` but `widthMinUpto M 2 = 0`
forces an immediate rollover at layer 1, so the built tree's only `t̃ = 0` divisor is `(0,0)` — `(2,0)`
is never realized (verified: integer sim + the Lean `conOracle` trace; two decorrelated Codex consults
independently found the same, with witness `![1,1,0]`). This matches the divergence half's `hMpos`
(`RouteMAchieverFullHNoFree`), the attainment/tightness layer that needs positive widths throughout;
the `⊆` lower bound (`minAdm_le_terminalExponents`) stays width-free.

CRUX (sorried, the §4 construction-tracing arc): the `conRel`-WF leaf fold along the `R(tStar)`
steering path, maintaining the 3-phase `SteerInv` (`pre`/`anchored`/`done`, with the level-coverage
clause forcing the anchor's pull at exactly `cleared = tStar^S`), reading `tStar` off the terminal
leaf. Tripwire: if the level-coverage / phase-maintenance fights, STOP + report. -/
theorem tStar_realized (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divProfile k = tStar M :=
  realize_aux M (tStar M) (tStar_mem M) (clearable_tStar M) hMpos conRoot
    (SteerInv_conRoot M (tStar M) hL)

/-- **`o5_core`, realized** (cert §3 + §4 composed): `minAdm M` is a divisor exponent of a leaf of the
built tree. The MOVE-AT-LANDING target — when this lands, o5_core moves here from `EngineConstruction`
(its sorry deleted) and `o5_realization` (`EngineObligations`) consumes it. Needs `hMpos` (the
achievability half is false at a zero width — see `tStar_realized`; the downstream re-signature joins
the move-at-landing batch). PROVEN modulo the §4 crux `tStar_realized`: the realized `tStar` leaf
divisor has `divExp = (Mval M tStar).toNat = minAdm M` (`IsFullMonomialization` read-off +
`Mval_tStar_eq`). -/
theorem o5_core_realized (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divExp k = minAdm M := by
  obtain ⟨l, hl, k, hk⟩ := tStar_realized M hL hMpos
  refine ⟨l, hl, k, ?_⟩
  have hexp := ((isFullMonomialization_buildTree_conRoot M hL l hl).1 k).1
  rw [hexp, hk, Mval_tStar_eq]
  exact Int.toNat_natCast _

end DLNFibre.DLN.RLCT.Engine

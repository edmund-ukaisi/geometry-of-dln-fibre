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

/-- **`tStar M` is realized as a `t̃ = 0` leaf-divisor profile of the built tree** (cert §4, the
anchor-descent along the `R(tStar)` steering path). MINIMIZER-ONLY: this is `tStar`, not general
`Clearable-Adm` (= R7). The `t̃ = 0` is automatic (`tStar ∈ Adm`, last coord `0`).

CRUX (sorried, the §4 construction-tracing brick): trace the `R(tStar)` root→leaf path in
`buildTree M (conOracle M) conRoot` (following the case-1(1)/1(2) selection per the steering rule),
maintain the anchor-descent invariant, and read `tStar` off the terminal leaf. Reuses `LiveHeadDom` /
`chooserTotalOnChain_of_sameLevel` / `step1_dominates` (reuse index (b)). Tripwire: if the pull-ordering
brick fights beyond a couple honest attempts, STOP + report for a consult seat. -/
theorem tStar_realized (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divProfile k = tStar M := by
  sorry

/-- **`o5_core`, realized** (cert §3 + §4 composed): `minAdm M` is a divisor exponent of a leaf of the
built tree. The MOVE-AT-LANDING target — when this lands, o5_core moves here from `EngineConstruction`
(its sorry deleted) and `o5_realization` (`EngineObligations`) consumes it. PROVEN modulo the §4 crux
`tStar_realized`: the realized `tStar` leaf divisor has `divExp = (Mval M tStar).toNat = minAdm M`
(`IsFullMonomialization` read-off + `Mval_tStar_eq`). -/
theorem o5_core_realized (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divExp k = minAdm M := by
  obtain ⟨l, hl, k, hk⟩ := tStar_realized M hL
  refine ⟨l, hl, k, ?_⟩
  have hexp := ((isFullMonomialization_buildTree_conRoot M hL l hl).1 k).1
  rw [hexp, hk, Mval_tStar_eq]
  exact Int.toNat_natCast _

end DLNFibre.DLN.RLCT.Engine

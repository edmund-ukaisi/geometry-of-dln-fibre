import DLNFibre.DLN.RLCT.Foundations.Lambda
import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit` — the LAYER-COLLAPSING carrier + recursion (R1 re-arch)

The re-architecture banked carrier for the general-M `routeStep` recursion. The fixed-arity
`ChainDimSplit M` (width-only, `Fin (L+1)`) structurally CANNOT express the genuine layer-collapsing
recursion (triple+Codex-confirmed by the prior tide, `RouteMRecursion.lean` blocker doc). This file
banks the layer-collapsing carrier `LayerSplit` and the value recursion `minAdmRec`, PROVEN to compute
the brute-force `minAdm = (Adm M).inf' Mval` — the keystone the fixed-arity carrier could not reach.

The genuine recursion (Aoyagi layer-peeling; exact 12/12, `/tmp/check_layercollapse.py`):

    minAdm(M₀,M₁,M₂,…,M_L) = min_{t ≤ min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(t, M₂, …, M_L) ]

with the reduced chain `(t,M₂,…,M_L)` having ONE FEWER LAYER (`Fin (L+1+1)` vs `Fin (L+1+1+1)`). The
recursion descends on the ARITY (structural in the `Fin`-arity, no `WellFounded.fix` for the value).

The keystone proof `minAdmRec_eq_minAdm` rests on two exact-certified facts (`/tmp/check_layercollapse.py`,
0 mismatches over 25k random cases):
- the **Mval decomposition** `Mval M T = (M₀−T₀)(M₁−T₀) + Mval (redChain T₀ M) (tail T)` (pointwise);
- the **admissibility bijection** `Adm M ≃ Σ_{t ≤ min(M₀,M₁)} Adm (redChain t M)` via `T ↦ (T₀, tail T)`.
-/

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The layer-collapsing reduced chain + recursion -/

/-- The layer-collapsed reduced chain `(t, M₂, …, M_L)` for a parent `M : Fin (L+1+1+1) → ℕ`:
position 0 is the surviving pivot rank `t`, position `i+1` is `M (i+2)`. The parent has `≥ 3` widths
(`L+2` matrices ↦ `L+1` matrices). One fewer LAYER than the parent. -/
def redChain (t : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ) : Fin (L + 1 + 1) → ℕ :=
  Fin.cons t (fun i : Fin (L + 1) => M i.succ.succ)

@[simp] theorem redChain_zero (t : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ) :
    redChain t M 0 = t := rfl

@[simp] theorem redChain_succ (t : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ) (i : Fin (L + 1)) :
    redChain t M i.succ = M i.succ.succ := by
  simp [redChain]

/-- The brute-force minimal admissible codim `minAdm M = ((Adm M).inf' Mval).toNat`. -/
def minAdm (M : Fin (L + 1) → ℕ) : ℕ := ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat

/-- **The layer-peeling recursion for `minAdm`** (the genuine Aoyagi descent).
- `Fin 1` (`L=0`, vacuous one-width — never a genuine chain): `0`.
- `Fin 2` (`L=1`, the two-width leaf): `M₀·M₁`.
- `Fin (L+3)` (`≥ 3` widths): branch on `t ≤ min(M₀,M₁)`, codim `(M₀−t)(M₁−t)`, recurse on `redChain t M`
  (ONE FEWER LAYER). -/
def minAdmRec : {L : ℕ} → (M : Fin (L + 1) → ℕ) → ℕ
  | 0, _ => 0
  | 1, M => M 0 * M 1
  | (_ + 1 + 1), M =>
      (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp)
        (fun t => (M 0 - t) * (M 1 - t) + minAdmRec (redChain t M))

/-- `minAdmRec` on a `≥ 3`-width chain unfolds to the layer-peeling min. -/
theorem minAdmRec_succ_succ (M : Fin (L + 1 + 1 + 1) → ℕ) :
    minAdmRec M = (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp)
        (fun t => (M 0 - t) * (M 1 - t) + minAdmRec (redChain t M)) := rfl

/-- `minAdmRec` on a two-width leaf is the pivot-width product. -/
theorem minAdmRec_leaf (M : Fin 2 → ℕ) : minAdmRec M = M 0 * M 1 := rfl

/-! ## The Mval decomposition (the elementary per-term algebra) -/

/-- `tPrev` of a parent at `j = i.succ` is `T i.castSucc` (the predecessor exponent). -/
theorem tPrev_succ (M : Fin (L + 1 + 1) → ℕ) (T : Fin (L + 1) → ℕ) (i : Fin L) :
    tPrev M T i.succ = (T i.castSucc : ℤ) := by
  simp only [tPrev]
  rw [if_neg (by simp [Fin.succ] : (i.succ).val ≠ 0)]
  have hidx : (⟨(i.succ).val - 1, by omega⟩ : Fin (L + 1)) = i.castSucc := by
    apply Fin.ext; simp [Fin.succ]
  rw [hidx]

/-- `tPrev` at `j = 0` is `M 0`. -/
theorem tPrev_zero (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (h : 0 < L) :
    tPrev M T ⟨0, h⟩ = (M 0 : ℤ) := by
  simp [tPrev]

/-- **The Mval decomposition (EXACT, pointwise).** For a `≥ 3`-width parent `M`, the candidate value
splits off the leading-pivot block term `(M₀−T₀)(M₁−T₀)` plus the reduced-chain value on the collapsed
chain `(T₀, M₂, …, M_L)` with the tail exponents:
`Mval M T = (M₀−T₀)(M₁−T₀) + Mval (redChain T₀ M) (Fin.tail T)`. The keystone of the layer-peeling
recursion (exact-certified 0/20k, `/tmp/check_layercollapse.py`). Both `Mval`s reindex by
`Fin.sum_univ_succ`; the `j=0` parent term IS the block term, and the `j=i.succ` parent term matches the
`j=i` reduced term under `tail`/`redChain`. -/
theorem Mval_decompose (M : Fin (L + 1 + 1 + 1) → ℕ) (T : Fin (L + 1 + 1) → ℕ) :
    Mval M T
      = ((M 0 : ℤ) - T 0) * ((M 1 : ℤ) - T 0)
        + Mval (redChain (T 0) M) (Fin.tail T) := by
  change (∑ j, (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ)))
      = ((M 0 : ℤ) - T 0) * ((M 1 : ℤ) - T 0)
        + ∑ j, (tPrev (redChain (T 0) M) (Fin.tail T) j - ((Fin.tail T) j : ℤ))
            * ((redChain (T 0) M j.succ : ℤ) - ((Fin.tail T) j : ℤ))
  -- Split the parent sum at j=0; match each parent j=i.succ term to the reduced j=i term.
  -- The j=0 parent term IS the block term definitionally (`tPrev M T 0 = M 0`, `M 0.succ = M 1`),
  -- so `congr 1` closes it by `rfl`, leaving the tail-sum goal.
  rw [Fin.sum_univ_succ]
  congr 1
  -- the parent tail sum (over j=i.succ) = the reduced full sum (over j=i).
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    -- parent term at i.succ:
    rw [tPrev_succ M T i]
    -- reduced term at i:
    have hredtp : tPrev (redChain (T 0) M) (Fin.tail T) i = (T i.castSucc : ℤ) := by
      rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
      · -- i = 0: tPrev (redChain) (tail) 0 = redChain 0 = T 0 = T (0.castSucc)
        simp only [tPrev, hi0, if_pos]
        rw [redChain_zero]
        norm_cast
        congr 1
        apply Fin.ext
        simp [Fin.val_castSucc, hi0]
      · -- i ≥ 1: tPrev (redChain) (tail) i = (tail T) (i-1) = T (i-1).succ = T i.castSucc
        simp only [tPrev]
        rw [if_neg (by omega : i.val ≠ 0)]
        simp only [Fin.tail]
        norm_cast
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
    rw [hredtp]
    -- the second factor: parent M i.succ.succ vs reduced (redChain) at i.succ
    rw [redChain_succ]
    -- and the subtracted exponents: parent T i.succ vs reduced (tail T) i
    simp only [Fin.tail]

/-! ## The admissibility transfer (the `Adm M ↔ Σ_t Adm (redChain t M)` bijection content) -/

/-- `admBound` of the reduced chain at `0` is `min t (M 2)` (= `min (redChain 0) (redChain 1)`). -/
theorem admBound_redChain_zero (t : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ) :
    admBound (redChain t M) 0 = min t (M 2) := by
  rw [admBound, if_pos (by rfl), redChain_zero]
  have h1 : redChain t M 1 = M 2 := by
    rw [show (1 : Fin (L + 1 + 1)) = (0 : Fin (L + 1)).succ from by
      apply Fin.ext; simp [Fin.val_one]]
    rw [redChain_succ]
    congr 1
  rw [h1]

/-- `admBound` of the reduced chain at `j = i.succ` (`i : Fin L`) is `M i.succ.succ.succ` (the parent
bound shifted by one layer). -/
theorem admBound_redChain_succ (t : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ) (i : Fin L) :
    admBound (redChain t M) i.succ = M i.succ.succ.succ := by
  rw [admBound, if_neg (by simp : (i.succ).val ≠ 0), redChain_succ]

/-- **Forward admissibility transfer.** If `T ∈ Adm M` for a `≥ 3`-width parent, then the leading pivot
`T 0 ≤ min (M 0) (M 1)` and the tail `Fin.tail T ∈ Adm (redChain (T 0) M)`. The forward leg of the
`Adm M ↔ Σ_t Adm (redChain t M)` bijection (exact-certified 0/5k, `/tmp/check_layercollapse.py`). -/
theorem tail_mem_Adm_redChain (M : Fin (L + 1 + 1 + 1) → ℕ) (T : Fin (L + 1 + 1) → ℕ)
    (hT : T ∈ Adm M) :
    T 0 ≤ min (M 0) (M 1) ∧ Fin.tail T ∈ Adm (redChain (T 0) M) := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨_, hbound, hdecr, hlast⟩ := hT
  have h0bound : T 0 ≤ min (M 0) (M 1) := by
    have := hbound 0; simpa [admBound] using this
  refine ⟨h0bound, ?_⟩
  -- The shared per-index bound for the tail (indices in `Fin (L+1)`).
  have hbnd : ∀ j : Fin (L + 1), Fin.tail T j ≤ admBound (redChain (T 0) M) j := by
    intro j
    rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
    · have hj : j = 0 := Fin.ext hj0
      subst hj
      rw [admBound_redChain_zero]
      simp only [Fin.tail]
      have e01 : (Fin.succ (0 : Fin (L+1)) : Fin (L+1+1)) = (1 : Fin (L+1+1)) := by
        apply Fin.ext; simp [Fin.val_one]
      rw [e01]
      have hT1le0 : T 1 ≤ T 0 := hdecr 0 1 (by simp [Fin.le_def, Fin.val_one])
      have hT1leM2 : T 1 ≤ M 2 := by
        have := hbound 1
        have h1 : admBound M 1 = M 2 := by
          rw [admBound, if_neg (by simp [Fin.val_one] : (1 : Fin (L+1+1)).val ≠ 0)]
          congr 1
        rw [h1] at this
        omega
      omega
    · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := j) (by
        intro h; rw [h] at hjpos; simp at hjpos)
      rw [admBound_redChain_succ]
      simp only [Fin.tail]
      have := hbound i.succ.succ
      have hb : admBound M i.succ.succ = M i.succ.succ.succ := by
        rw [admBound, if_neg (by simp : (i.succ.succ).val ≠ 0)]
      rw [hb] at this
      omega
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, hbnd, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [Finset.mem_range]; have := hbnd j; omega
  · intro a b hab
    simp only [Fin.tail]
    exact hdecr a.succ b.succ (Fin.succ_le_succ_iff.mpr hab)
  · intro j hj
    simp only [Fin.tail]
    apply hlast j.succ
    simp only [Fin.val_succ]
    omega

/-- **Backward admissibility transfer.** If `t ≤ min (M 0) (M 1)` and `T' ∈ Adm (redChain t M)`, then the
reassembled exponent `Fin.cons t T' ∈ Adm M`. The backward leg of the bijection: every admissible reduced
stratum lifts to an admissible parent stratum with leading exponent `t`. -/
theorem cons_mem_Adm (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (T' : Fin (L + 1) → ℕ)
    (ht : t ≤ min (M 0) (M 1)) (hT' : T' ∈ Adm (redChain t M)) :
    Fin.cons t T' ∈ Adm M := by
  rw [Adm, Finset.mem_filter] at hT'
  obtain ⟨_, hbound', hdecr', hlast'⟩ := hT'
  -- `T' 0 ≤ t` (from `T' 0 ≤ admBound (redChain) 0 = min t (M 2) ≤ t`).
  have hT'0le_t : T' 0 ≤ t := by
    have := hbound' 0
    rw [admBound_redChain_zero] at this
    omega
  -- Per-index bound on `cons t T'`.
  have hbnd : ∀ j : Fin (L + 1 + 1), (Fin.cons t T' : Fin (L + 1 + 1) → ℕ) j ≤ admBound M j := by
    intro j
    rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
    · have hj : j = 0 := Fin.ext hj0
      subst hj
      simpa [admBound] using ht
    · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := j) (by
        intro h; rw [h] at hjpos; simp at hjpos)
      rw [Fin.cons_succ]
      -- `admBound M i.succ = M i.succ.succ`.
      have hbM : admBound M i.succ = M i.succ.succ := by
        rw [admBound, if_neg (by simp : (i.succ).val ≠ 0)]
      rw [hbM]
      -- `T' i ≤ admBound (redChain t M) i = (M i.succ.succ on i≥1, ≤ M 2 ≤ M i.succ.succ on i=0)`.
      have hb' := hbound' i
      rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
      · have hi : i = 0 := Fin.ext hi0
        subst hi
        rw [admBound_redChain_zero] at hb'
        -- T' 0 ≤ min t (M 2) ≤ M 2 = M ((0.succ).succ)
        have hM2 : M (Fin.succ (0 : Fin (L + 1))).succ = M 2 := by
          congr 1
        rw [hM2]; omega
      · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by
          intro h; rw [h] at hipos; simp at hipos)
        rw [admBound_redChain_succ] at hb'
        -- T' k.succ ≤ M k.succ.succ.succ = M (k.succ.succ) = admBound at i.succ
        have hidx : M k.succ.succ.succ = M (Fin.succ k.succ.succ) := rfl
        omega
  rw [Adm, Finset.mem_filter]
  refine ⟨?_, hbnd, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [Finset.mem_range]; have := hbnd j; omega
  · -- weak-decrease of `cons t T'`.
    intro a b hab
    rcases Nat.eq_zero_or_pos a.val with ha0 | hapos
    · -- a = 0: (cons) b ≤ t = (cons) 0.
      have ha : a = 0 := Fin.ext ha0
      subst ha
      rw [Fin.cons_zero]
      rcases Nat.eq_zero_or_pos b.val with hb0 | hbpos
      · have hb : b = 0 := Fin.ext hb0
        subst hb; rw [Fin.cons_zero]
      · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (i := b) (by
          intro h; rw [h] at hbpos; simp at hbpos)
        rw [Fin.cons_succ]
        -- T' k ≤ T' 0 ≤ t
        exact le_trans (hdecr' 0 k (by simp [Fin.le_def])) hT'0le_t
    · -- a = a'.succ, b = b'.succ.
      obtain ⟨a', rfl⟩ := Fin.eq_succ_of_ne_zero (i := a) (by
        intro h; rw [h] at hapos; simp at hapos)
      obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero (i := b) (by
        intro h; subst h
        rw [Fin.le_def] at hab
        simp only [Fin.val_succ, Fin.val_zero] at hab
        omega)
      rw [Fin.cons_succ, Fin.cons_succ]
      exact hdecr' a' b' (Fin.succ_le_succ_iff.mp hab)
  · intro j hj
    -- last index: j = last of Fin (L+1+1) = (last of Fin (L+1)).succ
    have hjne0 : j ≠ 0 := by
      intro h; rw [h] at hj; simp at hj
    obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (i := j) hjne0
    rw [Fin.cons_succ]
    apply hlast' k
    simp only [Fin.val_succ] at hj
    omega

/-! ## The keystone — `minAdmRec` computes the brute-force `inf' Mval` (the layer-peeling theorem) -/

/-- The ℕ block term casts to the ℤ block term when `t ≤ min (M 0) (M 1)`. -/
theorem block_cast {M₀ M₁ t : ℕ} (ht : t ≤ min M₀ M₁) :
    ((M₀ - t) * (M₁ - t) : ℕ) = ((M₀ : ℤ) - t) * ((M₁ : ℤ) - t) := by
  have h0 : t ≤ M₀ := le_trans ht (min_le_left _ _)
  have h1 : t ≤ M₁ := le_trans ht (min_le_right _ _)
  rw [Nat.cast_mul, Nat.cast_sub h0, Nat.cast_sub h1]

/-- `Mval` of the all-zero stratum on a two-width leaf is the pivot-width product `M 0 · M 1`. Local
(`Fin 2`) version of `Mval_zeroT_eq` — keeps this module on the light `Lambda` import. -/
theorem Mval_zeroT_leaf (M : Fin 2 → ℕ) : Mval M (fun _ => 0) = (M 0 : ℤ) * (M 1 : ℤ) := by
  simp only [Mval, Fin.sum_univ_one]
  have h0 : tPrev M (fun _ => 0) 0 = (M 0 : ℤ) := by simp [tPrev]
  have h1 : M (0 : Fin 1).succ = M 1 := by congr 1
  rw [h0, h1]; simp

/-- **The layer-peeling theorem (KEYSTONE, ℤ form).** The brute-force minimal admissible codim
`(Adm M).inf' Mval` equals the cast of the layer-peeling recursion `minAdmRec M`. Proven by induction on
the arity: the `Mval` decomposition + the `Adm M ↔ Σ_t Adm (redChain t M)` bijection (forward/backward
transfers) give the two `le` legs of the `inf'` equality at each step. This is the encoding the fixed-arity
`ChainDimSplit` carrier could NOT express — the layer-collapsing recursion is the genuine Aoyagi descent. -/
theorem minAdmRec_eq_inf' : {L : ℕ} → (M : Fin (L + 1) → ℕ) →
    ((minAdmRec M : ℤ) = (Adm M).inf' (Adm_nonempty M) (Mval M))
  | 0, M => by
      -- L = 0 (Fin 1): vacuous one-width chain. `Adm` exponents are `Fin 0 → ℕ` (only the empty tuple),
      -- `Mval = 0` (empty sum), `minAdmRec = 0`.
      have hMval : ∀ T : Fin 0 → ℕ, Mval M T = 0 := by
        intro T; simp [Mval]
      rw [show minAdmRec M = 0 from rfl]
      have : (Adm M).inf' (Adm_nonempty M) (Mval M) = 0 := by
        obtain ⟨T, _, hT⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
        rw [hT, hMval]
      rw [this]; simp
  | 1, M => by
      -- L = 1 (Fin 2): the leaf. `Adm` has only the all-zero `T` (`T (last) = 0` and `Fin 1`), and
      -- `Mval M 0 = M 0 * M 1`. `minAdmRec = M 0 * M 1`.
      rw [minAdmRec_leaf]
      have hMval0 : Mval M (fun _ => 0) = (M 0 : ℤ) * (M 1 : ℤ) := Mval_zeroT_leaf M
      have hAll : ∀ T : Fin 1 → ℕ, T ∈ Adm M → T = (fun _ => 0) := by
        intro T hT
        rw [Adm, Finset.mem_filter] at hT
        obtain ⟨_, _, _, hlast⟩ := hT
        funext i
        have hi : i = 0 := Fin.ext (by omega)
        subst hi
        exact hlast 0 (by simp)
      have : (Adm M).inf' (Adm_nonempty M) (Mval M) = Mval M (fun _ => 0) := by
        obtain ⟨T, hTmem, hT⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
        rw [hT, hAll T hTmem]
      rw [this, hMval0, Nat.cast_mul]
  | (L + 1 + 1), M => by
      rw [minAdmRec_succ_succ]
      -- IH on each reduced chain.
      have IH : ∀ t : ℕ, (minAdmRec (redChain t M) : ℤ)
          = (Adm (redChain t M)).inf' (Adm_nonempty _) (Mval (redChain t M)) :=
        fun t => minAdmRec_eq_inf' (redChain t M)
      set bmin := min (M 0) (M 1) with hbmin
      -- Push the ℕ→ℤ cast through the recursion's `inf'` (cast preserves `min = ⊓`).
      rw [Finset.comp_inf'_eq_inf'_comp (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
        (g := (Nat.cast : ℕ → ℤ)) (fun x y => by exact_mod_cast Nat.cast_min x y)]
      -- The per-cell ℤ value at `t`: block(t) + ↑minAdmRec(redChain t M).
      have hcell_val : ∀ t : ℕ, t ≤ bmin →
          ((Nat.cast : ℕ → ℤ) ∘ fun t => (M 0 - t) * (M 1 - t) + minAdmRec (redChain t M)) t
          = ((M 0 : ℤ) - t) * ((M 1 : ℤ) - t)
            + (Adm (redChain t M)).inf' (Adm_nonempty _) (Mval (redChain t M)) := by
        intro t ht
        simp only [Function.comp_apply, Nat.cast_add]
        rw [block_cast ht, IH t]
      apply le_antisymm
      · -- recursion-inf' ≤ Adm-inf': use the inf' achiever T* of Adm M.
        obtain ⟨T, hTmem, hTeq⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
        rw [hTeq]
        obtain ⟨hT0, htail⟩ := tail_mem_Adm_redChain M T hTmem
        have hT0' : T 0 ≤ bmin := by rw [hbmin]; exact hT0
        have hmem : T 0 ∈ Finset.range (bmin + 1) := by rw [Finset.mem_range]; omega
        refine le_trans (Finset.inf'_le _ hmem) ?_
        rw [hcell_val (T 0) hT0']
        calc ((M 0 : ℤ) - T 0) * ((M 1 : ℤ) - T 0)
              + (Adm (redChain (T 0) M)).inf' (Adm_nonempty _) (Mval (redChain (T 0) M))
            ≤ ((M 0 : ℤ) - T 0) * ((M 1 : ℤ) - T 0)
              + Mval (redChain (T 0) M) (Fin.tail T) := by gcongr; exact Finset.inf'_le _ htail
          _ = Mval M T := (Mval_decompose M T).symm
      · -- Adm-inf' ≤ recursion-inf': bound by every cell.
        refine Finset.le_inf' _ _ (fun t ht => ?_)
        rw [Finset.mem_range] at ht
        have ht_bmin : t ≤ bmin := by omega
        rw [hcell_val t ht_bmin]
        obtain ⟨T', hT'mem, hT'eq⟩ :=
          Finset.exists_mem_eq_inf' (Adm_nonempty (redChain t M)) (Mval (redChain t M))
        have hcons : (Fin.cons t T' : Fin (L + 1 + 1) → ℕ) ∈ Adm M :=
          cons_mem_Adm M t T' (by rw [hbmin] at ht_bmin; exact ht_bmin) hT'mem
        have hMvalcons : Mval M (Fin.cons t T')
            = ((M 0 : ℤ) - t) * ((M 1 : ℤ) - t) + Mval (redChain t M) T' := by
          rw [Mval_decompose M (Fin.cons t T')]
          simp only [Fin.cons_zero, Fin.tail_cons]
        calc (Adm M).inf' (Adm_nonempty M) (Mval M)
            ≤ Mval M (Fin.cons t T') := Finset.inf'_le _ hcons
          _ = ((M 0 : ℤ) - t) * ((M 1 : ℤ) - t) + Mval (redChain t M) T' := hMvalcons
          _ = ((M 0 : ℤ) - t) * ((M 1 : ℤ) - t)
              + (Adm (redChain t M)).inf' (Adm_nonempty _) (Mval (redChain t M)) := by rw [hT'eq]

/-- **The layer-peeling theorem (ℕ form).** `minAdmRec M = minAdm M` — the layer-collapsing recursion
computes the brute-force minimal admissible codim. Casts `minAdmRec_eq_inf'` through `.toNat`
(`Mval ≥ 0` on `Adm`, so the `inf'` is `≥ 0` and the round-trip is faithful). -/
theorem minAdmRec_eq_minAdm (M : Fin (L + 1) → ℕ) : minAdmRec M = minAdm M := by
  unfold minAdm
  have h := minAdmRec_eq_inf' M
  omega

/-! ## The layer-collapsing carrier `LayerSplit` + the depth-recursion descent

The structured carrier the re-architected `routeStep` recurses on: a leading-pivot rank `t ≤ min(M₀,M₁)`
selecting the reduced chain `redChain t M` (one fewer LAYER). Unlike the fixed-arity `ChainDimSplit M`
(same arity `Fin (L+1)`, width-only), `LayerSplit` is genuinely layer-collapsing — the reduced chain
`redChain t M : Fin (L+1+1) → ℕ` lives one arity below the parent `M : Fin (L+1+1+1) → ℕ`.

The descent certificate generalises the banked `ReducedTransport`/`IsSchurStraightenSqueeze` to the
collapsed chain: peel layer 1 at rank `t` → a fresh depth-`(L+1)` core `dlnLoss (redChain t M) 0` (the
#18 depth-recursion, exact-validated in `verify-r1-shortcut.md`). The squeeze front
(`schur_recursion_step_squeeze`, banked) and the det-1 MP reindex (`rlctAtOn_comp_homeomorph`, banked) are
arity-generic, so they transport to `Params (redChain t M)` unchanged. -/

/-- **The layer-collapsing carrier.** For a `≥ 3`-width parent `M`, a `LayerSplit M` is a leading-pivot
rank `t ≤ min (M₀, M₁)` selecting the reduced chain `redChain t M` (ONE FEWER LAYER). The genuine Aoyagi
layer-peel — the carrier the fixed-arity `ChainDimSplit M` could not express. -/
structure LayerSplit (M : Fin (L + 1 + 1 + 1) → ℕ) where
  /-- The surviving leading-pivot rank after peeling layer 1. -/
  t : ℕ
  /-- The pivot rank is admissible (`≤ min (M₀, M₁)`). -/
  ht : t ≤ min (M 0) (M 1)

/-- The reduced chain of a `LayerSplit` (`= redChain S.t M`, one fewer layer). -/
def LayerSplit.red {M : Fin (L + 1 + 1 + 1) → ℕ} (S : LayerSplit M) : Fin (L + 1 + 1) → ℕ :=
  redChain S.t M

/-- The block codimension a `LayerSplit` cell emits: `(M₀ − t)(M₁ − t)` (the Case-2 block exponent read
directly off the blow-up centre — NOT a per-peel count, the `verify-r1-135` §3 subtlety). -/
def LayerSplit.codim {M : Fin (L + 1 + 1 + 1) → ℕ} (S : LayerSplit M) : ℕ :=
  (M 0 - S.t) * (M 1 - S.t)

/-- **The value-fold over the `LayerSplit` cells is the layer-peeling recursion = `minAdm M`.** The min
over leading-pivot ranks `t ≤ min(M₀,M₁)` of `(M₀−t)(M₁−t) + minAdm (redChain t M)` is `minAdm M`. This
is the carrier's value-fold equation — it CONFIRMS the layer-collapsing carrier resolves the encoding the
fixed-arity `ChainDimSplit` could not. Unfolds `minAdm = minAdmRec` (the keystone) twice + the recursion
step `minAdmRec_succ_succ`; each cell's `minAdm (redChain t M) = minAdmRec (redChain t M)`. -/
theorem LayerSplit_value_eq_minAdm (M : Fin (L + 1 + 1 + 1) → ℕ) :
    (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp)
        (fun t => (M 0 - t) * (M 1 - t) + minAdm (redChain t M))
      = minAdm M := by
  rw [← minAdmRec_eq_minAdm M, minAdmRec_succ_succ]
  refine Finset.inf'_congr _ rfl (fun t _ => ?_)
  rw [minAdmRec_eq_minAdm (redChain t M)]

/-- **The layer-collapsing reduced-chain transport** (the depth-recursion analog of
`rlctAtOn_reduced_transport`). If the post-blow-up reduced core `G` pulls back the COLLAPSED chain loss
`dlnLoss (redChain t M) 0` via a measure-preserving reindex `redEmbed : Y ≃ₜ Params (redChain t M)`
anchored at the deepest point, then `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss (redChain t M) 0) redZero`. The
#18 depth-recursion (peel layer 1 → fresh lower-depth core); the reindex is arity-generic
(`rlctAtOn_comp_homeomorph`), so the same proof transports to the one-fewer-arity chain. -/
theorem rlctAtOn_layerReduced_transport (t : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ)
    {Y : Type*} [MeasureSpace Y] [TopologicalSpace Y] [Zero Y]
    (G : Y → ℝ) (redEmbed : Y ≃ₜ Params (redChain t M))
    (hmp : MeasurePreserving redEmbed volume volume) (hemb : MeasurableEmbedding redEmbed)
    (redZero : Params (redChain t M)) (hzero : redEmbed 0 = redZero)
    (hredCore : ∀ y, G y ^ 2 = dlnLoss (redChain t M) 0 (redEmbed y)) :
    rlctAtOn (fun y => G y ^ 2) (0 : Y) = rlctAtOn (dlnLoss (redChain t M) 0) redZero := by
  have hpull : (fun y => G y ^ 2) = (fun y => dlnLoss (redChain t M) 0 (redEmbed y)) := by
    funext y; exact hredCore y
  rw [hpull, rlctAtOn_comp_homeomorph redEmbed hmp hemb (dlnLoss (redChain t M) 0) 0, hzero]

-- ANCHOR CHECKS: layer-peeling recursion = brute-force minAdm (incl. binding-coupled witnesses).
example : minAdmRec (![2, 2, 2] : Fin 3 → ℕ) = 3 := by decide
example : minAdm (![2, 2, 2] : Fin 3 → ℕ) = 3 := by decide
example : minAdmRec (![3, 3, 4] : Fin 3 → ℕ) = 8 := by decide
example : minAdm (![3, 3, 4] : Fin 3 → ℕ) = 8 := by decide
example : minAdmRec (![4, 4, 2, 2] : Fin 4 → ℕ) = 4 := by decide
example : minAdmRec (![3, 3, 2, 2] : Fin 4 → ℕ) = 4 := by decide

end DLNFibre.DLN.RLCT

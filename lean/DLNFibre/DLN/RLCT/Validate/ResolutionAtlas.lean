import DLNFibre.DLN.RLCT.Skeleton

/-!
# `DLNFibre.DLN.RLCT.Validate.ResolutionAtlas` — the R1.6 atlas obligation + the value consequence

The R1.6 residual (cover-exhaustiveness) pinned as a precise Lean-grade obligation
(`IsResolutionAtlas`) and the value it delivers (`resolution_value_of_atlas`), per pp2's #133
obligation card. The chart-tree of the (C2) resolution is an instance of `resolution_charts`'s
existential witness `(ι, d, k, h)` PLUS a `stratum` tag (the rank stratum each path's binding
min-codim center cuts). The obligation has four conjuncts:

- **(A) `stratum_admissible`** — every path's binding center is an admissible rank stratum
  (structural: the recursion pivots only on `{∏C = 0}`; certified #132).
- **(S) `stratum_surjective`** — every admissible stratum is REACHED by some path (the cover-
  exhaustiveness; *the single residual open obligation* — adjudicated pp2/pp3, formalises later).
- **(K) `mult_one`** — multiplicity 1 on every exceptional divisor (`k_E = 1`, multilinearity #132).
- **(C) `threshold_eq`** — per-path threshold `= ½·(its binding stratum's codim)` (#131 Schur codim +
  `axisRatio_regularSeq` + S2 `monomial_rlct`).

`resolution_value_of_atlas` takes the atlas as a hypothesis and proves
`⨅ monomialThreshold = ofReal(lambdaCore M)` SORRY-FREE. It is the pure `⨅`-rearrangement: the image
of `stratum` is exactly `Adm M` (A: image ⊆ Adm; S: image ⊇ Adm), so the `⨅`-over-paths of
`½·Mval(stratum)` is `½·min_{T∈Adm} Mval = lambdaCore M`. Surjectivity (S) is EXACTLY what makes
`min`-over-image = `min`-over-`Adm` (without it the `⨅` could miss the minimiser and over-estimate —
the incomplete-cover failure).

**Scope: core-only** (`rlctAtOn(dlnLoss M 0) 0`, `M = H − r`). The regular `[−r²+r(H⁰+Hᴸ)]/2` shift is
L2/Fubini (`product_reduction`), NOT here — `IsResolutionAtlas` carries no `nReg`.

This file states the obligation + proves the value consequence; it does NOT prove (S) (the open
combinatorial core, via `Core.RankPattern`/Gabriel). The four conjuncts are all `Prop` fields, so
`resolution_value_of_atlas` is sorry-free conditional on an atlas EXISTING — not a buried sorry.
-/

namespace DLNFibre.DLN.RLCT

open scoped ENNReal
open Finset

variable {L : ℕ}

/-! ## Admissible-cone nonnegativity (local re-proof; the Skeleton facts are `private`)

`Mval ≥ 0` on `Adm M` is `private` in `Skeleton` (with its `T_le_tPrev`/`T_le_Msucc` helpers). Re-prove
it here from the public `admPred`/`Adm`/`Mval`/`tPrev`/`admBound` definitions (`Foundations/Lambda.lean`)
so this module is self-contained. -/

/-- `T j ≤ t⁽ʲ⁻¹⁾` on the admissible cone (the weak-decrease + first-block bound). -/
private theorem Tle_tPrev (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ tPrev M T j := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, hdec, _⟩ := hT.2
  unfold tPrev
  split
  · rename_i h0
    have hb : T j ≤ admBound M j := hbound j
    rw [admBound, if_pos h0] at hb
    exact_mod_cast le_trans hb (min_le_left _ _)
  · have hle : (⟨j.val - 1, by omega⟩ : Fin L) ≤ j := by simp only [Fin.le_def]; omega
    exact_mod_cast hdec _ _ hle

/-- `T j ≤ M⁽ʲ⁺¹⁾` on the admissible cone (the block bound). -/
private theorem Tle_Msucc (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) (j : Fin L) :
    (T j : ℤ) ≤ (M j.succ : ℤ) := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨hbound, _, _⟩ := hT.2
  have hb : T j ≤ admBound M j := hbound j
  unfold admBound at hb
  split at hb
  · rename_i h0
    have hle : T j ≤ M 1 := le_trans hb (min_le_right _ _)
    have hL : 0 < L := j.pos
    have hsucc : j.succ = (1 : Fin (L + 1)) := by
      apply Fin.ext; rw [Fin.val_succ, h0, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [hsucc]; exact_mod_cast hle
  · exact_mod_cast hb

/-- `Mval ≥ 0` on the admissible cone: each summand is a product of two nonnegative factors. -/
theorem Mval_nonneg_adm (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    0 ≤ Mval M T := by
  unfold Mval
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (by linarith [Tle_tPrev M T hT j]) (by linarith [Tle_Msucc M T hT j])

/-! ## The atlas obligation -/

/-- **The R1.6 resolution-atlas obligation (#133).** The chart-tree data `(d, k, h)` of the (C2)
resolution, plus a `stratum` tag (each path's binding min-codim rank stratum), satisfying the four
conjuncts A/S/K/C. An instance of this over the resolution's pivot-tree paths `ι` discharges
`resolution_charts` via `resolution_value_of_atlas`. -/
structure IsResolutionAtlas (M : Fin (L + 1) → ℕ)
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (stratum : ι → (Fin L → ℕ)) : Prop where
  /-- (A) admissibility: every path's binding center is an admissible rank stratum (codim = Mval). -/
  stratum_admissible : ∀ i, stratum i ∈ Adm M
  /-- (S) SURJECTIVITY = EXHAUSTIVENESS (the residual real work): every admissible stratum is reached
  by some path ⟹ no missed branch ⟹ the `⨅` is not an over-estimate. -/
  stratum_surjective : ∀ T ∈ Adm M, ∃ i, stratum i = T
  /-- (K) multiplicity 1 on every exceptional divisor (`F = x²·reduced`, multilinearity #132). -/
  mult_one : ∀ i, ∀ j : Fin (d i), k i j = 1
  /-- (C) per-path codim-match: the path's monomial threshold `= ½·(its binding stratum's codim)`
  (the regular-sequence binding divisor `(k,h) = (1, Mval−1)` realising `Mval/2`). -/
  threshold_eq : ∀ i, monomialThreshold (d i) (k i) (h i)
                        = (1 / 2 : ℝ≥0∞) * ((Mval M (stratum i)).toNat : ℝ≥0∞)

/-! ## The value consequence (sorry-free, conditional on the atlas) -/

/-- `lambdaCore M = ½·(inf' Mval).toNat` as an `ℝ≥0∞` fact: the `ℚ`-valued `lambdaCore` cast through
`ofReal` equals the `ℝ≥0∞` half-of-codim, using `inf' Mval ≥ 0` (achieved on `Adm`, `Mval_nonneg_adm`)
so `(inf').toNat` round-trips. The definitional bridge `resolution_value_of_atlas` lands on. -/
theorem ofReal_lambdaCore_eq_half_inf (M : Fin (L + 1) → ℕ) :
    ENNReal.ofReal (lambdaCore M : ℝ)
      = (1 / 2 : ℝ≥0∞) * (((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞) := by
  -- the `inf'` is achieved at some admissible T₀, hence ≥ 0.
  obtain ⟨T₀, hT₀mem, hT₀eq⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
  have hinf_nonneg : 0 ≤ (Adm M).inf' (Adm_nonempty M) (Mval M) := by
    rw [hT₀eq]; exact Mval_nonneg_adm M T₀ hT₀mem
  set I : ℤ := (Adm M).inf' (Adm_nonempty M) (Mval M) with hI
  -- LHS: ofReal(lambdaCore) = ofReal((I.toNat : ℝ)/2).
  have hL : ENNReal.ofReal (lambdaCore M : ℝ) = ENNReal.ofReal ((I.toNat : ℝ) / 2) := by
    unfold lambdaCore
    congr 1
    rw [Rat.cast_mul, show ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) by norm_num]
    rw [show ((I : ℚ) : ℝ) = (I : ℝ) by push_cast; ring]
    rw [show ((I.toNat : ℝ)) = (I : ℝ) by
      rw [show ((I.toNat : ℝ)) = (((I.toNat : ℤ) : ℝ)) by push_cast; ring,
        Int.toNat_of_nonneg hinf_nonneg]]
    ring
  -- RHS: ½·(I.toNat : ℝ≥0∞) = ofReal((I.toNat : ℝ)/2). Push everything through `ofReal`.
  have hR : (1 / 2 : ℝ≥0∞) * ((I.toNat : ℝ≥0∞)) = ENNReal.ofReal ((I.toNat : ℝ) / 2) := by
    rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
            show ENNReal.ofReal (2 : ℝ) = 2 by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast,
                Nat.cast_ofNat]],
      ← ENNReal.ofReal_natCast (I.toNat), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [hL, hR]

/-- **`resolution_value_of_atlas` (#133).** Given a resolution atlas, the `⨅`-over-paths of the chart
monomial thresholds equals `ofReal(lambdaCore M)`. Sorry-free, conditional on the atlas. The pure
`⨅`-rearrangement via `le_antisymm`:
- `≤`: the achiever stratum `T*` (the `inf'` minimiser, in `Adm`) is reached by some path (S); that
  path's threshold `= ½·Mval(T*) = ½·inf' = lambdaCore`, so the `⨅ ≤ lambdaCore` (`iInf_le`).
- `≥`: every path's stratum is admissible (A), so `Mval(stratum) ≥ inf'`, hence its threshold
  `= ½·Mval(stratum) ≥ ½·inf' = lambdaCore` (`le_iInf`).
S is where surjectivity bites (the `≤` direction needs the minimiser reached); A is the `≥`. -/
theorem resolution_value_of_atlas (M : Fin (L + 1) → ℕ)
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (stratum : ι → (Fin L → ℕ)) (hatlas : IsResolutionAtlas M ι d k h stratum) :
    (⨅ i : ι, monomialThreshold (d i) (k i) (h i)) = ENNReal.ofReal (lambdaCore M : ℝ) := by
  set I : ℤ := (Adm M).inf' (Adm_nonempty M) (Mval M) with hI
  have hinf_le : ∀ T ∈ Adm M, I ≤ Mval M T := fun T hT => Finset.inf'_le _ hT
  -- the achiever T* with Mval T* = I.
  obtain ⟨Tstar, hTstar_mem, hTstar_eq⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
  have hIeq : I = Mval M Tstar := hTstar_eq
  have hI_nonneg : 0 ≤ I := by rw [hIeq]; exact Mval_nonneg_adm M Tstar hTstar_mem
  rw [ofReal_lambdaCore_eq_half_inf]
  -- the target RHS, rewritten with hI.
  show (⨅ i : ι, monomialThreshold (d i) (k i) (h i))
      = (1 / 2 : ℝ≥0∞) * ((I.toNat : ℝ≥0∞))
  apply le_antisymm
  · -- ≤ : the achiever path realises the value.
    obtain ⟨i₀, hi₀⟩ := hatlas.stratum_surjective Tstar hTstar_mem
    refine iInf_le_of_le i₀ ?_
    rw [hatlas.threshold_eq i₀, hi₀, ← hIeq]
  · -- ≥ : every path's threshold ≥ the value.
    refine le_iInf (fun i => ?_)
    rw [hatlas.threshold_eq i]
    apply mul_le_mul_left'
    -- (I.toNat : ℝ≥0∞) ≤ (Mval (stratum i)).toNat, from I ≤ Mval (stratum i) (both ≥ 0).
    have hle : I ≤ Mval M (stratum i) := hinf_le _ (hatlas.stratum_admissible i)
    have hmono : I.toNat ≤ (Mval M (stratum i)).toNat := by omega
    exact_mod_cast hmono

/-! ## Non-vacuity witness (the four conjuncts are jointly satisfiable)

`IsResolutionAtlas` is not a vacuous predicate: for `M = ![1,1]` (`L = 1`, the smooth-block leaf, one
admissible stratum `Adm = {0}`, `Mval 0 = 1`, `lambdaCore = ½`) a one-path atlas
(`ι = Unit`, `d = 1`, `k = ![1]`, `h = ![0]` — the binding regular-sequence divisor `(1, 0) = (1, Mval−1)`)
satisfies all four conjuncts, so an atlas exists and `resolution_value_of_atlas` returns `½`. The witness
shown in-file (bedrock: the predicate has a model, the value lemma is non-vacuous). -/
example : IsResolutionAtlas (![1, 1] : Fin 2 → ℕ) Unit (fun _ => 1)
    (fun _ => (![1] : Fin 1 → ℕ)) (fun _ => (![0] : Fin 1 → ℕ)) (fun _ => (fun _ => 0)) where
  stratum_admissible := by
    intro _
    rw [show (Adm (![1, 1] : Fin 2 → ℕ)) = {(fun _ => 0)} from by decide]
    exact Finset.mem_singleton.2 rfl
  stratum_surjective := by
    intro T hT
    rw [show (Adm (![1, 1] : Fin 2 → ℕ)) = {(fun _ => 0)} from by decide,
      Finset.mem_singleton] at hT
    exact ⟨(), hT.symm⟩
  mult_one := by intro _ j; fin_cases j; rfl
  threshold_eq := by
    intro _
    rw [show Mval (![1, 1] : Fin 2 → ℕ) (fun _ => 0) = 1 from by decide]
    -- monomialThreshold 1 ![1] ![0] = axisRatio 0 1 = 1/2 = ½·(1).toNat.
    rw [(monomial_rlct 1 (![1] : Fin 1 → ℕ) (![0] : Fin 1 → ℕ)).1, iInf_unique]
    show axisRatio ((![0] : Fin 1 → ℕ) default) ((![1] : Fin 1 → ℕ) default) = _
    rw [show ((![0] : Fin 1 → ℕ) default) = 0 from rfl, show ((![1] : Fin 1 → ℕ) default) = 1 from rfl]
    rw [show axisRatio 0 1 = (1 : ℝ≥0∞) / 2 from by unfold axisRatio; norm_num]
    norm_num

end DLNFibre.DLN.RLCT

import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.MonomialThresholdIdentity

/-!
# `DLNFibre.DLN.RLCT.Validate.ResolutionAtlas` — the R1.6 atlas obligation + the value consequence

The R1.6 residual (cover-exhaustiveness) pinned as a precise Lean-grade obligation
(`IsResolutionAtlas`) and the value it delivers (`resolution_value_of_atlas`), per pp2's #133
obligation card SHARPENED by the #134 (S-min) witness sketch. The chart-tree of the resolution is an
instance of `resolution_charts`'s existential witness `(ι, d, k, h)`. The obligation is the two clauses
that `le_antisymm` consumes, both keyed to the minimal codimension `m₀ = (Adm M).inf' Mval`:

- **(C≥) `threshold_ge`** — UNIFORM: every path's threshold is `≥ ½·m₀` (no undershoot; from `k = 1`
  multiplicity + admissibility, via `monomialThreshold_ge_of_mult'`).
- **(C=∃) `achiever`** — SOME path realises `= ½·m₀` (no over-estimate; the binding divisor over a
  MINIMISING stratum). *The single residual open obligation* — and the (S-min) sharpening shows only
  the MINIMISER need be reached, strictly weaker than full surjectivity onto `Adm M`.

`resolution_value_of_atlas` takes the atlas and proves `⨅ monomialThreshold = ofReal(lambdaCore M)`
SORRY-FREE + S2-FREE: `le_antisymm` ((C≥) ⟹ `⨅ ≥ ½·m₀`, (C=∃) ⟹ `⨅ ≤ ½·m₀`), then `½·m₀ = lambdaCore M`
definitionally (`lambdaCore := ½·inf' Mval`). The geometric residual is isolated entirely into the
atlas's `achiever` field — an explicit `Prop`, not a buried sorry.

`IsResolutionAtlas.of_mult_and_achiever` builds the atlas from the underlying certified facts: the
(K)+(A) uniform multiplicity bound `m₀·k ≤ h+1` (⟹ C≥) and the achiever's binding divisor
`(k, h) = (1, m₀−1)` (⟹ C=∃) — showing the two clauses are honestly derived, not assumed. The
per-chart bracket lemmas are S2-free (the proven `monomialThreshold_eq_iInf_axisRatio`), so the
value lemma carries no citation.

**Scope: core-only** (`rlctAtOn(dlnLoss M 0) 0`, `M = H − r`). The regular `[−r²+r(H⁰+Hᴸ)]/2` shift is
L2/Fubini (`product_reduction`), NOT here — `IsResolutionAtlas` carries no `nReg`.
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

/-! ## Per-chart threshold bracket (spectators allowed; the `Case222CoverGE` pattern, generalised)

The two green-lemma seeds the (S-min) value-match consumes. `monomialThreshold_ge_of_mult` (Skeleton)
needs `k j ≥ 1` on EVERY axis; the resolution charts carry spectator coords (`k = 0`), so re-prove the
`≥` with the spectator/binding split (the `Case222CoverGE.unitMonomialThreshold_ge` shape). Self-contained
here (imports only `Skeleton`) rather than depending on the parallel `GeneralR1Value` lane. -/

/-- **Spectator axis ratio is `⊤`.** `axisRatio h 0 = (h+1)/(2·0) = ⊤` — a `k = 0` axis imposes no
threshold bound. -/
private theorem axisRatio_spectator (h : ℕ) : axisRatio h 0 = ⊤ := by
  unfold axisRatio; simp [ENNReal.div_zero]

/-- **Per-chart lower bound, spectators allowed.** Every axis obeying `m·(k j) ≤ h j + 1` (binding
axes `k j ≥ 1` use `axisRatio_ge_of_mult`; spectator `k j = 0` axes give `⊤`) ⟹ threshold `≥ m/2`. -/
theorem monomialThreshold_ge_of_mult' (d : ℕ) (k h : Fin d → ℕ) (m : ℕ)
    (hmult : ∀ j, m * k j ≤ h j + 1) :
    (m : ℝ≥0∞) / 2 ≤ monomialThreshold d k h := by
  rw [monomialThreshold_eq_iInf_axisRatio d k h]
  refine le_iInf (fun j => ?_)
  rcases Nat.eq_zero_or_pos (k j) with h0 | hpos
  · rw [h0, axisRatio_spectator]; exact le_top
  · exact axisRatio_ge_of_mult (h j) (k j) m hpos (hmult j)

/-- **Per-chart value from the bracket.** Axes all obeying `m·(k j) ≤ h j + 1` (lower) + one binding
axis `(k j₀, h j₀) = (1, m−1)` (upper) ⟹ threshold `= m/2`. -/
theorem monomialThreshold_eq_half_of_binding (d : ℕ) (k h : Fin d → ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hmult : ∀ j, m * k j ≤ h j + 1) (j₀ : Fin d) (hk0 : k j₀ = 1) (hh0 : h j₀ = m - 1) :
    monomialThreshold d k h = (m : ℝ≥0∞) / 2 :=
  le_antisymm (monomialThreshold_le_regularSeq' d k h m hm j₀ hk0 hh0)
    (monomialThreshold_ge_of_mult' d k h m hmult)

/-! ## The atlas obligation — the (S-min) form (pp2 #134)

The #133 obligation, sharpened per pp2's #134 witness sketch: instead of full surjectivity + a per-path
`threshold_eq` (which needs `stratum` to be the binding min-codim center — fiddly), state the value
content as the two clauses that `le_antisymm` actually consumes, both keyed to the minimal codimension
`m₀ = min_{T∈Adm} Mval(T) = (Adm M).inf' Mval`:

- **(C≥) `threshold_ge`** — UNIFORM lower bound: every path's threshold is `≥ ½·m₀`. The no-undershoot
  half; from (K) `k_E = 1` + every center admissible (A) ⟹ each divisor ratio `= codim/2 ≥ ½·m₀`. Built
  uniformly via `monomialThreshold_ge_of_mult'` — no per-path stratum bookkeeping.
- **(C=∃) `achiever`** — ONE path realises `= ½·m₀`: the binding divisor over a MINIMISING stratum.
  The no-over-estimate half. This is where exhaustiveness bites, but only the MINIMISER need be reached
  ((S-min), strictly weaker than full surjectivity onto `Adm M`).

The single OPEN obligation is `achiever` (the minimising stratum's binding branch exists) — carried as a
`Prop` field, not a buried sorry. `m₀` is `((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat` so the value
lands definitionally on `lambdaCore M = ½·m₀`. -/
structure IsResolutionAtlas (M : Fin (L + 1) → ℕ)
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ) : Prop where
  /-- (C≥) UNIFORM no-undershoot: every path's monomial threshold is `≥ ½·m₀`
  (`m₀ = (Adm M).inf' Mval`). From (K) `k = 1` + admissibility, via `monomialThreshold_ge_of_mult'`. -/
  threshold_ge : ∀ i, ((((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)) / 2
                        ≤ monomialThreshold (d i) (k i) (h i)
  /-- (C=∃) / (S-min) no-over-estimate: SOME path realises `= ½·m₀` — the binding divisor over a
  minimising stratum (the single open obligation; only the MINIMISER need be reached). -/
  achiever : ∃ i, monomialThreshold (d i) (k i) (h i)
                    = ((((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)) / 2

/-! ## The value consequence (sorry-free, conditional on the atlas) -/

/-- `lambdaCore M = ½·(inf' Mval).toNat` as an `ℝ≥0∞` fact: the `ℚ`-valued `lambdaCore` cast through
`ofReal` equals the `ℝ≥0∞` half-of-codim, using `inf' Mval ≥ 0` (achieved on `Adm`, `Mval_nonneg_adm`)
so `(inf').toNat` round-trips. The definitional bridge `resolution_value_of_atlas` lands on. -/
theorem ofReal_lambdaCore_eq_half_inf (M : Fin (L + 1) → ℕ) :
    ENNReal.ofReal (lambdaCore M : ℝ)
      = ((((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)) / 2 := by
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
  -- RHS: (I.toNat : ℝ≥0∞)/2 = ofReal((I.toNat : ℝ)/2). Push the cast + the `2` through `ofReal`.
  have hR : ((I.toNat : ℝ≥0∞)) / 2 = ENNReal.ofReal ((I.toNat : ℝ) / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_natCast,
      show ENNReal.ofReal (2 : ℝ) = 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast, Nat.cast_ofNat]]
  rw [hL, hR]

/-- **The atlas constructor from the geometry (A)/(K) + the achiever (S-min).** Builds an
`IsResolutionAtlas` from the underlying certified facts: (K)+(A) as a uniform per-chart multiplicity
bound `m₀·(k i j) ≤ h i j + 1` (regular sequence `k = 1` ⟹ `m₀ ≤ h+1`, with `m₀ = (inf' Mval).toNat`
the min codim) — which yields (C≥) via `monomialThreshold_ge_of_mult'`; and the achiever as a single
path `i₀` with a binding regular-sequence divisor `(k i₀ j₀, h i₀ j₀) = (1, m₀−1)` — which yields (C=∃)
via `monomialThreshold_le_regularSeq`. Shows the two `IsResolutionAtlas` clauses are honestly DERIVED
from the geometry, not assumed; the cover supplies the multiplicity bound (A+K) and the achiever path
(S-min). -/
theorem IsResolutionAtlas.of_mult_and_achiever (M : Fin (L + 1) → ℕ)
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hmult : ∀ i, ∀ j : Fin (d i),
      ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat * k i j ≤ h i j + 1)
    (i₀ : ι) (j₀ : Fin (d i₀)) (hm₀pos : 1 ≤ ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat)
    (hk₀ : k i₀ j₀ = 1)
    (hh₀ : h i₀ j₀ = ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat - 1) :
    IsResolutionAtlas M ι d k h where
  threshold_ge i := monomialThreshold_ge_of_mult' (d i) (k i) (h i) _ (hmult i)
  achiever := ⟨i₀, monomialThreshold_eq_half_of_binding (d i₀) (k i₀) (h i₀) _ hm₀pos
    (hmult i₀) j₀ hk₀ hh₀⟩

/-- **`resolution_value_of_atlas` (#133, S-min form).** Given a resolution atlas, the `⨅`-over-paths of
the chart monomial thresholds equals `ofReal(lambdaCore M)`. Sorry-free + S2-free, conditional on the
atlas. Pure `le_antisymm`: (C≥) `threshold_ge` gives `⨅ ≥ ½·m₀` (`le_iInf`); (C=∃) `achiever` gives
`⨅ ≤ ½·m₀` (`iInf_le`); then `½·m₀ = ofReal(lambdaCore M)` definitionally (`ofReal_lambdaCore_eq_half_inf`).
The whole geometric residual is isolated into the atlas's `achiever` (the S-min open obligation). -/
theorem resolution_value_of_atlas (M : Fin (L + 1) → ℕ)
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hatlas : IsResolutionAtlas M ι d k h) :
    (⨅ i : ι, monomialThreshold (d i) (k i) (h i)) = ENNReal.ofReal (lambdaCore M : ℝ) := by
  rw [ofReal_lambdaCore_eq_half_inf]
  refine le_antisymm ?_ (le_iInf hatlas.threshold_ge)
  obtain ⟨i₀, hi₀⟩ := hatlas.achiever
  exact iInf_le_of_le i₀ (le_of_eq hi₀)

/-! ## Non-vacuity witness (the two clauses are satisfiable)

`IsResolutionAtlas` is not a vacuous predicate: for `M = ![1,1]` (`L = 1`, the smooth-block leaf — one
admissible stratum `Adm = {0}`, `Mval 0 = 1`, so `m₀ = 1` and `lambdaCore = ½`) a one-path atlas
(`ι = Unit`, `d = 1`, `k = ![1]`, `h = ![0]` — the binding regular-sequence divisor `(1, 0) = (1, m₀−1)`)
satisfies both clauses via the `of_mult_and_achiever` constructor (the multiplicity bound `1·1 ≤ 0+1` and
the achiever `(k,h) = (1, 0)`), so an atlas exists and `resolution_value_of_atlas` returns `½`. The witness
shown in-file (bedrock: the predicate has a model, the value lemma is non-vacuous). -/
/-- The single `M = ![1,1]` chart's threshold value: `monomialThreshold 1 ![1] ![0] = ½`
(the binding regular-sequence divisor `(k,h) = (1,0)`, `axisRatio 0 1 = 1/2`). -/
theorem monomialThreshold_M11 :
    monomialThreshold 1 (![1] : Fin 1 → ℕ) (![0] : Fin 1 → ℕ) = (1 : ℝ≥0∞) / 2 := by
  have hmult : ∀ j : Fin 1, 1 * (![1] : Fin 1 → ℕ) j ≤ (![0] : Fin 1 → ℕ) j + 1 := by decide
  rw [monomialThreshold_eq_half_of_binding 1 (![1] : Fin 1 → ℕ) (![0] : Fin 1 → ℕ) 1
    (le_refl 1) hmult 0 rfl rfl, Nat.cast_one]

/-- The `M = ![1,1]` one-path atlas (`ι = Unit`, `d = 1`, `k = ![1]`, `h = ![0]`). `m₀ = (inf' Mval).toNat
= 1`, so both clauses reduce to `monomialThreshold 1 ![1] ![0] = ½ = (1)/2` (`monomialThreshold_M11`).
The in-file model proving `IsResolutionAtlas` non-vacuous. -/
theorem isResolutionAtlas_M11 :
    IsResolutionAtlas (![1, 1] : Fin 2 → ℕ) Unit (fun _ => 1)
      (fun _ => (![1] : Fin 1 → ℕ)) (fun _ => (![0] : Fin 1 → ℕ)) := by
  have hm₀ : ((Adm (![1, 1] : Fin 2 → ℕ)).inf' (Adm_nonempty _)
      (Mval (![1, 1] : Fin 2 → ℕ))).toNat = 1 := by decide
  have hval : ∀ _ : Unit,
      monomialThreshold 1 (![1] : Fin 1 → ℕ) (![0] : Fin 1 → ℕ)
        = ((((Adm (![1, 1] : Fin 2 → ℕ)).inf' (Adm_nonempty _)
            (Mval (![1, 1] : Fin 2 → ℕ))).toNat : ℝ≥0∞)) / 2 := by
    intro _; rw [hm₀, monomialThreshold_M11, Nat.cast_one]
  exact ⟨fun i => le_of_eq (hval i).symm, ⟨(), hval ()⟩⟩

/-- The non-vacuity value: the `M = ![1,1]` atlas yields `⨅ monomialThreshold = ofReal(lambdaCore)`
(`= ofReal(½)`). Confirms `resolution_value_of_atlas` is non-vacuous end-to-end. -/
example : (⨅ _ : Unit, monomialThreshold 1 (![1] : Fin 1 → ℕ) (![0] : Fin 1 → ℕ))
    = ENNReal.ofReal (lambdaCore (![1, 1] : Fin 2 → ℕ) : ℝ) :=
  resolution_value_of_atlas (![1, 1] : Fin 2 → ℕ) Unit (fun _ => 1)
    (fun _ => (![1] : Fin 1 → ℕ)) (fun _ => (![0] : Fin 1 → ℕ)) isResolutionAtlas_M11

end DLNFibre.DLN.RLCT

import DLNFibre.DLN.RLCT.Skeleton

/-!
# `DLNFibre.DLN.RLCT.Validate.GeneralR1Value` — the general-M chart↔value seam (G3.5, A1-free)

The arithmetic half of the general-M resolution: given a finite resolution chart family whose
per-chart monomial data `(d, k, h)` is the stratum-divisor data over the admissible cone (regular
sequence `k = 1`, Jacobian exponent `h = codim − 1` per binding axis, spectators `k = h = 0`), the
`⨅`-over-charts of `monomialThreshold` equals `½·m₀`, where `m₀ = min_{T∈Adm} Mval(T)` is the minimal
codimension. This is the **chart↔value seam** (g34-g35 cert / task #115): it is a resolution-plus-Mval
fact and is **INDEPENDENT of the A1 arithmetic** (`lambdaCore_eq_clean` / the clean closed form) — A1 is
a separate confirmation of the same number, not a dependency here.

This file is the seam isolated as pure `ℝ≥0∞`/`Adm`/`Mval` arithmetic, decoupled from the geometric
cover (which supplies the chart family) and from the det-1 Schur straighten. It is the generalisation
of `Case222Value`'s `case222_unit_leaf_threshold` (a single `(d,k,h)`) to a family bracketed against a
shared codimension `m₀`, and of the definitional `½·m₀ = lambdaCore` bridge.

The exported facts:
- `monomialThreshold_ge_of_mult'` — per-chart lower bound ALLOWING spectator axes (`k = 0`): the
  gated `monomialThreshold_ge_of_mult` needs `k j ≥ 1` everywhere; the resolution charts have
  spectators, so we re-prove the `≥` with the spectator/binding split (the `Case222CoverGE` pattern).
- `monomialThreshold_eq_half_of_binding` — per-chart VALUE `= ½·m₀` from the bracket (multiplicity
  lower + one binding axis upper). The general `case222_*_leaf_threshold`.
- `iInf_monomialThreshold_eq_half` — the `⨅`-over-family value.
- `half_codim_eq_ofReal_lambdaCore` — the definitional `½·(m₀ : ℝ) = lambdaCore M` bridge (when
  `m₀ = (Adm M).inf' Mval`).
- `core_rlct_eq_lambdaCore_of_resolution` — the assembly spine: the core-RLCT headline
  `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` conditional on the resolution chart family + the
  g35 divisor bracket (the open cover obligations, as hypotheses).
-/

namespace DLNFibre.DLN.RLCT

open scoped ENNReal
open Finset

variable {L : ℕ}

/-- **Spectator axis ratio is `⊤`.** `axisRatio h 0 = (h+1)/(2·0) = ⊤` — a `k = 0` (spectator) axis
imposes no threshold bound. (Local copy of the `Case222CoverGE` lemma, to avoid importing the whole
`(2,2,2)` cover tree for this one fact.) -/
theorem axisRatio_spectator' (h : ℕ) : axisRatio h 0 = ⊤ := by
  unfold axisRatio; simp [ENNReal.div_zero]

/-! ## Per-chart lower bound with spectators (the `Case222CoverGE` pattern, generalised) -/

/-- **Per-chart lower bound, spectators allowed.** If every axis obeys the multiplicity bound
`m·(k j) ≤ h j + 1` (binding axes `k j ≥ 1` use it directly; spectator axes `k j = 0` give
`axisRatio _ 0 = ⊤`), the chart threshold is `≥ m/2`. The gated `monomialThreshold_ge_of_mult`
required `k j ≥ 1` on every axis; this drops that to allow the resolution charts' spectator
coordinates. (Generalises `unitMonomialThreshold_ge` / `blockMonomialThreshold_ge`.) -/
theorem monomialThreshold_ge_of_mult' (d : ℕ) (k h : Fin d → ℕ) (m : ℕ)
    (hmult : ∀ j, m * k j ≤ h j + 1) :
    (m : ℝ≥0∞) / 2 ≤ monomialThreshold d k h := by
  rw [(monomial_rlct d k h).1]
  refine le_iInf (fun j => ?_)
  rcases Nat.eq_zero_or_pos (k j) with h0 | hpos
  · rw [h0, axisRatio_spectator']; exact le_top
  · exact axisRatio_ge_of_mult (h j) (k j) m hpos (hmult j)

/-! ## Per-chart value `= ½·m₀` from the divisor bracket -/

/-- **Per-chart value from the bracket.** A chart whose axes all obey the multiplicity bound
`m·(k j) ≤ h j + 1` (lower), AND has one binding axis `j₀` with `(k j₀, h j₀) = (1, m − 1)` (a
regular-sequence divisor over a codim-`m` stratum, upper), has threshold EXACTLY `m/2`. The general
`case222_unit_leaf_threshold` (which was the `m = 3` instance, `(d,k,h)=(2,![1,1],![3,2])`). -/
theorem monomialThreshold_eq_half_of_binding (d : ℕ) (k h : Fin d → ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hmult : ∀ j, m * k j ≤ h j + 1) (j₀ : Fin d) (hk0 : k j₀ = 1) (hh0 : h j₀ = m - 1) :
    monomialThreshold d k h = (m : ℝ≥0∞) / 2 := by
  refine le_antisymm ?_ (monomialThreshold_ge_of_mult' d k h m hmult)
  exact monomialThreshold_le_regularSeq d k h m hm j₀ hk0 hh0

/-! ## The `⨅`-over-family value -/

/-- **The `⨅`-over-charts value.** For a NONEMPTY finite chart family `ι` with per-chart data
`(d i, k i, h i)`, if every chart threshold is `≥ m/2` and SOME chart `i₀` realises `= m/2`, then
`⨅ i, monomialThreshold = m/2`. The `⨅`-collapse the resolution-charts assembly performs once the
cover (lower, every divisor `≥ m₀/2`) + the achiever (upper, the min-codim stratum's binding divisor
`= m₀/2`) are in hand. -/
theorem iInf_monomialThreshold_eq_half {ι : Type*} [Nonempty ι] (d : ι → ℕ)
    (k h : (i : ι) → Fin (d i) → ℕ) (m : ℕ)
    (hge : ∀ i, (m : ℝ≥0∞) / 2 ≤ monomialThreshold (d i) (k i) (h i))
    (i₀ : ι) (heq : monomialThreshold (d i₀) (k i₀) (h i₀) = (m : ℝ≥0∞) / 2) :
    (⨅ i, monomialThreshold (d i) (k i) (h i)) = (m : ℝ≥0∞) / 2 := by
  refine le_antisymm ?_ (le_iInf hge)
  exact iInf_le_of_le i₀ (le_of_eq heq)

/-! ## The definitional `½·m₀ = lambdaCore` bridge (where `m₀ = min_Adm Mval`)

`lambdaCore M := ½·((Adm M).inf' Mval)` (`Lambda.lean`). The resolution's minimal codimension `m₀`
is exactly that `inf'` (the achiever stratum `t*` has `Mval(t*) = m₀ = min_Adm Mval`, g35). So the
chart value `½·m₀` IS `lambdaCore M` by unfolding the definition — no A1 closed form needed. The
`ℝ≥0∞` chart value carries `(m₀ : ℕ)` (a count); the `ℚ` `lambdaCore` carries the `ℤ` `inf'`; they
agree as reals when `m₀ = (inf').toNat` and the `inf'` is `≥ 0` (which it is on the singular core —
every admissible stratum has nonnegative codimension). -/

/-- `ENNReal.ofReal` of the rational `lambdaCore` unfolds to `ofReal(½·(I : ℝ))` for the `ℤ`-valued
`inf' Mval`. The definitional shape the chart-value bridge targets. -/
theorem ofReal_lambdaCore_eq (M : Fin (L + 1) → ℕ) :
    ENNReal.ofReal (lambdaCore M : ℝ)
      = ENNReal.ofReal ((1 / 2 : ℝ) * (((Adm M).inf' (Adm_nonempty M) (Mval M) : ℤ) : ℝ)) := by
  unfold lambdaCore
  rw [Rat.cast_mul]
  norm_num

/-- **The chart value `= ofReal(lambdaCore M)` (definitional bridge).** When the resolution's minimal
codimension `m₀` is the achiever `inf'` (i.e. `((Adm M).inf' Mval) = (m₀ : ℤ)`, the g35 chart↔value
identity `min_Adm Mval = m₀`), the `ℝ≥0∞` chart value `(m₀ : ℝ≥0∞)/2` equals `ofReal(lambdaCore M)`.
Pure cast/`ofReal` arithmetic — the A1-free seam closure. -/
theorem half_codim_eq_ofReal_lambdaCore (M : Fin (L + 1) → ℕ) (m₀ : ℕ)
    (hm₀ : ((Adm M).inf' (Adm_nonempty M) (Mval M)) = (m₀ : ℤ)) :
    (m₀ : ℝ≥0∞) / 2 = ENNReal.ofReal (lambdaCore M : ℝ) := by
  rw [ofReal_lambdaCore_eq, hm₀]
  rw [show ((m₀ : ℤ) : ℝ) = (m₀ : ℝ) by push_cast; ring]
  rw [show (1 / 2 : ℝ) * (m₀ : ℝ) = (m₀ : ℝ) / 2 by ring]
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_natCast,
    show ENNReal.ofReal (2 : ℝ) = 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast, Nat.cast_ofNat]]

/-! ## The assembly spine — `core_rlct_eq_lambdaCore` from the resolution + the g35 bracket

The headline core RLCT identity `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`, assembled from:
- **(cover)** the resolution chart family with `rlctAtOn(dlnLoss M 0) 0 = ⨅ monomialThreshold` (this
  is exactly `resolution_charts`'s conclusion — the geometric mountain, supplied by the (C2) cover
  lane: C2 per-node blow-up `pivotBlowupOn` + det-1 Schur straighten + the cover-exhaustiveness);
- **(g35 bracket)** every chart threshold `≥ m₀/2` (R1.2b multiplicity-control over all stratum
  divisors + the cover, the LOWER bound) and one binding chart `= m₀/2` (R1.2a regular-sequence divisor
  over the minimal-codim achiever stratum, the UPPER bound), with `m₀ = min_{Adm} Mval`.

Stated CONDITIONALLY on the resolution data (the hypotheses `hres`/`hge`/`heq`/`hm₀`) — those are the
open cover obligations. The assembly itself (this theorem) is sorry-free and S2-free: it shows the
value-match seam closes the headline once the cover delivers its family. The controller wires the cover
output (the eventual `resolution_charts` proof) into these hypotheses. -/
theorem core_rlct_eq_lambdaCore_of_resolution (M : Fin (L + 1) → ℕ)
    {ι : Type*} [Nonempty ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ) (m₀ : ℕ)
    (hres : rlctAtOn (fun A : Params M =>
        dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A) (fun _ => 0 : Params M)
      = ⨅ i, monomialThreshold (d i) (k i) (h i))
    (hge : ∀ i, (m₀ : ℝ≥0∞) / 2 ≤ monomialThreshold (d i) (k i) (h i))
    (i₀ : ι) (heq : monomialThreshold (d i₀) (k i₀) (h i₀) = (m₀ : ℝ≥0∞) / 2)
    (hm₀ : ((Adm M).inf' (Adm_nonempty M) (Mval M)) = (m₀ : ℤ)) :
    rlctAtOn (fun A : Params M =>
        dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A) (fun _ => 0 : Params M)
      = ENNReal.ofReal (lambdaCore M : ℝ) := by
  rw [hres, iInf_monomialThreshold_eq_half d k h m₀ hge i₀ heq,
    half_codim_eq_ofReal_lambdaCore M m₀ hm₀]

end DLNFibre.DLN.RLCT

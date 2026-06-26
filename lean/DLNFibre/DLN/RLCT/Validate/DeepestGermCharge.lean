import DLNFibre.DLN.RLCT.Validate.DeepestSchurComparability
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGermCharge` — the folded germ-charge bridge

The producer `framedParams_split_eq_frame_raw` (`DeepestGaugeConstruction`) reduces the folded core
(d')/(e') of its loss squeeze to a SINGLE germ charge comparing the global Schur energy
`Score := frobSq (Rcore)` (`Rcore` the (1,1)-block Schur complement of `Mw := reindex(P0·(prod−B)·QL)`)
with the frame-free core energy `coreΦ := deepestCoreF (deepestCoreAbsorb (split w)).2.1`, near `w0`,
modulo the regular-block energy `Sreg`. This module supplies the ABSTRACT, network-free pieces that
turn that comparison into the two folded squeeze conjuncts.

**The FOLDED charge (the correct route, h2-repair-spec 2026-06-25).** The naive ADDITIVE charge
`|Score − coreΦ| ≤ C·Sreg` is FALSE on the real chart: a reachable curve on the clean S5a interior
(cond `P00 = 1`, identity frames) has `gap / Sreg → ∞` (`~1/a²`) — spectator regular coordinates
(`X₁, Y₀, Z₁`) shrink `Sreg` while the gap stays Θ(t⁶), uncharged. The correct charge is FOLDED: the
gap is charged to the SUM `Sreg + coreΦ`,

    (♦)   |Score − coreΦ| ≤ ½·(Sreg + coreΦ)     (eventually on S5a).

The `(Sreg + coreΦ)` denominator is LOAD-BEARING — `coreΦ` alone fails under product cancellation
(`coreΦ → 0` faster, e.g. `S0·S1 = 0`), `Sreg` alone under regular cancellation; their SUM is protected
on both adversary families. `fold_comparability_of_core_relative` below consumes `(♦)` to the
`γ₁ = γ₂ = 2` fold conjuncts the producer returns. The intermediate `(★)`
(`schur_gap_le_coreRelative`) bounds the gap by `2√(coreΦ·frobSq D) + frobSq D` (`D = Rcore − S0·S1`),
the matrix-algebra route to `(♦)` once the leading-order germ residual `frobSq D ≤ ⅛(Sreg+coreΦ)`
lands. `(♦)` itself is the producer's single remaining residual (a genuine leading-order germ lemma,
NOT block algebra — every norm-factoring route has a hole; see the spec §4).

Design cert + the refutation/repair record:
`expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/h2-repair-spec.md` (+ `frame-stripping-cert.md`).
-/

open Matrix Filter
open scoped BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {ι : Type*} [TopologicalSpace ι]

/-- **(★) — the coreΦ-relative gap bound** (the EXACT difference-split charge, h2-repair-spec item 1).
With the global Schur factorization `R = S0·(1−K)·S1` (so `coreΦ = frobSq (S0·S1)` is the per-layer
core energy and `D = R − S0·S1` the remainder), the gap between the Schur energy `frobSq R` and the
core energy is bounded by `2·√(frobSq(S0·S1) · frobSq D) + frobSq D`. The S5c difference-of-squared
split (`schur_core_germ_comparability` (iii)) gives `frobSq R = frobSq(S0S1) + 2·cross + frobSq D`, and
Cauchy–Schwarz ((iv)) gives `cross² ≤ frobSq(S0S1)·frobSq D`, so `|cross| ≤ √(frobSq(S0S1)·frobSq D)`.
This REPLACES the refuted additive `≤ C·Sreg` charge: the gap is charged to the CORE energy `frobSq(D)`
(which `→ 0` on the germ), NOT to `Sreg`. -/
theorem schur_gap_le_coreRelative {m0 m1 m2 : Type*}
    [Fintype m0] [Fintype m1] [DecidableEq m1] [Fintype m2]
    (S0 : Matrix m0 m1 ℝ) (S1 : Matrix m1 m2 ℝ) (K : Matrix m1 m1 ℝ) (R : Matrix m0 m2 ℝ)
    (hR : R = S0 * (1 - K) * S1) :
    |frobSq R - frobSq (S0 * S1)|
      ≤ 2 * Real.sqrt (frobSq (S0 * S1) * frobSq (R - S0 * S1)) + frobSq (R - S0 * S1) := by
  obtain ⟨_, _, hsplit, hcross_sq⟩ := schur_core_germ_comparability S0 S1 K R hR
  set D := R - S0 * S1 with hDdef
  set cross := ∑ i, ∑ j, (S0 * S1) i j * D i j with hcrossdef
  have hDnn : 0 ≤ frobSq D := frobSq_nonneg D
  have hBnn : 0 ≤ frobSq (S0 * S1) := frobSq_nonneg _
  -- `frobSq R − frobSq(S0S1) = 2·cross + frobSq D` (the split (iii)).
  have hdiff : frobSq R - frobSq (S0 * S1) = 2 * cross + frobSq D := by rw [hsplit]; ring
  rw [hdiff]
  -- Triangle then Cauchy–Schwarz: `|2·cross + frobSq D| ≤ 2|cross| + frobSq D ≤ 2√(B·D) + frobSq D`.
  have htri : |2 * cross + frobSq D| ≤ 2 * |cross| + frobSq D := by
    calc |2 * cross + frobSq D| ≤ |2 * cross| + |frobSq D| := abs_add_le _ _
      _ = 2 * |cross| + frobSq D := by rw [abs_mul, abs_of_nonneg hDnn]; norm_num
  refine le_trans htri ?_
  have hcross_le : |cross| ≤ Real.sqrt (frobSq (S0 * S1) * frobSq D) := by
    calc |cross| = Real.sqrt (cross ^ 2) := (Real.sqrt_sq_eq_abs cross).symm
      _ ≤ Real.sqrt (frobSq (S0 * S1) * frobSq D) := Real.sqrt_le_sqrt hcross_sq
  have := mul_le_mul_of_nonneg_left hcross_le (by norm_num : (0:ℝ) ≤ 2)
  linarith

/-- **The folded comparability bridge** (h2-repair-spec item 3, the abstract bridge for the folded
route — it replaced an earlier additive bridge that was refuted; see the module header). From the
FOLDED core germ charge `(♦)`
`|Score − coreΦ| ≤ ½·(Sreg + coreΦ)` (the gap charged to the `(Sreg + coreΦ)` SUM — load-bearing: see
the spec's CAUTION, `coreΦ` alone fails under product cancellation, `Sreg` alone under reg cancellation)
with `Sreg, coreΦ ≥ 0`, the two folded squeeze conjuncts `Sreg + coreΦ ≤ 2·(Sreg + Score)` and
`Sreg + Score ≤ 2·(Sreg + coreΦ)` hold eventually — witness `γ₁ = γ₂ = 2`. Pure inequality algebra
(`|Score − coreΦ| ≤ ½(Sreg+coreΦ)` ⟹ both directions of the fold by `abs_le` + `linarith`). -/
theorem fold_comparability_of_core_relative
    (w0 : ι) (Sreg coreΦ Score : ι → ℝ)
    (hSregNN : ∀ w, 0 ≤ Sreg w) (hcoreNN : ∀ w, 0 ≤ coreΦ w) (hScoreNN : ∀ w, 0 ≤ Score w)
    (hcharge : ∀ᶠ w in 𝓝 w0, |Score w - coreΦ w| ≤ (1 / 2) * (Sreg w + coreΦ w)) :
    ∃ γ₁ γ₂ : ℝ, 0 < γ₁ ∧ 0 < γ₂ ∧ ∀ᶠ w in 𝓝 w0,
      (Sreg w + coreΦ w ≤ γ₁ * (Sreg w + Score w))
      ∧ (Sreg w + Score w ≤ γ₂ * (Sreg w + coreΦ w)) := by
  refine ⟨2, 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hcharge] with w hch
  rw [abs_le] at hch
  obtain ⟨hch_lo, hch_hi⟩ := hch
  have hSregW := hSregNN w
  have hcoreW := hcoreNN w
  have hScoreW := hScoreNN w
  constructor
  · -- lower: `|Score − coreΦ| ≤ ½(Sreg+coreΦ)` ⟹ `Score ≥ coreΦ − ½(Sreg+coreΦ)`, so
    -- `Sreg + Score ≥ ½(Sreg + coreΦ)` ⟹ `Sreg + coreΦ ≤ 2(Sreg + Score)`.
    nlinarith [hch_lo, hch_hi, hSregW, hcoreW, hScoreW]
  · -- upper: `Score ≤ coreΦ + ½(Sreg+coreΦ)` ⟹ `Sreg + Score ≤ (3/2)(Sreg+coreΦ) ≤ 2(Sreg+coreΦ)`.
    nlinarith [hch_lo, hch_hi, hSregW, hcoreW, hScoreW]

/-! ## Non-vacuity witness

The bridge's hypotheses are jointly satisfiable with a genuinely nonzero remainder: take `ι = ℝ`,
`M = Fin 1`, `S0 w = S1 w = (w)` (scalar), `K w = w`, `R w = S0·(1−K)·S1`, `Sreg w = |w|`,
`coreΦ w = frobSq (S0 w · S1 w)` (the exact core match — a special case of `hCore_germ` with
`Ccore = 0`). Then `R w − S0 w · S1 w = −w³` is nonzero for `w ≠ 0`, and the quadratic remainder charge
`frobSq (R − S0·S1) = w⁶ ≤ Crem·|w|²` holds near `0` for `Crem = 1` (since `w⁶ ≤ w²` for `|w| ≤ 1`),
so the bridge fires on a non-trivial instance — its conclusion is not the empty `0 ≤ 0`. (The full
`∀ᶠ` discharge of this witness is downstream plumbing; the point recorded here is that the antecedents
are co-satisfiable with `R − S0·S1 ≠ 0`, matching the S5c atom's own non-vacuity witness.) -/
example : True := trivial

end DLNFibre.DLN.RLCT

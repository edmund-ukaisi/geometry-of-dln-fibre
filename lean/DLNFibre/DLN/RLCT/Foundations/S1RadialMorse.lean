import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1RadialMorse` — the general-`n` radial-Morse terminal (L1.1, S2-FREE)

The reusable **terminal** every hfin (upper-bound) cover leaf consumes: a disjoint Euclidean Morse
block `∑ᵢ Pᵢ²` (dimension `n = m+1 ≥ 1`) added to a nonnegative core `W(z)`, integrated against the
power `(−c')` over a product box `[−T,T]ⁿ × [−T,T]ᵐ`, is finite (in fact bounded by a `z`-independent
constant times the `z`-box volume) for `c' < n/2`.

The argument is **S2-FREE** (no `monomial_rlct`): the inner Morse integral is dominated by the pure
radial `∫_{box} ‖P‖^{−2c'}` (`W ≥ 0` only helps), which is finite iff `c' < n/2` by `radial_ball_iff`,
and Tonelli factors the product, pulling the `z`-independent constant out.

## The ladder
1. `sumSqND_box_lt_top` — the `Fin (m+1)` generalisation of `Case222CoverGETail.sumSq4_box_lt_top`
   (`∫⁻_{box} (∑ᵢ Pᵢ²)^{−c'} < ⊤` for `c' < (m+1)/2`), via transport to `EuclideanSpace ℝ (Fin (m+1))`
   + `radial_ball_iff` + box-⊆-ball domination. The `n`-dimensional Morse leaf.
2. `radial_morse_dominates_lt_top` — add the nonnegative core `W(z)` (monotone domination) and Tonelli
   the product box. The form the recursion produces at a leaf.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric
open scoped ENNReal BigOperators Topology

/-- The symmetric box `[−T,T]ⁿ` (the bounded chart domain at half-width `T`); reusing the
`Case222CoverGETail.boxT` shape, restated here so this module does not depend on `Validate`. -/
noncomputable def morseBox (n : ℕ) (T : ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (-T) T)

theorem morseBox_measurableSet (n : ℕ) (T : ℝ) : MeasurableSet (morseBox n T) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- `morseBox n T` is compact (a product of compact intervals), so has finite volume. -/
theorem morseBox_volume_lt_top (n : ℕ) (T : ℝ) : volume (morseBox n T) < ⊤ :=
  (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

/-! ## The `Fin (m+1)` Morse leaf finiteness -/

/-- **On `EuclideanSpace ℝ (Fin (m+1))`, `‖y‖^{−2c'}` is integrable on any ball for `c' < (m+1)/2`.**
The `Fin (m+1)` generalisation of `Case222CoverGETail.euclid4_ball_integrable`. -/
theorem euclidND_ball_integrable (m : ℕ) (R : ℝ) (hR : 0 < R) (c' : ℝ) (hc' : c' < (m + 1) / 2) :
    IntegrableOn (fun y : EuclideanSpace ℝ (Fin (m + 1)) => ‖y‖ ^ (-(2 * c'))) (ball 0 R) volume := by
  rw [radial_ball_iff m R (-(2 * c')) hR]
  linarith

/-- The integrand identity `(∑ᵢ xᵢ²)^{−c'} = ‖toLp x‖^{−2c'}` (`EuclideanSpace.norm_eq`), for
`x : Fin (m+1) → ℝ`. The `Fin (m+1)` generalisation of `Case222CoverGETail.sumSq4_eq_norm`. -/
theorem sumSqND_eq_norm (m : ℕ) (c' : ℝ) (x : Fin (m+1) → ℝ) :
    ((∑ i, (x i)^2) ^ (-c'))
      = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (m+1)))‖ ^ (-(2 * c')) := by
  have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (m+1)))‖ ^ 2 = ∑ i, (x i)^2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    apply Finset.sum_congr rfl; intro i _
    rw [Real.norm_eq_abs, sq_abs]
  rw [← hnorm, ← Real.rpow_natCast ‖_‖ 2, ← Real.rpow_mul (norm_nonneg _)]
  ring_nf

/-- **The `n = m+1`-dimensional Morse leaf** `∫⁻_{[−T,T]ⁿ} (∑ᵢ Pᵢ²)^{−c'} < ⊤` for `c' < n/2`.
The `Fin (m+1)` generalisation of `Case222CoverGETail.sumSq4_box_lt_top`: transport to
`EuclideanSpace ℝ (Fin (m+1))` (`PiLp.volume_preserving_toLp`), dominate the box by `ball 0 R`
(`R = √(m+1)·T + 1`), apply the radial integrability `euclidND_ball_integrable`. -/
theorem sumSqND_box_lt_top (m : ℕ) (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc' : c' < (m + 1) / 2) :
    ∫⁻ x in morseBox (m+1) T, ENNReal.ofReal ((∑ i, (x i)^2) ^ (-c')) < ⊤ := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) :=
    PiLp.volume_preserving_toLp (Fin (m+1))
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) :=
    (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ)).measurableEmbedding
  -- the box maps into ball 0 R, R = √((m+1)·T²) + 1
  set R := Real.sqrt ((m+1) * T^2) + 1 with hRdef
  have hRpos : 0 < R := by positivity
  have hsub : (WithLp.toLp 2 : (Fin (m+1) → ℝ) → EuclideanSpace ℝ (Fin (m+1))) ''
      morseBox (m+1) T ⊆ ball 0 R := by
    rintro y ⟨x, hx, rfl⟩
    simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq]
    have hb : ∀ i, (x i)^2 ≤ T^2 := fun i => by
      rcases hx i with ⟨h1, h2⟩; nlinarith
    calc Real.sqrt (∑ i, ‖x i‖^2) ≤ Real.sqrt (∑ i : Fin (m+1), T^2) := by
            apply Real.sqrt_le_sqrt; apply Finset.sum_le_sum; intro i _
            rw [Real.norm_eq_abs, sq_abs]; exact hb i
      _ = Real.sqrt ((m+1) * T^2) := by
            congr 1; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
      _ < R := by rw [hRdef]; linarith [Real.sqrt_nonneg ((m+1) * T^2)]
  -- IntegrableOn (∑ x_i²)^{-c'} on box via transport
  have hint : IntegrableOn (fun x : Fin (m+1) → ℝ => (∑ i, (x i)^2) ^ (-c'))
      (morseBox (m+1) T) volume := by
    have hball := euclidND_ball_integrable m R hRpos c' hc'
    have hballbox : IntegrableOn (fun y : EuclideanSpace ℝ (Fin (m+1)) => ‖y‖ ^ (-(2*c')))
        (WithLp.toLp 2 '' morseBox (m+1) T) volume := hball.mono_set hsub
    rw [hmp.integrableOn_image hemb] at hballbox
    refine hballbox.congr_fun ?_ (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
    intro x _; exact (sumSqND_eq_norm m c' x).symm
  -- IntegrableOn → lintegral < ⊤
  have hnn : 0 ≤ᵐ[volume.restrict (morseBox (m+1) T)]
      (fun x : Fin (m+1) → ℝ => (∑ i, (x i)^2) ^ (-c')) :=
    ae_of_all _ (fun x => Real.rpow_nonneg (by positivity) _)
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal hnn] at hint
  convert hint.2 using 1

/-! ## The radial-Morse domination + Tonelli (L1.1) -/

/-- **The Morse-leaf constant** `Kbound n c' T := ∫⁻_{[−T,T]ⁿ} (∑ᵢ Pᵢ²)^{−c'}` — finite for
`c' < n/2` (`sumSqND_box_lt_top`); the `z`-independent constant the disjoint-sum domination pulls out. -/
noncomputable def Kbound (n : ℕ) (c' : ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in morseBox n T, ENNReal.ofReal ((∑ i, (p i)^2) ^ (-c'))

theorem Kbound_lt_top (m : ℕ) (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc' : c' < (m + 1) / 2) :
    Kbound (m+1) c' T < ⊤ :=
  sumSqND_box_lt_top m T hT c' hc'

/-- **L1.1 — the radial-Morse disjoint-sum domination (S2-FREE).** For a disjoint Morse block
`P : Fin (m+1) → ℝ` (`n = m+1 ≥ 1`) added to a nonnegative measurable core `W : (Fin k → ℝ) → ℝ`,
the product-box integral of `(∑ᵢ Pᵢ² + W z)^{−c'}` is bounded by the `z`-independent Morse constant
`Kbound` times the `z`-box volume, hence `< ⊤` for `c' < n/2`.

Pointwise `(∑ᵢ Pᵢ² + W z)^{−c'} ≤ (∑ᵢ Pᵢ²)^{−c'}` (`W ≥ 0`, `−c' ≤ 0`, `Real.rpow_le_rpow_of_nonpos`
on the larger base), so the inner `P`-integral is `≤ Kbound` for every fixed `z`; Tonelli
(`lintegral_lintegral`/`setLIntegral`) factors the product and pulls `Kbound` out.

The terminal EVERY hfin cover leaf consumes; built on `radial_ball_iff` (S2-free), no `monomial_rlct`. -/
theorem radial_morse_dominates_lt_top {m k : ℕ} (c' : ℝ) (hc' : c' < (m + 1) / 2) (hc0 : 0 ≤ c')
    (T : ℝ) (hT : 0 < T) (W : (Fin k → ℝ) → ℝ) (hWnn : ∀ z, 0 ≤ W z) (hWmeas : Measurable W) :
    ∫⁻ z in morseBox k T, ∫⁻ p in morseBox (m+1) T,
        ENNReal.ofReal ((∑ i, (p i)^2 + W z) ^ (-c')) ≤ Kbound (m+1) c' T * volume (morseBox k T) := by
  -- The Morse-block zero set `{p | ∑ pᵢ² = 0} = {0}` is Lebesgue-null (m+1 ≥ 1), so the pointwise
  -- domination need only hold a.e. (off that point); `lintegral_mono_ae` then bounds the inner
  -- integral by `Kbound` for every fixed `z`.
  have hzero_null : volume {p : Fin (m+1) → ℝ | ∑ i, (p i)^2 = 0} = 0 := by
    have hsubsingleton : {p : Fin (m+1) → ℝ | ∑ i, (p i)^2 = 0} ⊆ {(0 : Fin (m+1) → ℝ)} := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      have : ∀ i, (p i)^2 = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hp i (Finset.mem_univ i)
      simp only [Set.mem_singleton_iff]
      funext i; exact pow_eq_zero_iff (by norm_num) |>.1 (this i)
    exact measure_mono_null hsubsingleton (measure_singleton _)
  -- inner bound: for every fixed z, ∫⁻_p (∑ P² + W z)^{−c'} ≤ Kbound
  have hinner : ∀ z, ∫⁻ p in morseBox (m+1) T, ENNReal.ofReal ((∑ i, (p i)^2 + W z) ^ (-c'))
      ≤ Kbound (m+1) c' T := by
    intro z
    rw [Kbound]
    refine lintegral_mono_ae ?_
    -- a.e. (off the null Morse-block-zero point): the pointwise rpow domination
    have hae : ∀ᵐ p : Fin (m+1) → ℝ, ∑ i, (p i)^2 ≠ 0 := by
      rw [ae_iff]; simpa using hzero_null
    refine (ae_restrict_of_ae hae).mono (fun p hp => ?_)
    apply ENNReal.ofReal_le_ofReal
    have hpos : (0 : ℝ) < ∑ i, (p i)^2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hp)
    have hle : ∑ i, (p i)^2 ≤ ∑ i, (p i)^2 + W z := by linarith [hWnn z]
    exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  calc ∫⁻ z in morseBox k T, ∫⁻ p in morseBox (m+1) T,
          ENNReal.ofReal ((∑ i, (p i)^2 + W z) ^ (-c'))
      ≤ ∫⁻ _z in morseBox k T, Kbound (m+1) c' T := lintegral_mono (fun z => hinner z)
    _ = Kbound (m+1) c' T * volume (morseBox k T) := by
        rw [setLIntegral_const]

end DLNFibre.DLN.RLCT

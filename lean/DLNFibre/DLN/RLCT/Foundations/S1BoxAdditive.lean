import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1BoxAdditive` — additive-block box integrability (R1 lift, piece 2)

Piece 2 of the GE-leg squeeze+reindex lift (glue (a)): the smooth-block normal form
`Φ(x, z) = (∑ᵢ xᵢ²) + G(z)²` (the `n` Erow Morse squares + the child core `G²`) is integrable on a
product box `(Erow ball) ×ˢ (child box)` when `c' < n/2 + (child box threshold)` — splitting `c' = a + b`
with the `n`-D smooth block carrying `a < n/2` and the child carrying `b` (its box-integrability the
threaded input).

The `n`-dimensional generalisation of `S1Fubini.step_integrableOn` (`Fin 1` → `EuclideanSpace ℝ (Fin
n)`): the pointwise sum-power comparison `cmpF` `(s + t)^{−(a+b)} ≤ s^{−a}·t^{−b}` dominates `Φ^{−c'}`
by the product `‖x‖^{−2a}·|G²|^{−b}`, whose `x`-factor is integrable on a ball (`radial_ball_iff`) and
whose `z`-factor is the child box-integrability (the hypothesis the recursion threads). `Integrable.mul_prod`
+ `mono'` close it.

Used in the lift: `Φ = smoothBlockSplitForm G` is integrable over `(ball) ×ˢ (child box)`, reducing
`hKint(Φ)` (hence `hKint(core)` via the box squeeze) to `hKint(G²)` = the child box-integrability.

Axiom-free target (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open MeasureTheory Set Metric
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- **The `n`-D additive-block box integrability** (`n = m+1`). With the `n`-D smooth block
`‖x‖² = ∑ᵢ xᵢ²` on `EuclideanSpace ℝ (Fin n)` and a child core `G² ≥ 0` (measurable, `≠ 0` a.e. on the
child box `V`), if `a < n/2` (the smooth block below threshold, `−n < −2a`) and `|G²|^{−b}` is integrable
on `V`, then the joint density `|‖x‖² + G(z)²|^{−(a+b)}` is integrable on `(ball 0 ε) ×ˢ V`. The `n`-D
`step_integrableOn`: `cmpF` domination + `radial_ball_iff` (`x`-factor) + the child box-integrability
(`z`-factor) + `Integrable.mul_prod`. -/
theorem boxAdditive_integrableOn
    {W : Type*} [MeasureSpace W] [SigmaFinite (volume : Measure W)]
    (m : ℕ) (G : W → ℝ) (hG : ∀ z, 0 ≤ G z ^ 2) (hGmeas : Measurable G)
    (a b ε : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (halt : a < (m + 1) / 2) (hε : 0 < ε)
    (V : Set W)
    (hGne : ∀ᵐ z ∂(volume.restrict V), G z ^ 2 ≠ 0)
    (hz : IntegrableOn (fun z : W => |G z ^ 2| ^ (-b)) V volume) :
    IntegrableOn (fun p : EuclideanSpace ℝ (Fin (m + 1)) × W =>
        |(∑ i, p.1 i ^ 2) + G p.2 ^ 2| ^ (-(a + b)))
      ((ball 0 ε) ×ˢ V) volume := by
  -- the `x`-factor `‖x‖^{−2a}` is integrable on the ball (`radial_ball_iff`, `−(m+1) < −2a`)
  have hx : IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ‖x‖ ^ (-(2 * a)))
      (ball 0 ε) volume := by
    rw [radial_ball_iff m ε _ hε]; linarith
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  -- the dominating product is integrable on the product
  have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin (m + 1)) × W =>
      ‖p.1‖ ^ (-(2 * a)) * |G p.2 ^ 2| ^ (-b))
      ((volume.restrict (ball 0 ε)).prod (volume.restrict V)) :=
    Integrable.mul_prod hx hz
  refine hdom.mono' ((by fun_prop : Measurable _).aestronglyMeasurable) ?_
  -- `‖x‖ > 0` a.e. (off the null `{0}`) and `G² > 0` a.e. on `V` (`hGne`)
  have hxne0 : ∀ᵐ x ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) ε)), x ≠ 0 := by
    apply ae_restrict_of_ae; exact ae_iff.2 (by simp [measure_singleton])
  have hxne' := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) ε))
    (ν := volume.restrict V)).tendsto_ae.eventually hxne0
  have hGne' := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict (ball (0 : EuclideanSpace ℝ (Fin (m + 1))) ε))
    (ν := volume.restrict V)).tendsto_ae.eventually hGne
  filter_upwards [hxne', hGne'] with p hxp hgp
  -- `∑ᵢ xᵢ² = ‖x‖²`, `> 0` (x ≠ 0); `G² > 0` (hgp)
  have hnorm : (∑ i, p.1 i ^ 2) = ‖p.1‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    congr 1; ext i; rw [Real.norm_eq_abs, sq_abs]
  have hsx : 0 < ‖p.1‖ ^ 2 := by
    have : 0 < ‖p.1‖ := norm_pos_iff.mpr hxp
    positivity
  have htg : 0 < G p.2 ^ 2 := lt_of_le_of_ne (hG p.2) (Ne.symm hgp)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (by rw [hnorm]; positivity : (0 : ℝ) ≤ (∑ i, p.1 i ^ 2) + G p.2 ^ 2)]
  rw [hnorm]
  -- domination via `cmpF`
  have hcmp : (‖p.1‖ ^ 2 + G p.2 ^ 2) ^ (-(a + b)) ≤ ‖p.1‖ ^ (-(2 * a)) * |G p.2 ^ 2| ^ (-b) := by
    calc (‖p.1‖ ^ 2 + G p.2 ^ 2) ^ (-(a + b)) ≤ (‖p.1‖ ^ 2) ^ (-a) * (G p.2 ^ 2) ^ (-b) :=
          cmpF _ _ a b hsx htg ha hb
      _ = ‖p.1‖ ^ (-(2 * a)) * |G p.2 ^ 2| ^ (-b) := by
          rw [abs_of_nonneg (hG p.2), ← Real.rpow_natCast ‖p.1‖ 2,
            ← Real.rpow_mul (norm_nonneg _)]
          ring_nf
  exact hcmp

end DLNFibre.DLN.RLCT

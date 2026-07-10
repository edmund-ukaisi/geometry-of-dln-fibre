# genm-p2rev — fidelity review of Cat I brick P2 (`projection_rpow_lintegral_uniform`)

**Verdict: PASS.** (Persisted by the controller — p2rev could not write the artefact under its harness
constraint; findings verbatim from its report. Decorrelated Codex xhigh corroborated all points.)

**Under review:** `RouteMSJProjRadial.lean` @ `c2a68086` (branch `genm-catI-p2-proj`, now merged into
`genm-catI-integrability-work @ 5c368bd8`):
`projection_rpow_lintegral_uniform (q r : ℕ) (hr : 1 ≤ r) (hrq : r ≤ q) {a : ℝ} (ha : a < r) (R : ℝ) :
∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ U : Submodule ℝ (EuclideanSpace ℝ (Fin q)), r ≤ Module.finrank ℝ U →
(∫⁻ w in Metric.ball 0 R, ENNReal.ofReal (‖U.starProjection w‖ ^ (-a))) ≤ C`.

## Findings
1. **Threshold `a < r` correct + TIGHT.** `∫_{B_d(R)} ‖x‖^{−a}` converges iff `a < d`
   (`= |S^{d−1}|·R^{d−a}/(d−a)`); the integrability-worst subspace is `d = r`, so `a < r` is exactly what
   uniformity needs; `a = r` diverges for any `r`-dim `U`. Codex confirmed the closed form.
2. **Uniformity genuine; the proof does NOT make the flagged error.** `C` sums `radVal` over ALL
   `d ∈ [r,q]`, not just `d = r`. (A larger `d` can be numerically bigger; the finite-sum `C` dominates
   every `d` regardless — a point in the proof's favour, not a hole.)
3. **Route deviation sound.** `T = ofLp ∘ Φ` is measure-preserving via `LinearIsometryEquiv.measurePreserving`
   ∘ `WithLp.volume_preserving_ofLp` (two composed Mathlib lemmas, not asserted); `↥U` never carries a
   measure (the `Subtype` MeasurableSpace diamond genuinely sidestepped). Norm bridge
   `‖U.starProjection w‖ = ‖(T w).1‖` verified via `fst_orthogonalDecomposition_apply` (fst =
   orthogonalProjection U) + isometry. `starProjection` = orthogonal projection onto `U`; `|det| = 1`, no
   scaling.
4. **Non-vacuous.** `C < ⊤` real; `U = ⊤` (dim `q ≥ r`) instantiates the `∀`.
5. **Forced axioms clean-three** `[propext, Classical.choice, Quot.sound]` under a FORCED recompile
   (source-hash perturbed + oleans deleted at the correct `.lake/build/lib/lean/` path).

## Notes (not defects — for integration cleanup)
- `hrq : r ≤ q` is UNUSED (compiler-flagged): `finrank U ≤ q` comes from the ambient dimension, so the
  theorem holds without it. Mild over-hypothesis — the statement is in fact slightly more general; harmless
  for P4's use. Drop it at integration if trivial (name=content: it currently claims to need `r ≤ q`).
- Two unused `simp` args (`WithLp.toLp_fst/_snd`) — cosmetic lint only.

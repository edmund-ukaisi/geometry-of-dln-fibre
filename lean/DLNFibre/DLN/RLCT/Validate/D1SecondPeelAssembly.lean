import DLNFibre.DLN.RLCT.Validate.D1SecondPeelChart

/-!
# `DLNFibre.DLN.RLCT.Validate.D1SecondPeelAssembly` — the L = 2 D1 `≥`-leg, second peel DISCHARGED

Wires the SECOND-peel chart producer `secondPeel_hchart_residual` (`D1SecondPeelChart`, PROVEN) into
the two-peel D1 producer `deepest_le_of_optimal_of_iftResidual` (`D1IFTResidualProducer`), DISCHARGING
the `hchart₂` hypothesis from the second-peel selected-minor data. The result is a new L = 2 D1
per-point `≥`-leg lemma in which the SECOND peel is no longer a hypothesis — it is built from the
first-peel slice residual's own `C²` structure + an invertible `extra`-minor of its Jacobian.

## What stays a NAMED-OPEN gate (honest scope)

The lemma carries, as EXPLICIT hypotheses (none silently assumed):
  * the FIRST-peel chart transfer `hchart` (the DLN-specific bounded-unit IFT chart at `v` — the first
    peel `dln_hchart_residual` produces this; here it is threaded as the first-peel `C¹` residual `q` +
    `hchart`, exactly as `deepest_le_of_optimal_of_iftResidual` takes it);
  * `hDeepest` = #44 (`deepest_regular_core_normal_form_of`, the deepest-side equality — gated on the
    R1 core value `hcore` + `hGne`, ready in `DeepestL2Wiring`);
  * `hDegraded` = the §5 R1-resolution-at-`M'` interface value (gated on the R1 leg);
  * the SECOND-peel selected-minor data: the first-peel slice residual `q (0,·)` is `C²` with an
    invertible `extra × extra` Jacobian minor at its basepoint (the analytic non-degeneracy the
    verify-first gate identified — a JACOBIAN-rank condition on the residual VECTOR, NOT a Hessian
    condition; see `D1SecondPeelChart`).

The SECOND peel's chart (`hchart₂`) — the genuinely-open analytic piece this tide targeted — is now
PROVEN-from-data, not hypothesized. D1 still SEQUENCES on R1 (via `hDegraded`) and on #44 (via
`hDeepest`), and on the first-peel chart transfer; those are the tracked obligations, untouched.

Scope L = 2 only. The general-L Skeleton sorry `rlctAt_deepest_le_of_optimal` stays #120-walled.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The L = 2 D1 per-point `≥`-leg with the SECOND peel DISCHARGED.** At a middle-stratum optimal
`v` (square deepest reduced widths `(m,m,m)`, `coreDeepest = ofReal(lambdaCore (square m))`,
`a + b ≤ m`), with `Y = Fin Nslice → ℝ` the first-peel complement slice:

  * the FIRST-peel `C¹` residual `q` + chart transfer `hchart` give the `nReg`-block `hAtV` half;
  * the SECOND-peel chart `hchart₂` is BUILT (not hypothesized) by `secondPeel_hchart_residual` from
    the first-peel slice residual `q (0,·)` being `C²` (`hslice`), vanishing at the basepoint
    (`hslice0`), and having an invertible `extra`-minor at the basepoint (`hminor₂`);
  * `hDeepest` (#44) and `hDegraded` (the R1 interface at `M'`) close the comparison.

Concludes `rlctAt deepest ≤ rlctAt v`. The `extra` Morse squares peeled in the SECOND pass are
`extraCount m a b`; `nReg = nRegL2 H r`. The `Y₂` of the two-peel producer is instantiated to
`Fin (Nslice − extraCount m a b) → ℝ` by the producer's output. -/
theorem deepest_le_of_optimal_secondPeel_discharged {Nslice n : ℕ}
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (deepest v : Params H) (m a b : ℕ) (hab : a + b ≤ m) (coreDeepest : ℝ≥0∞)
    (hcoreDeepest : coreDeepest = ENNReal.ofReal (lambdaCore (squareWidths m) : ℝ))
    (hDeepest : rlctAt H (dlnLoss H B) deepest = (nRegL2 H r : ℝ≥0∞) / 2 + coreDeepest)
    -- FIRST-peel `C¹` residual + chart transfer
    (q : (Fin (nRegL2 H r) → ℝ) × (Fin Nslice → ℝ) → EuclideanSpace ℝ (Fin n))
    (hq : ContDiff ℝ 1 q) (t0 : Fin Nslice → ℝ)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin Nslice → ℝ) =>
            (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0))
    (hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
        (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
    -- SECOND-peel selected-minor data (the first-peel slice residual `q (0,·)` is `C²`, vanishes,
    -- and has an invertible `extra`-minor at its basepoint `t0`)
    (hslice : ContDiff ℝ 2 (fun t : Fin Nslice → ℝ => q ((0 : Fin (nRegL2 H r) → ℝ), t)))
    (hslice0 : (fun t : Fin Nslice → ℝ => q ((0 : Fin (nRegL2 H r) → ℝ), t)) t0 = 0)
    (eh : Fin (extraCount m a b) → Fin n) (ec : Fin (extraCount m a b) → Fin Nslice)
    (heh : Function.Injective eh) (hec : Function.Injective ec)
    (hminor₂ : (Matrix.of (fun k k' : Fin (extraCount m a b) =>
      (fderiv ℝ (fun t => q ((0 : Fin (nRegL2 H r) → ℝ), t) (eh k)) t0)
        (Pi.single (ec k') 1))).det ≠ 0)
    -- the §5 R1-resolution interface value + the second-peel slice non-vanishing, BOTH stated on the
    -- BUILT second-peel residual `q₂`/`t0₂` (the named-open R1 gates; `hR₂ne` is the degraded-core
    -- non-degeneracy, the same `hGne`-shape discipline as the first peel)
    (hInterface : ∀ (q₂ : (Fin (extraCount m a b) → ℝ) × (Fin (Nslice - extraCount m a b) → ℝ)
          → EuclideanSpace ℝ (Fin n)) (t0₂ : Fin (Nslice - extraCount m a b) → ℝ),
        (rlctAtOn (fun t : Fin Nslice → ℝ => ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
            = rlctAtOn (fun p : (Fin (extraCount m a b) → ℝ) × (Fin (Nslice - extraCount m a b) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2)) ((0 : Fin (extraCount m a b) → ℝ), t0₂)) →
        (∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U),
            (∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), z) i ^ 2) ≠ 0)
          ∧ rlctAtOn (fun t : Fin (Nslice - extraCount m a b) → ℝ =>
              ∑ i, q₂ ((0 : Fin (extraCount m a b) → ℝ), t) i ^ 2) t0₂
            = ENNReal.ofReal (lambdaCore (MprimeWidths m a b) : ℝ)) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  -- BUILD the second-peel chart `hchart₂` + the `C¹` residual `q₂` from the selected-minor data.
  obtain ⟨q₂, t0₂, hq₂CD, hchart₂⟩ :=
    secondPeel_hchart_residual (fun t => q ((0 : Fin (nRegL2 H r) → ℝ), t)) t0 hslice hslice0
      eh ec heh hec hminor₂
  -- the R1 interface, applied to the BUILT second-peel residual, supplies both `hR₂ne` and `hDegraded`.
  obtain ⟨hR₂ne, hDeg⟩ := hInterface q₂ t0₂ hchart₂
  exact deepest_le_of_optimal_of_iftResidual H r B deepest v m a b hab coreDeepest hcoreDeepest
    hDeepest q hq t0 hchart hRne q₂ hq₂CD t0₂ hchart₂ hR₂ne hDeg

end DLNFibre.DLN.RLCT

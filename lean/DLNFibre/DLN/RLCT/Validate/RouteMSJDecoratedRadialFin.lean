import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRadial

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRadialFin` — the radial-peel finiteness brick

**Thread `genm-decbuild`, tile T3.** The finiteness CONSEQUENCE of the banked radial-attach
factoring (`RouteMSJDecoratedRadial.radialAttach_integral`, `radialAttachFactor_lt_top`): attaching
a Case-2 radial preserves box-finiteness. This is the (b) RADIAL half of one decorated peel,
packaged as the reusable finiteness brick the eventual `decorated_peel_step` (regime A) consumes.

## What lands here (sorry-free)

* **`radialAttach_integral_lt_top`** — the brick: `(radialAttach D j₀).integral c' < ⊤` whenever
  (i) `c' < (j₀+1)/2` (the per-divisor Morse threshold, so the 1-D radial factor is finite) and
  (ii) the parent decoration integral `D.integral c'` is finite. Immediate from the banked factoring
  `radialAttach_integral` + `radialAttachFactor_lt_top` + `ENNReal.mul_lt_top`.

## What this is NOT (fidelity — the honest boundary)

The radial half ALONE covers `c'` only up to the per-divisor threshold `(j₀+1)/2 = ½·peelCharge`
(with `j₀ = peelCharge − 1`). For a chain with `minAdm M > peelCharge M u` — the generic case that
forces the `(S,J)` flag (`minAdm_le_peelCharge_add_redChain` is an inequality, not an equality) —
the surplus `½·peelCharge ≤ c' < ½·minAdm` is NOT covered by the radial: there the 1-D radial factor
DIVERGES and the finiteness must come from the reduced-chain descent (the block split, tile T4,
closed by the one-shorter IH at threshold shifted by `½·peelCharge` via `carrierThreshold_shift`).
So this brick is a regime-A ingredient; it does NOT discharge `DecoratedPeelStep` on its own.

S2-FREE: pure `ℝ≥0∞` finiteness over the banked radial factoring. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The radial-peel finiteness brick.** Attaching a Case-2 radial with accumulated Jacobian
exponent `j₀` preserves box-finiteness at exponent `c'`: `(radialAttach D j₀).integral c' < ⊤`
whenever `c'` is below the per-divisor Morse threshold `(j₀+1)/2` (so the 1-D radial factor is
finite) and the parent decoration integral is finite. The banked factoring `radialAttach_integral`
splits the integral into the 1-D factor times the parent; `radialAttachFactor_lt_top` gives the
former, `hD` the latter. -/
theorem radialAttach_integral_lt_top {M : Fin (L + 1) → ℕ} (D : SJDecoration M) (j₀ : ℕ) (c' : ℝ)
    (hthr : c' < ((j₀ : ℝ) + 1) / 2) (hD : D.integral c' < ⊤) :
    (D.radialAttach j₀).integral c' < ⊤ := by
  rw [D.radialAttach_integral j₀ c']
  exact ENNReal.mul_lt_top (radialAttachFactor_lt_top j₀ c' (by linarith)) hD

/-! ## Non-vacuity — a genuine `d = 1` radial peel on the `(3,3,4)` anchor -/

/-- **Non-vacuity.** For any decoration `D` on the `(3,3,4)` anchor and any `c' < 6`: if
`D.integral c'` is finite, attaching a Case-2 radial with Jacobian exponent `j₀ = 11` keeps it
finite (the per-divisor threshold `(11+1)/2 = 6` covers `c'`). A concrete `d ↦ d+1` inhabitant
exercising the brick end-to-end (no `minAdm` evaluation needed). -/
example (D : SJDecoration (![3, 3, 4] : Fin 3 → ℕ)) (c' : ℝ) (hc' : c' < 6)
    (hD : D.integral c' < ⊤) :
    (D.radialAttach 11).integral c' < ⊤ :=
  radialAttach_integral_lt_top D 11 c' (by norm_num; linarith) hD

end DLNFibre.DLN.RLCT

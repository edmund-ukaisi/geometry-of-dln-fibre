import DLNFibre.DLN.RLCT.Validate.HeadlineL1Mint
import DLNFibre.DLN.RLCT.Validate.HeadlineGenAssembly
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCapB

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineConditionalSpine` — the expedition's durable conditional close-out

The unconditional learning-coefficient headline needs the layer-product box integral to be finite
below the geometric threshold `½·minAdm` — the genuine open analytic content, named
`RouteMBoxThresholdFinite` ("the named analytic finiteness hypothesis", `RouteMBoxReduction.lean`).
This module banks the honestly-clean-three CONDITIONAL result: GIVEN that box-finiteness (for the
reduced widths `H − r`), the full `∀ L ≥ 1` Aoyagi headline `= ofReal (aoyagiLambda H r)` (`= C/2`)
holds, clean-three MODULO the hypothesis.

**Why condition on box-finiteness, not on `chartBridgeFaithful_buildTree`** (the correction, navigator-8
+ elder, pnp-full #3a): a first version conditioned on `chartBridgeFaithful_buildTree` — the claim that
the SPECIFIC α-atlas `geoAtlasNorm alphaGauge` satisfies `ChartBridgeFaithful`, including its
`LeafPullback` conjunct. That `LeafPullback` over the α-atlas is **category-FALSE**: no det-1 chart
makes the residual core bounded below (it → 0; diagonalization requires a det-0 projection). So
`chartBridgeFaithful_buildTree` is UNPROVABLE-as-stated, conditioning on it is VACUOUS (ex-falso), and
the "one `exact` from unconditional" seam is DEAD. The honest hypothesis is the ABSTRACT Prop the
engine genuinely owes — `RouteMBoxThresholdFinite (H − r)` — which is TRUE (the paper's "mildly
singular" result) and **route-agnostic**: dischargeable by ANY valid route (a future valid atlas over
a finer resolution / route-ii extra blow-ups, or the ideal-level Aoyagi Lemma 1 lower bound), NOT tied
to the refuted α-atlas chart-bridge.

`aoyagi_learning_coefficient_gen` already IS the `L ≥ 2` core "given box-finiteness, aoyagi = C/2"
(clean-three, `hbox` a hypothesis). This module folds in the unconditional `L = 1` endpoint
(`aoyagi_learning_coefficient_L1`) to state the FULL `∀ L ≥ 1` headline conditional on `hbox`.

Discharge to unconditional: supply any proof of `RouteMBoxThresholdFinite (fun s => H s − r)`.

**Non-vacuity — the hypothesis is PROVEN, not hoped.** `RouteMBoxThresholdFinite` is discharged
clean-three for the entire `L = 2` (three-layer) family by `routeMBoxThresholdFinite_mnp`
(`RouteMSchurRectCapB.lean`, the SchurCore recursion — discharge-agnostic, NO chart CoV). So `hbox`
is a genuinely satisfiable hypothesis, not a refuted clause; the corollary
`aoyagi_learning_coefficient_L2_unconditional` below feeds it into the spine to close the headline
UNCONDITIONALLY at `L = 2`. Only `L ≥ 3` box-finiteness is open (the ideal-level follow-up).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal

variable {L : ℕ}

/-- **The conditional Aoyagi headline — clean-three modulo box-finiteness.** GIVEN the genuine open
analytic obligation `hbox : RouteMBoxThresholdFinite (fun s => H s − r)` (the layer-product box
integral is finite below `½·minAdm` for the reduced widths), the global learning coefficient (the
infimum of the local RLCT over the fibre `mult⁻¹(B)`) of the `∀ L ≥ 1` deep-linear square-Frobenius
loss equals Aoyagi's closed form `aoyagiLambda H r` (`= C/2`), for every nondegenerate rank-`r` target
(`r < H s` at every layer). The `L = 1` arm is the unconditional regular Morse endpoint
`aoyagi_learning_coefficient_L1` (does not use `hbox`); the `L ≥ 2` arm is
`aoyagi_learning_coefficient_gen` fed `hbox` directly. Clean-three modulo `hbox` (see the module
docstring and the `#guard_msgs` gate below).

`hbox` is the honest, ROUTE-AGNOSTIC obligation — dischargeable by any valid resolution or the
ideal-level Aoyagi Lemma 1 bound. It is NOT the refuted α-atlas `chartBridgeFaithful_buildTree` (whose
`LeafPullback` is category-false, pnp-full #3a); this theorem supersedes that vacuous framing. -/
theorem aoyagi_learning_coefficient_of_boxThresholdFinite
    (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hbox : RouteMBoxThresholdFinite (fun s => H s - r)) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  rcases lt_or_ge L 2 with hlt | hge
  · -- `1 ≤ L < 2` ⟹ `L = 1`: the unconditional regular Morse endpoint (`hbox` unused).
    obtain rfl : L = 1 := by omega
    exact aoyagi_learning_coefficient_L1 H r B hB hr hpos
  · -- `L ≥ 2`: the general assembly fed the box-finiteness hypothesis directly (no α-atlas, no
    -- `resolutionOf`, no chart bridge — `hbox` is the abstract owed Prop).
    exact aoyagi_learning_coefficient_gen H r B hB hr hL hge hpos hbox

-- Self-contained axiom gate (build FAILS if the footprint drifts): the conditional spine is
-- clean-three MODULO `hbox`. A `sorryAx` here would mean the proof re-opened a hole.
/-- info: 'DLNFibre.DLN.RLCT.aoyagi_learning_coefficient_of_boxThresholdFinite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms aoyagi_learning_coefficient_of_boxThresholdFinite

/-- **Unconditional at `L = 2`** (the three-layer `(m, n, p)` family) — the concrete non-vacuity base
case with real unconditional teeth. Discharging `hbox` via the PROVEN clean-three
`routeMBoxThresholdFinite_mnp` (box-finiteness for every three-layer width vector, SchurCore
recursion — NO chart CoV), the spine's headline becomes UNCONDITIONAL: the three-layer Aoyagi learning
coefficient equals `ofReal (aoyagiLambda H r)`, clean-three, no hypothesis. The deliverable closes
OUTRIGHT at `L ≤ 2`; only `L ≥ 3` stays conditional on box-finiteness (the ideal-level follow-up's
target). This is the answer to "is the conditional vacuous?" — no: it has a proven unconditional base
case. -/
theorem aoyagi_learning_coefficient_L2_unconditional (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hpos : ∀ s : Fin 3, r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  have hbox : RouteMBoxThresholdFinite (fun s => H s - r) := by
    have hconv : (fun s => H s - r) = (![H 0 - r, H 1 - r, H 2 - r] : Fin 3 → ℕ) := by
      funext s; fin_cases s <;> rfl
    rw [hconv]; exact routeMBoxThresholdFinite_mnp _ _ _
  exact aoyagi_learning_coefficient_of_boxThresholdFinite H r B hB hr (by norm_num) hpos hbox

-- Self-contained gate on the unconditional L=2 corollary: MUST be clean-three (no `hbox`, no `sorryAx`).
/-- info: 'DLNFibre.DLN.RLCT.aoyagi_learning_coefficient_L2_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms aoyagi_learning_coefficient_L2_unconditional

end DLNFibre.DLN.RLCT

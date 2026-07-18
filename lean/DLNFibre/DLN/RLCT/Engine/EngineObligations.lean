import DLNFibre.DLN.RLCT.Engine.EngineDefs
import DLNFibre.DLN.RLCT.Engine.RegionGlueAssembly

/-!
# `DLNFibre.DLN.RLCT.Engine.EngineObligations` — the engine's obligations (the sorried theorems)

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.** The transform-only Aoyagi engine's obligation THEOREMS, split from the carrier-facing
`def`s (`EngineDefs`). The two holes are `monomialization_terminates` + `region_glue`; the rest are
projections of `resolutionOf_spec`. This file MAY import glue modules (they consume `EngineDefs`, not
this file), keeping the sorried holes off the region-glue lane's import path.

**Layer-B fence: only `region_glue` integrates.**
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped ENNReal

variable {L : ℕ}

/-! ## The construction hole + the canonical resolution -/

/-- **Monomialisation terminates into a canonical resolution** (map: `monomialization-termination`;
the ONE construction hole). Layer B; structural. The coverage/step/exponent/CoV CONTENT lives
here. -/
@[blueprint] theorem monomialization_terminates (M : Fin (L + 1) → ℕ) :
    ∃ t : ResolutionTree M, CanonicalResolution M t := by
  sorry

/-- **The canonical resolution** of `M`. A blueprint forecast (rests on the sorried
construction). -/
@[blueprint] noncomputable def resolutionOf (M : Fin (L + 1) → ℕ) : ResolutionTree M :=
  (monomialization_terminates M).choose

/-- The canonical resolution satisfies the full bundle. -/
@[blueprint] theorem resolutionOf_spec (M : Fin (L + 1) → ℕ) :
    CanonicalResolution M (resolutionOf M) :=
  (monomialization_terminates M).choose_spec

/-- The canonical resolution is a full monomialisation — the precondition of `region_glue`. -/
@[blueprint] theorem resolutionOf_isFullMonomialization (M : Fin (L + 1) → ℕ) :
    IsFullMonomialization (resolutionOf M) :=
  (resolutionOf_spec M).1

/-! ## The obligations (projections of the bundle) + the analytic hole -/

/-- **Case-step invariant** (map: `case-step-lemmas`). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem case_step_invariant (M : Fin (L + 1) → ℕ) :
    ∀ p ∈ ResolutionTree.stepEdges (resolutionOf M), StepRel p.1 p.2 :=
  (resolutionOf_spec M).2.1

/-- **Reduction layer** (map: `reduction-layer`). The regular peel: the resolution begins at the
base `S = J = 0`. STRUCTURAL (Layer-B fence). A projection of `resolutionOf_spec`. -/
@[blueprint] theorem reduction_layer (M : Fin (L + 1) → ℕ) :
    ∃ (n : StepData M) (edges : List (Edge M)),
      resolutionOf M = ResolutionTree.branch n edges ∧ n.layer = 0 ∧ n.cleared = 0 :=
  (resolutionOf_spec M).2.2.1

/-- **Coverage — THE HARD PART** (map: `coverage-theorem`, owned by coverage-design). The atlas
covers an UPSTAIRS-open box-neighbourhood via chart images, per-leaf injective/disjoint coords,
a.e.-injective charts, pullback, Jacobian, and the derived coherence. WITHOUT `rlct = c*`. A
projection. -/
@[blueprint] theorem coverage_theorem (M : Fin (L + 1) → ℕ) :
    ChartBridge M (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.1

/-- **Exponent-ledger bridge** (map: `exponent-ledger-bridge`). `minAdm M` is a terminal exponent
(now including `resRank`) and lower-bounds them all — so `minAdm ≤ resRank` too (ruling 2a).
Consumes `minAdm`/`Mval` verbatim. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem exponent_ledger_bridge (M : Fin (L + 1) → ℕ) :
    (∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), minAdm M ≤ e) ∧
      minAdm M ∈ ResolutionTree.terminalExponents (resolutionOf M) :=
  (resolutionOf_spec M).2.2.2.2.1

/-- **Live attainment** (finding 3): `minAdm M` is attained by a divisor exponent of a leaf with a
NONEMPTY source box — no empty-`srcBox` phantom. A projection of `resolutionOf_spec`. -/
@[blueprint] theorem exponent_ledger_liveAttainment (M : Fin (L + 1) → ℕ) :
    ∃ l ∈ ResolutionTree.leaves (resolutionOf M), l.srcBox.Nonempty ∧
      minAdm M ∈ (List.finRange l.numDiv).map l.divExp :=
  (resolutionOf_spec M).2.2.2.2.2

/-- **Region glue** (map: `region-glue`; the ONE analytic hole). ASSEMBLY ONLY: given the CoV
bridge, the box integral is finite whenever `c'` is below half every terminal exponent (divisor
exponents AND the folded `resRank` — so the Morse-core threshold is covered) — the banked
monomial/radial reads + the Mathlib area formula on the `ψ ∘ β` chart (consuming the upper det
bound; elder-ratified fork-8 revision) + the scaling-bridge globalization, glued over the
upstairs-open finite subcover. Precondition `IsFullMonomialization`. -/
@[blueprint] theorem region_glue (M : Fin (L + 1) → ℕ)
    (hbridge : ChartBridge M (resolutionOf M)) (c' : ℝ)
    (hrat : ∀ e ∈ ResolutionTree.terminalExponents (resolutionOf M), c' < (e : ℝ) / 2) :
    routeMLayerBoxIntegral M c' 1 < ⊤ :=
  region_glue_of_chartBridge (resolutionOf M) hbridge c' hrat

end DLNFibre.DLN.RLCT.Engine

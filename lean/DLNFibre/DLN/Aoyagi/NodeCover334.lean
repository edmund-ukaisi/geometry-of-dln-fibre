import DLNFibre.DLN.Aoyagi.CoverFold
import DLNFibre.DLN.Aoyagi.Corank2FanCover334

/-!
# R3 first brick — the (3,3,4) born-fan over the KEPT center {0,1,2,3,20} covers (4..7 spectators)

**RECONTEXTUALIZED (2026-07-26, elder-ruled #183).** This is the COVER-ONLY de-risk brick, NOT buildTree's
actual node cover. buildTree's node uses the FULL center (`dCenterOfNode` = the full residual block, size 9 at
the outer (3,3,4) node) via the RLCT Engine's `flatCube`/`pivotChart` (`flatCube_subset_leafPathImages`) — that
is the value/cover substrate (elder-ruled W3-clean, clean-three). This kept-subset born-fan (card 5) covers a
SMALLER center and CANNOT carry the value-Jacobian (kept card 5 → |u|^4 ≠ the correct |u|^8); guardrail-0 blocks
its born value-Jacobian at the shear node. So this brick is banked as cover-side de-risk only — named
`keptSubsetBornFan_cover_334` for exactly that.

The elder-gated R3 node/leaf layering: the NODE cover is the input-pivot FULL cover (no hole, no
`hnull`); the output-generator sandwich (`SurvivorFanCover`) is the LEAF/value side. This is the
NODE hook at the REAL (3,3,4) geometry, W3-clean (born from `StepConstructor.bornSiblings`, NOT the
`gWrapFan` K-orbit skeleton).

## The center — kept pivots of the real outer node
The reroute's real (3,3,4) fan is the 3-node chain (`Corank2GWrapDecomp`): outer `sigmaPiv`
(`blockBlowupMap {0..7,20} 20`, clearing `shearH∘permP`), `bbA0` (`{0..7}` pivot 0), `bbA1`
(`{1,5,6,7}` pivot 1). The clearing `shearH` keeps `shearKeepH = {i | i < 4 ∨ 12 ≤ i}` — i.e. it
CLEARS the residual block `{4..11}`. The born-fan bundles guardrail-0 (`PivotStep` requires each
pivot KEPT), so its center must be a KEPT set. We take `{0,1,2,3,20}` — the kept pivots of the outer
`sigmaPiv` center `{0..7,20}` (the cleared coords `4..7` are handled as SPECTATORS by the
block-blow-up argmax atom, which covers `closedBall 0 R` for ANY nonempty center, passing non-center
coords through). This is the born route's faithful handling of the shear node.

## The clause
`keptSubsetBornFan_cover_334`: `closedBall 0 R ⊆ ⋃ p, (bornSiblings {0,1,2,3,20} clearing334 · p).stepMap '' box`
— the born-siblings' step-maps (`blockBlowupMap ∘ shearH`) FULLY cover the node ball, with the box
inflated by the real shear factor `f = r ↦ r + 2r²` (`shearH_covers`, the two-product slots force
`C = 2`). NO hole, NO `hnull` — a full cover, per the elder's node layer. Via the banked general
`CoverFold.bornSiblings_union_covers_closed` (the node hook) instantiated at the REAL clearing
`clearing334` (its shear IS `shearH`, `clearing334_shear_eq_shearH`) +
`Corank2FanCover334.shearH_covers`.

## Scope (honest)
- IN: the one-node full-cover clause at the real (3,3,4) outer node (born-fan, real shear).
- FIDELITY NOTE: the fan center is the KEPT subset `{0,1,2,3,20}` of the geometric center
  `{0..7,20}`; the cleared coords `4..7` are spectators (block-blow-up atom handles them). Faithful
  for the COVER, with TWO calibration caveats: (i) this cover is CENTER-AGNOSTIC — the argmax atom
  covers `closedBall 0 R` for ANY nonempty center, so this theorem's green build certifies NOTHING
  about whether `{0,1,2,3,20}` is the geometrically-correct center; (ii) the center choice fixes the
  whole ATLAS IDENTITY / value pullback (which coords are blown up vs spectators), NOT merely a
  Jacobian exponent. Center/node-structure fidelity (does `buildTree`'s `conOracle` produce this
  center?) is settled INDEPENDENTLY on the value/atlas-identity side — the `#183` cover-center
  identity gate, NOT this green cover.
- OUT: the leaf/value side (sandwich, monomialisation, `{X=0}` recursion — the LEAF hook,
  `SurvivorFanCover`); the 3-node fold over the chain (next brick, via `ImageTreeCover`/`FanTree`).

## Main results
- `kept334` — the center `{0,1,2,3,20}` is kept by the real clearing.
- `keptSubsetBornFan_cover_334` — the born-fan full-cover clause at the real (3,3,4) node.
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.StepConstructor

namespace DLNFibre.DLN.Aoyagi.NodeCover334

/-- The kept center `{0,1,2,3,20}` (the kept pivots of the outer `sigmaPiv` center) is kept by the
real clearing `clearing334` (`shearKeepH = {i < 4 ∨ 12 ≤ i}`: `0,1,2,3 < 4`, `20 ≥ 12`). -/
theorem kept334 : ∀ p ∈ ({0, 1, 2, 3, 20} : Finset (Fin 21)), clearing334.keep p := by
  intro q hq
  fin_cases hq <;> first | exact Or.inl (by decide) | exact Or.inr (by decide)

/-- **The (3,3,4) born-fan over the KEPT center `{0,1,2,3,20}` fully covers (`4..7` spectators).**
The born-siblings over `{0,1,2,3,20}` — the KEPT pivots of the real outer center `{0..7,20}`; the
cleared coords `4..7` are NOT born-pivots but SPECTATORS (the block-blow-up atom covers via the
argmax over `{0,1,2,3,20}`, passing `4..7` through) — with step-map `blockBlowupMap ∘ shearH` FULLY
cover `closedBall 0 R`, from the shear-inflated box `closedBall 0 (max R 1 + 2·(max R 1)²)`. This is
NOT a claim about a fan over all of `{0..7,20}`. No hole, no `hnull` — the elder's input-pivot node
layer, at the REAL clearing `shearH`, W3-clean (born from `bornSiblings`, NOT the K-orbit). -/
theorem keptSubsetBornFan_cover_334 {R : ℝ} (hR : 0 ≤ R) :
    closedBall (0 : Fin 21 → ℝ) R ⊆
      ⋃ p : {p // p ∈ ({0, 1, 2, 3, 20} : Finset (Fin 21))},
        (bornSiblings ({0, 1, 2, 3, 20} : Finset (Fin 21)) clearing334 kept334 p.1 p.2).stepMap ''
          closedBall 0 (max R 1 + 2 * (max R 1) ^ 2) := by
  refine CoverFold.bornSiblings_union_covers_closed ({0, 1, 2, 3, 20} : Finset (Fin 21))
    ⟨0, by decide⟩ clearing334 kept334
    (fun _ _ => closedBall 0 (max R 1 + 2 * (max R 1) ^ 2)) hR ?_
  intro p hp
  rw [clearing334_shear_eq_shearH]
  exact Corank2FanCover334.shearH_covers

#assert_banked_clean_batch [keptSubsetBornFan_cover_334]

end DLNFibre.DLN.Aoyagi.NodeCover334

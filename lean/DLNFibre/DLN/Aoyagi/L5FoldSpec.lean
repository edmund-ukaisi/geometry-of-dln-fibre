import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.Case2Wire
import DLNFibre.DLN.Aoyagi.PivotPreservation
import DLNFibre.Core.Aoyagi.PathAtoms

/-!
# `DLN.Aoyagi.L5FoldSpec` — SPECIFY for L5 (`leaf_stepInv_of_path`), the fold-induction HINGE

SPECIFY-ONLY (seat-L3T2, 2026-07-22). This is the obligation MAP for the L5 fold + the MISSING-ATOMS
list (proposed statements, sorried contracts — NOT proofs). The PROVE waves are commissioned off this
map. Not wired into the aggregator. Territory: tip 503b31f6c.

## The target (`leaf_stepInv_of_path`, MonumentAtlas)

    ∃ atlas : GeoAtlasData d e, FoldProduced d e atlas ∧ FoldRealizes d e atlas ∧
      ∀ c, ∃ q r, PrincipalInv (coreGen d e) (atlas.gmap c) (monoOf (atlas.bexp c)) q r (atlas.region c)

L5 CONSTRUCTS the atlas by enumerating the root→leaf branches of `buildTree d (conOracle d) conRoot`,
then discharges three things: (FP) `FoldProduced`, (FR) `FoldRealizes` (3 clauses incl. the Jacobian
collapse), (PI) per-chart terminal `PrincipalInv`.

## A. The fold induction (the spine)

Recurse over `buildTree` (`WellFounded.fix (conRel_wf d)`), or equivalently over the `TreePath`
of each branch. Carry the invariant DOWN each branch:
  * interior (`ed.nextState.layer + 1 < N`): `FoldStepInvAt d e (supportAt(node)) node`;
  * at `S = L` (`ed.nextState.layer + 1 = N`): `foldStepInvAt_to_lastLayerInv` SUBSUMES into
    `LastLayerInv`, then the clears carry it slot-by-slot;
  * terminal (`N ≤ ed.nextState.layer`): cross to the leaf, `terminal_bezout` upgrades to `PrincipalInv`.
Base: at `conRoot`, `foldG = id`, `foldB = 1`, `foldResid = coreGen`; `FoldStepInvAt` holds from
`he0`/`he_lin` (the root-anchored linearity — the ONLY use of `he0`/`he_lin`, all the leaves are
`he0`/`he_lin`-free).

## B. Per-edge-kind obligation map

L5 must, at each edge, (i) EMIT `(node.extend ed).IsRealBranch e` (by CONSTRUCTING `ed` with the
canonical center/pivot/shear), and (ii) CONSUME it through the matching leaf. IsRealBranch's `.step`
arm is three conjuncts: `[rec] ∧ [∃sc: ecase/child/center=canonCenterOf/pivot-pin] ∧ [ShearWithinCarveRaw]`.

| edge kind | EMIT ∃sc conjunct (center/pivot pin)                    | EMIT ShearWithinCarveRaw          | CONSUME (leaf)                    |
|-----------|---------------------------------------------------------|-----------------------------------|-----------------------------------|
| case11    | center := canonCenterOf(case11) = {birth-corner pivot}∪row-block; pivot := divBirthCoord[mergeIdx] corner | edgeShear = id (localSub=id) — clauses I/II/III trivial | case1_preserves_stepInv [seat-L4 WALL] |
| case12    | center := canonCenterOf(case12) = widthMinUpto block; pivot := (layer,cleared) corner | blockShear canonShearOf — clauses I/II/III from canonShearOf within-carve | case1_preserves_stepInv [seat-L4 WALL] |
| case2     | center := canonCenterOf(case2) = widthMinUpto block; pivot := (layer,cleared) corner | blockShear canonShearOf — clauses I/II/III | case2_preserves_stepInv [conjA DONE (Case2Wire); conjB seat-L4 WALL] |
| rollover  | center := ∅; canonPivotOf = none ⟹ pivot-pin VACUOUS   | edgeShear = id — clauses trivial  | (layer advance; no divisibility) |
| terminal  | (the last edge; reaches `N ≤ child.layer`)              | vacuous (`sl` exhausts)           | terminal_edge_stepInv [DONE] → terminal_bezout → PrincipalInv |

The `∃sc` conjunct is discharged BY CONSTRUCTION: L5 recurses into `sc ∈ (conOracle d node.conState)
.stepChildren`, sets `ecase := sc.ecase`, `nextState := sc.child`, `center := canonCenterOf d
node.conState sc`, `pivot := (canonPivotOf …).getD default`. So `sc.ecase = ecase` / `sc.child =
nextState` / `center = canonCenterOf` are all `rfl`-class; the pivot-pin
`∀ piv, canonPivotOf … = some piv → piv = pivot` holds by the `getD` choice (rollover: `none`, vacuous).
The transition/`edgeδ` laws come from the oracle (`realBranch_terminal_edgeδ` for the terminal rollover).

## C. FoldProduced discharge (definitional bookkeeping — cheap once the atlas is built)

`leafOf c` = the leaf branch `c` reaches. `hmem`/`hsurj` from the buildTree leaf-enumeration (M6).
`hjac_mem`/`hjac_onto` from the ledger read-off (`jexp` ↔ `divExp`, the `AtlasRealizesExponents` seam;
LeafGeometryWire's L8 already proves the downstream). `hdom_ball` from the constructed `dom`.
`hstep_block` = each GeoStep has `jexp a = if a = pivot then center.card-1 else 0` (M-construction).
`hjac_tie` = `jac := ∑ steps jexp` (definitional). `hcard_tie` = `bindingAxes.card = numDiv` (M6-adjacent).

## D. FoldRealizes discharge (3 clauses)

1. `gmap c = foldG d e (pathOf c)` — M5 (`gmap_eq_foldG`): the atlas's `pathMap (steps.map σ)` IS the
   branch's accumulated `foldG` (the GeoStep σ's ARE the branch's `stepMap`s).
2. `(pathOf c).reachesLeaf e (leafOf c)` = `IsRealBranch (from B) ∧ decisionEmitsLeaf`; leafOf surjective (M6).
3. **JACOBIAN COLLAPSE** `|jacDet (gmap c) u| = jacWeight (jac c) u` — the (★)-telescoping (elder ruling
   2026-07-22, journal ~16:20): chain rule (PathAtoms `abs_jacDet_pathMap_cons`, banked) ⟹ product of
   per-step `|jacDet σᵢ (partialᵢ u)|`; `GeoStep.hσ_jac` (banked field) ⟹ `∏ jacWeight(jexpᵢ)(partialᵢ u)`;
   the (★) pivot-preservation (M4) ⟹ `∏ jacWeight(jexpᵢ)(u)`; `jacWeight_add` (M1) ⟹
   `jacWeight(∑ jexpᵢ)(u)`; `hjac_tie` ⟹ `jacWeight(jac c)(u)`.

## E. Missing atoms (proposed statements below; the PROVE-wave targets)

M1 `jacWeight_add` — detail-at-scale (Finset.prod_mul_distrib + pow_add). Core/MonomialRLCT-grade.
M2 `abs_jacDet_pathMap_prod` — telescope `abs_jacDet_pathMap_cons` over the list; detail-at-scale. PathAtoms-grade.
M3 `blockBlowupMap_apply_pivot` / spectator — pivot fixed, spectator fixed; partly banked
   (`blockBlowupMap_spectator_eq`). Core/BlockBlowup-grade.
M4 **(★) pivot-preservation — THE DEEP ATOM.** A deeper step's σ fixes an earlier step's pivot corner.
   Driver: `ShearWithinCarveRaw` clause (III) [shear vanishes on every ledger birth-corner] + `divBirthCoord`
   immutability [an earlier divisor's birth corner stays in every deeper node's ledger] + `blockBlowupMap`
   fixes coords off `center∖{pivot}` [deeper `canonCenterOf` is disjoint from earlier birth-corners].
   Decomposes into M4a (shear-side, from clause III) + M4b (blowup-side, canonCenter disjointness).
M5 `gmap_eq_foldG` — the atlas gmap is the branch's foldG. Definitional-adjacent (the steps ARE the stepMaps).
M6 buildTree leaf-enumeration: the atlas has one chart per leaf; `leafOf` surjective; branch↔leaf. Engine
   machinery (`buildTree_leaf*` may partly bank it).
M7 `canonShearOf` construction + within-carve emission: DEFINE the per-step Q/Schur shear and PROVE it
   satisfies `ShearWithinCarveRaw` (I/II/III) — elder: emittable, "Schur fold writes no pivot corner"
   (clause III is write-side/corners-only). Substantial; L5-internal or a companion module.

## F. Dependencies / not-suspect flags

The Jacobian collapse is FORCED by IsRealBranch (elder bake d309bca48) — no suspect there. The (PI)
per-chart clause depends on `case1_preserves_stepInv` (seat-L4 wall) and `case2_preserves_stepInv`
conjunct-B (seat-L4 companion) — OPEN walls, not suspects. No STOP-ON-SUSPECT: every clause is a
provable equation/obligation given the banked leaves + M1–M7; the labour is M4 (the (★) core) and M7
(canonShearOf), both detail-at-scale on the construction side.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi.L5Spec

variable {N : ℕ}

/-- **M1 (proposed)** — `jacWeight` turns exponent-addition into a product. Detail-at-scale
(`Finset.prod_mul_distrib` + `pow_add`). Feeds the (★) sum-collapse. -/
theorem jacWeight_add {D : ℕ} (h₁ h₂ : Fin D → ℕ) (u : Fin D → ℝ) :
    jacWeight (h₁ + h₂) u = jacWeight h₁ u * jacWeight h₂ u :=
  -- map: M1 — LANDED in Core.Aoyagi.MonomialRLCT (jacWeight_add); this contract delegates.
  DLNFibre.Core.Aoyagi.jacWeight_add h₁ h₂ u

/-- **M1′ (proposed)** — the list-sum form the branch telescoping lands on. -/
theorem jacWeight_listSum {D : ℕ} (l : List (Fin D → ℕ)) (u : Fin D → ℝ) :
    jacWeight (l.foldr (· + ·) 0) u = (l.map (fun h => jacWeight h u)).prod :=
  -- map: M1′ — LANDED in Core.Aoyagi.MonomialRLCT (jacWeight_listSum); this contract delegates.
  DLNFibre.Core.Aoyagi.jacWeight_listSum l u

/-- **M3 (proposed)** — the block blow-up fixes the pivot coordinate (`blockBlowupMap S p w p = w p`),
directly from the def's first branch. The spectator case is banked (`blockBlowupMap_spectator_eq`). -/
theorem blockBlowupMap_apply_pivot {D : ℕ} (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ) :
    blockBlowupMap S p w p = w p :=
  -- map: M3 — LANDED in Core.Aoyagi.BlockBlowup (blockBlowupMap_apply_pivot); this contract delegates.
  DLNFibre.Core.Aoyagi.blockBlowupMap_apply_pivot S p w

/-- **M4 (proposed) — THE (★) pivot-preservation core (deep).** Along a real branch, the block
blow-up of a DEEPER step fixes an EARLIER step's pivot corner `c₀`, PROVIDED `c₀` is not a non-pivot
center coordinate of the deeper step (`c₀ ∉ deeperCenter ∖ {deeperPivot}`) — the `canonCenterOf`
disjointness (M4b). The shear-side (M4a) is `ShearWithinCarveRaw` clause (III). Stated here for the
blow-up half against the raw def; the branch-level (★) glues M4a+M4b along `pathMap` of the suffix. -/
theorem blockBlowupMap_fixes_offCenter {D : ℕ} (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ)
    (c₀ : Fin D) (h : c₀ ∉ S) : blockBlowupMap S p w c₀ = w c₀ :=
  -- map: M3 spectator — LANDED in Core.Aoyagi.BlockBlowup (blockBlowupMap_offCenter_eq); delegates.
  -- (The DEEP M4b is `c₀ ∉ deeperCenter` — the canonCenter disjointness — which is seat-L6's, not this.)
  DLNFibre.Core.Aoyagi.blockBlowupMap_offCenter_eq S p w h

/-- **M2 (proposed)** — the composed `|jacDet|` telescopes over the σ-list into the product of the
per-step `|jacDet|` at the running partial points (iterate the banked `abs_jacDet_pathMap_cons`). The
per-step differentiability side-condition is `differentiable_pathMap` (banked). -/
theorem abs_jacDet_pathMap_prod {D : ℕ} (l : List ((Fin D → ℝ) → (Fin D → ℝ)))
    (hdiff : ∀ σ ∈ l, Differentiable ℝ σ) (u : Fin D → ℝ) :
    |jacDet (pathMap l) u|
      = (List.ofFn (fun i : Fin l.length =>
          |jacDet (l.get i) (pathMap (l.drop (i.1 + 1)) u)|)).prod :=
  -- map: M2 — LANDED in Core.Aoyagi.PathAtoms (abs_jacDet_pathMap_prod, off jacDet_pathMap_eq_prod);
  -- this contract delegates.
  DLNFibre.Core.Aoyagi.abs_jacDet_pathMap_prod l hdiff u

open DLNFibre.DLN.Aoyagi.PivotPres in
/-- **(B) adapter core — jacWeight congruence on its support** (the M4-slot plug-in helper). `jacWeight
jexp` reads only the coords where `jexp ≠ 0`; if `w'` agrees with `w` there, the weights agree. -/
theorem jacWeight_congr_of_fixed {D : ℕ} (jexp : Fin D → ℕ) (w w' : Fin D → ℝ)
    (h : ∀ a, jexp a ≠ 0 → w' a = w a) : jacWeight jexp w' = jacWeight jexp w := by
  simp only [jacWeight]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rcases Nat.eq_zero_or_pos (jexp a) with h0 | hpos
  · rw [h0, pow_zero, pow_zero]
  · rw [h a hpos.ne']

open DLNFibre.DLN.Aoyagi.PivotPres in
/-- **(B) adapter — the M4-slot jacWeight congruence, per NON-ROLLOVER step** (A5-locked). For a real
branch, the suffix `pathMap` after step `i` fixes step `i`'s pivot corner
(`foldSuffix_fixes_ledgerCorner`), and `jexp` is supported on that pivot (`hstep_block`), so the step's
jacWeight factor is suffix-invariant — exactly the M4-slot form §D.3's telescoping consumes. Rollover
steps (`jexp = 0`) use `jacWeight_congr_of_fixed` directly (vacuous support). Consumes `IsLedgerCorner`
(L5 supplies it via `canonPivotOf_isLedgerCorner_conOracle`); NO `canonPivotOf` at this site. -/
theorem jacWeight_suffix_invariant {N : ℕ} {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (P : TreePath d) (hb : P.IsRealBranch e)
    (i : ℕ) (hi : i < (childStateList d P).length)
    (jexp : Fin (flatDim d) → ℕ) (piv : Fin (flatDim d))
    (hsupp : ∀ a, jexp a ≠ 0 → a = piv)
    (hledger : IsLedgerCorner d ((childStateList d P)[i]) piv)
    (u : Fin (flatDim d) → ℝ) :
    jacWeight jexp (pathMap ((TreePath.stepMapList d P).drop (i + 1)) u) = jacWeight jexp u := by
  refine jacWeight_congr_of_fixed jexp u _ (fun a ha => ?_)
  have haeq : a = piv := hsupp a ha
  subst haeq
  exact foldSuffix_fixes_ledgerCorner e P hb i hi a hledger u

end DLNFibre.DLN.Aoyagi.L5Spec

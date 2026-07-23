import DLNFibre.DLN.Aoyagi.SourceClearedResid
-- SIGNATURE-VALIDATION NOTE (seat-CAPF): the proof phase also needs
-- `DLNFibre.DLN.Aoyagi.MultiAffineHomogWire` (foldResid_layerHomogeneous' + homogeneousDeg1On_comp_of_fixing),
-- but its closure pulls in Case1Wire, which is PRE-EXISTING-BROKEN on the CAPR base
-- (Case1Wire.lean:401 type mismatch: realBranch_boostReady_case11' now yields the sourceClearedResid form,
-- consumer still expects foldResid — the boost-ready→sourceClearedResid consumer re-point, GM/integration).
-- Statements below reference ONLY SourceClearedResid's closure (MonumentAtlas), so signatures validate here.

/-!
# `DLN.Aoyagi.CapDescent` — the cap-frontier render (SEAT-CAPF)

Closes the support-descent frontier at the FRESH-after-rollover WIDE interior node: the primed twin
`realBranch_appendResidDescent_fresh_sourceCleared'` of `SourceClearedResid.lean`'s §12.2 obligation (b).

The mechanism (pnp cap-transport hinge, `verify/capstone_cap_transport.py`; TRANSPORTS verdict): on a WIDE
branch (`d_{S+1} > widthMinUpto S`) the RAW fold reads the out-of-cap columns
(`layerCoords ∖ blockCoords`) — the capped raw descent is FALSE there (the cap-escape,
`recoord-cap-escape-note.md`). But the SOURCE-CLEARED residual `foldResid ∘ couplingClear` does NOT read
them: the escaped-column coefficients factor through the ancestor coupling coordinates, which
`couplingClear` zeroes — a FUNCTION-level kill, not a set-level containment (the escaped coords are NOT in
`couplingCoords`). So obligation (b) = the raw UNCAPPED descent ∘ `couplingClear` + the KILL.

Pieces (this module, all additive — touches no existing file):
* `continuous_foldResid` — the fold residual is continuous (`blockBlowupCoordQuot` is a projection, not a
  division), needed by the AffineOn → continuous-decomposition bridge.
* `continuous_decomp_of_homogeneousDeg1On` — the (L2) bridge: `Continuous F` + `HomogeneousDeg1On F X` ⟹
  a continuous, `X`-`IgnoresCoords` support decomposition over `X` (mirrors `Case1Wire`'s
  `exists_ignoresCoords_decomp`, with `F`-continuity as a hypothesis and the zero-constant part from the
  homogeneity vanishing clause).
* `couplingCoords_decode_layer_le` — the (L1) separation: every ancestor coupling coordinate decodes to a
  layer `≤ p.conState.layer`, so at a fresh rollover child (layer advances) `couplingClear` FIXES every
  coordinate at layers `≥` the child layer.
* `realBranch_appendResidDescent_fresh_layerCoords` — the raw UNCAPPED descent: `Deg1SupportedSlot` of the
  raw fold over the FULL descended layer `layerCoords` (NOT `blockCoords` — capped is false wide), from
  `foldResid_layerHomogeneous'` (H) + continuity.
* `sourceClearedResid_ignoresEscaped` — the KILL: the source-cleared residual ignores the escaped
  out-of-cap columns (the genuinely new content).
* `realBranch_appendResidDescent_fresh_sourceCleared'` — the primed (b)-twin (statement byte-identical to
  `SourceClearedResid.lean`'s), assembled from the raw uncapped descent ∘ `couplingClear` + the KILL +
  the separation.

Cross-ref honesty: `sourceClearedResid` is RLCT-equivalent to Aoyagi's `D_J` via the source-clear
rendering (coordinate-form differs by our shear-frame), NOT coordinate-identical.
-/

open MeasureTheory Set Filter Topology
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **Continuity of the fold residual.** `coreGen` (continuous) composed with the per-edge step maps
(`stepMap`/strict-transform `blockBlowupCoordQuot`, all continuous — the strict transform is the projection
`if k = pivot then 1 else ·`, NOT a division). Path induction. -/
theorem continuous_foldResid (d : Fin (N + 1) → ℕ) (p : TreePath d) (j : Fin (foldNR d p)) :
    Continuous (foldResid d (canonFlatten d) p j) := by
  -- map: B-CAPF-continuous-foldResid (path induction; coreGen base, continuous_stepMap step)
  sorry

/-- **(L2) The continuous support-decomposition bridge.** A continuous `F` that is
`HomogeneousDeg1On X` decomposes as `∑_{i∈X} cᵢ·uᵢ` with each `cᵢ` continuous AND ignoring `X`. Mirrors
`Case1Wire.exists_ignoresCoords_decomp` (`cᵢ u = F(Pᵢ u) − F(P₀ u)`, continuous from `hF`), with the zero
constant part forced by the homogeneity vanishing clause rather than by an input decomposition. -/
theorem continuous_decomp_of_homogeneousDeg1On {D : ℕ}
    (F : (Fin D → ℝ) → ℝ) (X : Finset (Fin D))
    (hF : Continuous F) (hhom : HomogeneousDeg1On F X Set.univ) :
    ∃ c : Fin D → (Fin D → ℝ) → ℝ, (∀ i, Continuous (c i)) ∧
      (∀ u, F u = ∑ i ∈ X, c i u * u i) ∧ (∀ i, IgnoresCoords (c i) X Set.univ) := by
  -- map: B-CAPF-continuous-decomp-bridge (exists_ignoresCoords_decomp with F-continuity + homog vanishing)
  sorry

/-- **(L1) Coupling / layer separation.** Every ancestor coupling coordinate of a real branch `p` decodes
to a layer `≤ p.conState.layer` (a case2/case12 clear's below-pivot column sits at the clearing layer, and
layers are non-decreasing along the branch). At a fresh rollover child the layer strictly advances, so
`couplingClear` fixes every coordinate at layers `≥` the child layer. -/
theorem couplingCoords_decode_layer_le (d : Fin (N + 1) → ℕ) (p : TreePath d)
    (hbranch : p.IsRealBranch (canonFlatten d))
    {y : Fin (flatDim d)} (hy : y ∈ couplingCoords d p) :
    (((tupIdxEquiv d).symm y).1.1 : ℕ) ≤ p.conState.layer := by
  -- map: B-CAPF-couplingCoords-decode-layer-le (path induction; belowPivotCol at pivot layer, layer mono)
  sorry

/-- **The raw UNCAPPED descent** (NOT `blockCoords` — the capped raw form is FALSE on wide branches, the
cap-escape). At a fresh rollover child the raw fold residual is `Deg1SupportedSlot` over the FULL descended
layer `layerCoords d (child.layer)`. From `foldResid_layerHomogeneous'` (H, conjunct-2 directly) +
`continuous_foldResid` + the (L2) bridge (conjunct-1 over `layerCoords`). -/
theorem realBranch_appendResidDescent_fresh_layerCoords (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    {p : TreePath d} (ed : TreeEdge d p)
    (hroll : ed.case = StepCase.rollover)
    (hfresh : (p.extend ed).conState.cleared = 0)
    (hlayer : (p.extend ed).conState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∀ j, Deg1SupportedSlot d (foldResid d (canonFlatten d) (p.extend ed)) j
      (layerCoords d (p.extend ed).conState.layer)
      (supportLayerOf (p.extend ed).conState)
      (foldRegion d (canonFlatten d) (p.extend ed)) := by
  -- map: B-CAPF-raw-uncapped-descent (H conjunct-2 + continuous_foldResid + L2 bridge over layerCoords)
  sorry

/-- **The KILL — the source-cleared residual ignores the escaped out-of-cap columns** ⟨GENUINELY NEW⟩.
The escaped columns `layerCoords ∖ blockCoords` (col `≥ widthMinUpto`) are read by the raw fold ONLY through
the layer-(S)-clear recoord's column mixing, whose coefficients factor through the ancestor coupling
coordinates; `couplingClear` zeroes those, so `sourceClearedResid = foldResid ∘ couplingClear` does not read
them (the FUNCTION-level kill — the escaped coords themselves are NOT in `couplingCoords`, so this is not a
set-level containment). -/
theorem sourceClearedResid_ignoresEscaped (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    {p : TreePath d} (ed : TreeEdge d p)
    (hroll : ed.case = StepCase.rollover)
    (hfresh : (p.extend ed).conState.cleared = 0)
    (hlayer : (p.extend ed).conState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d))
    (j : Fin (foldNR d (p.extend ed))) :
    IgnoresCoords (sourceClearedResid d (p.extend ed) j)
      (layerCoords d (p.extend ed).conState.layer \ blockCoords d (p.extend ed).conState.layer)
      Set.univ := by
  -- map: B-CAPF-kill-escaped ⟨GENUINELY NEW — escaped coeffs factor through ancestor couplings⟩
  sorry

/-- **Cap-frontier obligation (b), source-cleared — PRIMED TWIN.** Statement byte-identical to
`SourceClearedResid.realBranch_appendResidDescent_fresh_sourceCleared` (the controller swaps its `sorry`
for `:= realBranch_appendResidDescent_fresh_sourceCleared' …` at integration). At a fresh rollover child the
source-cleared residual is `Deg1SupportedSlot` over the running-min-capped `blockCoords`. Assembled from the
raw UNCAPPED descent ∘ `couplingClear` (via the (L1) separation, so `couplingClear` fixes the descended
layer) + the KILL (escaped columns unread), which confines the layerCoords decomposition to `blockCoords`. -/
theorem realBranch_appendResidDescent_fresh_sourceCleared' (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    {p : TreePath d} (ed : TreeEdge d p)
    (hroll : ed.case = StepCase.rollover)
    (hfresh : (p.extend ed).conState.cleared = 0)
    (hlayer : (p.extend ed).conState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∀ j, Deg1SupportedSlot d (sourceClearedResid d (p.extend ed)) j
      (blockCoords d (p.extend ed).conState.layer)
      (supportLayerOf (p.extend ed).conState)
      (foldRegion d (canonFlatten d) (p.extend ed)) := by
  -- map: B-CAPF-fresh-sourceCleared-twin (raw uncapped descent ∘ couplingClear + KILL + separation)
  sorry

end DLNFibre.DLN.Aoyagi

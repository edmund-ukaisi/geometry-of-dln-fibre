import DLNFibre.Core.Aoyagi.PrincipalInv
import DLNFibre.Core.Aoyagi.PathAtoms
import DLNFibre.Core.Aoyagi.ConjResolution
import DLNFibre.DLN.Aoyagi.LearningCoefficient

/-!
# `DLN.Aoyagi.MonumentAtlas` — the coupled monument: leaves L5–L8 + the composition driver

**BLUEPRINT (aoyagi-engine rung C; RESHAPED per the pnp-case1/pnp-cover verdicts + elder D1–D4).**
The DLN-side leaves of the coupled product-ideal resolution monument (charter §1.B) and the
composition **driver** that folds L1 + L3/L4 + `terminal_bezout` + L5 + L6 + L7 + L8 (+ the landed
leaf-2 `blowupResolution`) into `∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res` —
the residual goal of `exists_coreResolution` (`LearningCoefficient`) after
`exists_hlb_hattain_of_exists_atlasRealizesExponents`. The driver is sorried ONLY via the leaves
(`#print axioms` = `sorryAx` from exactly the leaf set).

## Wiring note for the controller (import cycle)

`exists_coreResolution` lives in `LearningCoefficient`; its residual goal speaks about `coreGen`/
`flatDim` (defined there), so a general-`d` driver that discharges it MUST sit DOWNSTREAM of
`LearningCoefficient` and cannot be called back into its in-place `sorry` without a cycle. This module
therefore provides both `exists_atlasRealizesExponents` (the residual goal, general `d`) and
`exists_coreResolution_via_monument` (the FULL `exists_coreResolution` statement, re-proved by
composition). The controller wires the canonical discharge (either promote this as canonical or reorg
`coreGen`/`flatDim` upstream) — see the report.

## Decorrelated-check gate (pnp-cover risk note; flagged at leaf 5)

The **pathwise coherence of the sheared tree fold** — the historically-masked `srcBox` seam: that the
per-branch step maps compose coherently along a root→leaf path, with each next center a coordinate
block in the accumulated sheared coordinates — is the gate for leaf 5's fold. It rides the explicit
`CenterCoordAligned` field of each `BlockChild` (Core) and the per-path monomial law of
`Case1Preservation`; it is the point to re-run the decorrelated check before striking leaf 5.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- The single monic dominant monomial `b₁(u) = ∏_d u_d^(E_d)` of an exponent vector `E`;
`(fun _ : Fin 1 ↦ monoOf E) = monomialFam (fun _ : Fin 1 ↦ E)` definitionally (the M'=1 compression).
-/
def monoOf {D : ℕ} (E : Fin D → ℕ) : (Fin D → ℝ) → ℝ := fun u ↦ ∏ i, (u i) ^ (E i)

/-! ## The geometric atlas carrier -/

/-- **One geometric recursion step** on `ℝᴰ` (shear-pin certificate): the step map
`σ = sh ∘ blockBlowupMap center pivot` (block-center blow-up ∘ unipotent shear — elder S1, spectators
`∉ center` FIXED) bundled with its Jacobian exponent `jexp` and the shape certificates. `hσ_jac`:
`|det Dσ|` is the pure block monomial `jacWeight jexp` (unit ≡ 1 — the shear is Jacobian-exactly-1),
with exponent `|center|−1` at the pivot (W2: center-size, never ambient−1). `hσ_inj`: a.e.-injective
off the pivot hyperplane. -/
structure GeoStep (D : ℕ) where
  /-- The step coordinate change (unipotent shear ∘ block-center blow-up). -/
  σ : (Fin D → ℝ) → (Fin D → ℝ)
  /-- The blow-up center `S ⊆ Fin D` of this step (spectators are `∉ center`; elder S1). -/
  center : Finset (Fin D)
  /-- The blow-up pivot coordinate of this step (`∈ center`, the exceptional axis). Recorded so
  provenance ties the branch's pivots to the leaf's `divCoord` (the `CenterCoordAligned` coherence). -/
  pivot : Fin D
  /-- The step's Jacobian monomial exponent (`|center|−1` at the pivot — W2). -/
  jexp : Fin D → ℕ
  /-- `σ` is analytic (a polynomial map). -/
  hσ_an : AnalyticOnNhd ℝ σ Set.univ
  /-- `σ` fixes the origin. -/
  hσ0 : σ 0 = 0
  /-- `|det Dσ| = jacWeight jexp` — a pure monomial, unit ≡ 1 (shear-pin §3). -/
  hσ_jac : ∀ u, |jacDet σ u| = jacWeight jexp u
  /-- `σ` is a.e.-injective off the exceptional monomial's zero set (coordinate blocks). -/
  hσ_inj : Set.InjOn σ (Set.univ \ {w : Fin D → ℝ | jacWeight jexp w = 0})

/-- **The geometric resolution atlas** produced by the fold (L5): `n` charts, each a root→leaf branch
of shear ∘ blow-up steps, with a compact source domain, an open certificate region, and the dominant
monomial / total Jacobian exponents. The path map of chart `c` is `pathMap` of its step σ's
(`gmap`). Well-formedness (topology, binding, unit-multiplicity/squarefreeness of `b₁`) is carried as
fields. -/
structure GeoAtlasData (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) where
  /-- Number of geometric charts (root→leaf branches). -/
  n : ℕ
  /-- The atlas is nonempty. -/
  hn : 0 < n
  /-- Per-chart root→leaf step sequence (root = head, outermost). -/
  steps : Fin n → List (GeoStep (flatDim d))
  /-- Per-chart compact source domain (a closed box in resolved coordinates — pnp-cover). -/
  dom : Fin n → Set (Fin (flatDim d) → ℝ)
  /-- Per-chart open certificate region (the `nbhd`). -/
  region : Fin n → Set (Fin (flatDim d) → ℝ)
  /-- Per-chart dominant monomial `b₁` exponent. -/
  bexp : Fin n → (Fin (flatDim d) → ℕ)
  /-- Per-chart total Jacobian monomial exponent. -/
  jac : Fin n → (Fin (flatDim d) → ℕ)
  /-- Each region is open. -/
  hregion_open : ∀ c, IsOpen (region c)
  /-- Each region contains the origin. -/
  hzero_region : ∀ c, (0 : Fin (flatDim d) → ℝ) ∈ region c
  /-- Each source domain is compact. -/
  hdom_compact : ∀ c, IsCompact (dom c)
  /-- Each source domain contains the origin. -/
  hzero_dom : ∀ c, (0 : Fin (flatDim d) → ℝ) ∈ dom c
  /-- Each source domain sits inside its region. -/
  hdom_sub : ∀ c, dom c ⊆ region c
  /-- Each dominant monomial binds along some axis. -/
  hbind : ∀ c, (bindingAxes (bexp c)).Nonempty
  /-- **Squarefree `b₁`** — unit divisor multiplicity `k_d = 1` on binding axes (Aoyagi
  worked.tex:495; condition (4)'s squarefreeness). -/
  hsqfree : ∀ c, ∀ a ∈ bindingAxes (bexp c), bexp c a = 1

/-- The path map of chart `c`: the composition of its step σ's (`pathMap`, root outermost). -/
def GeoAtlasData.gmap {d : Fin (N + 1) → ℕ} {e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d}
    (a : GeoAtlasData d e) (c : Fin a.n) : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  pathMap ((a.steps c).map GeoStep.σ)

/-- **The fold-provenance predicate (rev-leaves round-2 anchor).** The structural bridge tying a
`GeoAtlasData` to `buildTree d (conOracle d) conRoot` — WITHOUT it, `leafPath_compactCover` (L7) and
`leafPath_realizesExponents` (L8) are FALSE as `∀ atlas` statements (a bare atlas carries no
tree/fold link: the degenerate `n=1, steps=[], dom={0}` breaks L7; adversarial `jac := Σ+1` breaks
L8). `FoldProduced` RECORDS what L5's fold constructs — DEFINITIONAL bookkeeping only, NOT the cover
(that stays L7's proof obligation) and NOT the `∈ terminalExponents` lift (that stays L8's):

* `leafOf` — the chart↔leaf correspondence into the tree's leaves (`hmem`), SURJECTIVE (`hsurj`: every
  leaf, in particular the `minAdm`-attainer, gets a chart);
* `hjac_mem` / `hjac_onto` — the exponent read-off: each binding-axis `jac a + 1` IS one of `leafOf c`'s
  divisor exponents (kills the adversarial `jac`), and every divisor exponent is realised by some binding
  axis (feeds L8 clause (ii));
* `hdom_ball` — each source domain contains a nontrivial ball (kills the `dom = {0}` degeneracy; weaker
  than fixing a radius, so D2'-compatible with the terminal region-shrink);
* **σ-PROVENANCE (rev-leaves round-3 B; elder-ratified):** `hstep_block` — every step IS a genuine
  block-center blow-up (`pivot ∈ center`, `jexp = (|center|−1)` at the pivot, `0` off it), and
  `hjac_tie` — `atlas.jac` is the ACCUMULATED step-ledger `∑ steps s.jexp`, NOT a free field. Together
  they kill the wrong-pivot / hand-set-`jac` atlas (Lean-confirmed to miss whole directions) that the
  count-only provenance admitted: `jac` can no longer be dialled to match a leaf it does not geometrically
  realise. Aoyagi-side (no `RLCT.flatDim`↔`Aoyagi.flatDim` card↔sum bridge — that stays next-expedition
  runway; the landed `AtlasRealizesExponents` seam likewise stays at ℕ-valued `divExp`, never `divCoord`).
* `hcard_tie` — `(bindingAxes bexp).card = leafOf.numDiv` (elder ii; ℕ-valued, merge/rollover-immune,
  replacing the UNSATISFIABLE `steps.length = numDiv` — a Case-1(1) merge is a genuine block blow-up that
  births NO divisor, so a branch's step-count exceeds its `t̃=0` divisor count). With `hjac_mem`/`hjac_onto`
  it does the anti-degeneracy work for L8. -/
def FoldProduced {N : ℕ} (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (atlas : GeoAtlasData d e) : Prop :=
  ∃ leafOf : Fin atlas.n → LeafData d,
    (∀ c, leafOf c ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N))) ∧
    (∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
      ∃ c, leafOf c = l) ∧
    (∀ (c : Fin atlas.n) (a : Fin (flatDim d)), a ∈ bindingAxes (atlas.bexp c) →
      ∃ k : Fin (leafOf c).numDiv, atlas.jac c a + 1 = (leafOf c).divExp k) ∧
    (∀ (c : Fin atlas.n) (k : Fin (leafOf c).numDiv),
      ∃ a : Fin (flatDim d), a ∈ bindingAxes (atlas.bexp c) ∧ atlas.jac c a + 1 = (leafOf c).divExp k) ∧
    (∀ c, ∃ R : ℝ, 0 < R ∧ Metric.closedBall (0 : Fin (flatDim d) → ℝ) R ⊆ atlas.dom c) ∧
    (∀ (c : Fin atlas.n) (s : GeoStep (flatDim d)), s ∈ atlas.steps c →
      s.pivot ∈ s.center ∧ ∀ a, s.jexp a = if a = s.pivot then s.center.card - 1 else 0) ∧
    (∀ (c : Fin atlas.n) (a : Fin (flatDim d)),
      atlas.jac c a = ((atlas.steps c).map (fun s => s.jexp a)).sum) ∧
    (∀ c, (bindingAxes (atlas.bexp c)).card = (leafOf c).numDiv)

/-! ## The foldState monument spine (round-5 RESHAPE; elder-locked) — `TreePath` + the coupled fold

**The foldState recursion MERGES the two honest shapes** (`Core.PrincipalInv` closing principle, roads
(a)+(b)): a `TreePath` is a root→node path of `buildTree d (conOracle d) conRoot`, and the resolved
state at that node — the accumulated coordinate change `foldG`, the dominant monomial `foldB`, the
residual family `foldResid`, and the certificate region `foldRegion` — is READ OFF the path BY
DEFINITION (structural recursion), NOT quantified as a free `(state, spec)`. Provenance is therefore
DEFINITIONAL: the four dead refutations the free-standing `∀-(state, spec)` form admitted — the
constant family (S3), the kernel-refuted Σw² Case-2 spectator-support witness, the `|S|=1`/`sh=id`
lazy witness, and the `SupportedOn`-severance — ALL die BY DEFINITION, because there is no free state
or residual to adversarially instantiate: the fold's own accumulated data is the only state, and the
residual is `foldResid p`, pinned. The one-step preservation leaves become `FoldStepInv d e p →
FoldStepInv d e (p.extend ed)`, indexed by the path (road (b)) whose data IS the fold (road (a)).

The per-edge shear `σ = sh ∘ blockBlowupMap S p` (elder S1) is carried as the `shearφ` field of a
`TreeEdge` (the Q/Schur Let-block φ); its Jacobian-exactly-1 property (`hshear`, shear-pin thread 33)
and origin-fixing (`hshear0`) travel with the edge. `edgeδ = [J=0]` is read OFF the state
(`conState.cleared`), UNIFORM across sub-cases (S2), never the edge kind.

**IMPLEMENTATION NOTES (total, proof-free DATA defs; flagged for the fidelity review):**
* `TreePath.step`/`extend` carry `shearφ` as a 6th field (beyond the locked 5): the fold's
  `stepMap d ed` provably needs the shear to survive `extend` — else `foldG (p.extend ed) = foldG p ∘
  stepMap d ed` is FALSE for a non-identity shear — so the shear is stored on the path, not only the
  edge. `TreePath.step` stores only the DATA `shearφ`, not the `hshear`/`hshear0` proofs (the path is
  proof-free; the leaves receive the proofs via `ed : TreeEdge d p`).
* `foldNR` child counts are STAND-INS: case-2 APPENDS one (`+1`, via `Fin.snoc`); case-1/rollover keep
  the parent count (the exact clear = `center.card` refinement is deferred). `foldResid`'s case-2
  appended entry is the coordinate `u ↦ u_pivot` (a total stand-in for the Schur/clear closed form —
  NEVER a division / exactness choice, per the design guard); the carried entries are the pullback
  `foldResid p ∘ stepMap`.
* `edgeChartDom = Set.univ`, so `foldRegion ≡ Set.univ` (open, ∋ 0 — provable WITHOUT shear continuity,
  which is not a stored field); the terminal region-shrink (D2') is deferred to L5 / `terminal_bezout`.
* `terminal_bezout` stays the untouched Core theorem (`Core.Aoyagi.terminal_bezout : TerminalBezout`);
  re-anchoring it to the foldState was not needed — L5 consumes it directly. -/

/-- A root→node path of `buildTree d (conOracle d) (conRoot : ConState N)`: `root` at the top; a
`step` carrying one edge's data (`center`, `pivot`, `case`, the child `nextState`, and the unipotent
shear displacement `shearφ`). -/
inductive TreePath (d : Fin (N + 1) → ℕ) : Type where
  | root : TreePath d
  | step (p : TreePath d) (center : Finset (Fin (flatDim d))) (pivot : Fin (flatDim d))
      (case : StepCase) (nextState : ConState N)
      (shearφ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) : TreePath d

/-- The construction state at a path node (`root ↦ conRoot`; a step ↦ its recorded `nextState`). -/
def TreePath.conState {d : Fin (N + 1) → ℕ} : TreePath d → ConState N
  | .root => conRoot
  | .step _ _ _ _ s _ => s

/-- An outgoing edge at a path node `p`: the blow-up `center`/`pivot` (`pivot ∈ center`), the step
`case`, the child `nextState`, and the unipotent shear `shearφ` of the Q/Schur closed form —
Jacobian-exactly-1 (`hshear`) and origin-fixing (`hshear0`), the shear-pin certificate carried as
edge data (elder S1). -/
structure TreeEdge (d : Fin (N + 1) → ℕ) (p : TreePath d) where
  /-- The blow-up center `S ⊆ Fin (flatDim d)`. -/
  center : Finset (Fin (flatDim d))
  /-- The blow-up pivot (the exceptional axis). -/
  pivot : Fin (flatDim d)
  /-- The pivot lies in the center. -/
  hpivot : pivot ∈ center
  /-- Which branch of the `(S,J)` step this edge realises. -/
  case : StepCase
  /-- The child construction state. -/
  nextState : ConState N
  /-- The unipotent shear displacement (the Q/Schur Let-block φ). -/
  shearφ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)
  /-- The shear is Jacobian-exactly-1 (shear-pin, thread 33). -/
  hshear : ∀ u, jacDet (blockShear shearφ) u = 1
  /-- The shear displacement fixes the origin. -/
  hshear0 : shearφ 0 = 0

/-- The edge realises a case-2 (full-block append) step. -/
def TreeEdge.isCase2 {d : Fin (N + 1) → ℕ} {p : TreePath d} (ed : TreeEdge d p) : Prop :=
  ed.case = StepCase.case2

/-- The edge realises a case-1 (`11` merge or `12` split) step. -/
def TreeEdge.isCase1 {d : Fin (N + 1) → ℕ} {p : TreePath d} (ed : TreeEdge d p) : Prop :=
  ed.case = StepCase.case11 ∨ ed.case = StepCase.case12

/-- The edge realises a rollover (layer-advance) step. -/
def TreeEdge.isRollover {d : Fin (N + 1) → ℕ} {p : TreePath d} (ed : TreeEdge d p) : Prop :=
  ed.case = StepCase.rollover

/-- Extend a path by one edge. Keeps `shearφ` (see the section note); drops the edge proof fields. -/
def TreePath.extend {d : Fin (N + 1) → ℕ} (p : TreePath d) (ed : TreeEdge d p) : TreePath d :=
  TreePath.step p ed.center ed.pivot ed.case ed.nextState ed.shearφ

/-! ### Center/pivot spec (seat-L4 drift-guard; controller calibration 26)

`ConState` is purely COMBINATORIAL (`layer S`, `cleared J`, `numDiv`, `divExp`, `divProfile`, …); it
carries NO coordinate-level center/pivot. So `TreeEdge.center`/`.pivot` — kept as the elder-locked
structure FIELDS — are NOT yet pinned to the construction. The INTENDED derivation (the spec the
construction must meet, checkable against thread-37's (3,3,4) battery once the coordinate bridge lands):

* `edgeCenter d S J` = the flat indices (in `Aoyagi.flatDim d`, decoded via `tupIdxEquiv`) of the
  layer-`S` residual block with row, col ≥ `J`;
* `edgePivot` = the merged old-`u` exceptional coordinate (case-1(1)) / a fresh `d`-entry (case-1(2) /
  case-2);
* (3,3,4) table: S=1 case-2 appends have center codims 9, 4, 1; S=2 the 1×2 block has a codim-2 center;
  the case-1(1) merge at (S=2, J=0) has center = {d-block ∪ old-u} with pivot = the old-u coord; the
  1(2) split pivots at a fresh d-entry.

NOT FABRICATED into `edgeCenter`/`edgePivot` DEFS here: the map from the engine's `RLCT.flatDim`
divisor coordinates to `Aoyagi.flatDim d` is the deferred coordinate bridge (next-expedition runway;
flagged in `FoldProduced` + memory). A def body written without that bridge would be a name≠content
violation. Until it lands, the leaves quantify over ALL `ed` (free center/pivot) — the STRONGEST form
(the seat must handle every center, including the construction's); pinning `ed.center = edgeCenter …`
is the implementation-owned refinement that awaits the bridge. -/

/-- `δ = [J = 0]` — read OFF the node state's cleared count (never the edge kind). -/
def edgeδ (d : Fin (N + 1) → ℕ) (p : TreePath d) : Bool := decide (p.conState.cleared = 0)

/-- **The per-case step shear** (seat-L4 consumer pin): `sh = id` at a case-1(1) MERGE edge and at a
ROLLOVER edge (the merge substitutes into the existing exceptional / the rollover is a ledger relabel,
both `localSub = id`, seat-L4 §4 cert); `sh = blockShear φ` at a case-1(2) SPLIT and a case-2 append
(the Q/Schur closed form). Keyed off the case so the seat can rewrite `edgeShear → id` from the tag. -/
def edgeShearRaw (d : Fin (N + 1) → ℕ) (cse : StepCase)
    (shearφ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  match cse with
  | StepCase.case11 => id
  | StepCase.rollover => id
  | _ => blockShear shearφ

/-- `edgeShearRaw` fixes the origin when the displacement does (`id 0 = 0` / `blockShear_zero`). -/
theorem edgeShearRaw_zero (d : Fin (N + 1) → ℕ) (cse : StepCase)
    (shearφ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) (h0 : shearφ 0 = 0) :
    edgeShearRaw d cse shearφ 0 = 0 := by
  cases cse <;> first | rfl | exact blockShear_zero shearφ h0

/-- The step shear at an edge (`= edgeShearRaw` on the edge's case + φ). -/
def edgeShear (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  edgeShearRaw d ed.case ed.shearφ

/-- The step map on stored edge data: `edgeShearRaw case φ ∘ blockBlowupMap center pivot` (the fold
uses this form so the defining equations hold on the raw `TreePath.step` fields, per-case). -/
def stepMapRaw (d : Fin (N + 1) → ℕ) (cse : StepCase) (center : Finset (Fin (flatDim d)))
    (pivot : Fin (flatDim d)) (shearφ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  edgeShearRaw d cse shearφ ∘ blockBlowupMap center pivot

/-- One step's coordinate change: (per-case) shear ∘ block-center blow-up. Equals
`stepMapRaw d ed.case ed.center ed.pivot ed.shearφ` definitionally. -/
def stepMap (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  edgeShear d ed ∘ blockBlowupMap ed.center ed.pivot

/-- **Def-lemma** — `jacDet (edgeShear d ed) u = 1` (shear-pin): `id` at merge/rollover (`jacDet_id`),
`blockShear` elsewhere (`hshear`). -/
theorem jacDet_edgeShear (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (u : Fin (flatDim d) → ℝ) : jacDet (edgeShear d ed) u = 1 := by
  unfold edgeShear edgeShearRaw
  split <;> first | exact jacDet_id u | exact ed.hshear u

/-- **Def-lemma** — `stepMap d ed 0 = 0` (the step map fixes the origin). -/
theorem stepMap_zero (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    stepMap d ed 0 = 0 := by
  change edgeShear d ed (blockBlowupMap ed.center ed.pivot 0) = 0
  rw [blockBlowupMap_zero]
  exact edgeShearRaw_zero d ed.case ed.shearφ ed.hshear0

/-- The accumulated coordinate change along a path (`root ↦ id`; `p.extend ed ↦ foldG p ∘ stepMap`). -/
def foldG (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    TreePath d → ((Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ))
  | .root => id
  | .step p center pivot cse _ shearφ => foldG d e p ∘ stepMapRaw d cse center pivot shearφ

/-- The accumulated dominant monomial along a path (`root ↦ 1`; step ↦ `u_pivot^δ ·` the pullback). -/
def foldB (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    TreePath d → ((Fin (flatDim d) → ℝ) → ℝ)
  | .root => fun _ => 1
  | .step p center pivot cse _ shearφ => fun u =>
      (u pivot) ^ (if edgeδ d p then 1 else 0) * foldB d e p (stepMapRaw d cse center pivot shearφ u)

/-- The residual family length along a path (`root ↦ d_N·d_0`; case-2 appends one; else unchanged). -/
def foldNR (d : Fin (N + 1) → ℕ) : TreePath d → ℕ
  | .root => d (Fin.last N) * d 0
  | .step p _ _ StepCase.case2 _ _ => foldNR d p + 1
  | .step p _ _ StepCase.case11 _ _ => foldNR d p
  | .step p _ _ StepCase.case12 _ _ => foldNR d p
  | .step p _ _ StepCase.rollover _ _ => foldNR d p

/-- The residual family along a path (`root ↦ coreGen d e`; case-2 appends the coordinate `u_pivot`;
else the pullback `foldResid p ∘ stepMap` — the Schur/clear closed form is a total stand-in here, never
a division/exactness choice: that belongs to the `∃q` of `FoldStepInv`, not this DATA def). -/
noncomputable def foldResid (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    (p : TreePath d) → (Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ)
  | .root => coreGen d e
  -- case-2 (full-block APPEND): pullback carried entries + snoc the new block coordinate `u_pivot`.
  --   Seat-L4 fires `WeightedCofactor.weightedCofactor_transport` on the carried entries.
  | .step p center pivot StepCase.case2 _ shearφ =>
      Fin.snoc (fun j u => foldResid d e p j (stepMapRaw d StepCase.case2 center pivot shearφ u))
        (fun u => u pivot)
  -- case-1(1) MERGE (sh = id): pullback through `blockBlowupMap` alone — seat-L4 fires
  --   `BlockDivision.blockBlowup_center_comb_eq` (exact `/u_p`, `blockBlowupCoordQuot`). Never quotient-by-u_p.
  | .step p center pivot StepCase.case11 _ shearφ =>
      fun j u => foldResid d e p j (stepMapRaw d StepCase.case11 center pivot shearφ u)
  -- case-1(2) SPLIT: pullback through shear ∘ blow-up — seat-L4 fires `weightedCofactor_transport`.
  | .step p center pivot StepCase.case12 _ shearφ =>
      fun j u => foldResid d e p j (stepMapRaw d StepCase.case12 center pivot shearφ u)
  -- rollover (sh = id): reindex/absorb (p.19 transpose boundary), no blow-up content.
  | .step p center pivot StepCase.rollover _ shearφ =>
      fun j u => foldResid d e p j (stepMapRaw d StepCase.rollover center pivot shearφ u)

/-- A total open certificate domain per edge (`Set.univ` stand-in — the D2' shrink is deferred). -/
def edgeChartDom (d : Fin (N + 1) → ℕ) {p : TreePath d} (_ed : TreeEdge d p) :
    Set (Fin (flatDim d) → ℝ) := Set.univ

/-- The accumulated certificate region along a path (`root ↦ univ`; step ↦ pullback ∩ chart dom). -/
def foldRegion (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    TreePath d → Set (Fin (flatDim d) → ℝ)
  | .root => Set.univ
  | .step p center pivot cse _ shearφ =>
      stepMapRaw d cse center pivot shearφ ⁻¹' foldRegion d e p ∩ Set.univ

/-- `foldRegion ≡ Set.univ` (the `edgeChartDom = univ` stand-in). -/
theorem foldRegion_eq_univ {d : Fin (N + 1) → ℕ} (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    ∀ p : TreePath d, foldRegion d e p = Set.univ
  | .root => rfl
  | .step p center pivot cse _ shearφ => by
      change stepMapRaw d cse center pivot shearφ ⁻¹' foldRegion d e p ∩ Set.univ = Set.univ
      rw [foldRegion_eq_univ e p, Set.preimage_univ, Set.inter_univ]

/-- `foldRegion` is open. -/
theorem isOpen_foldRegion (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) : IsOpen (foldRegion d e p) := by
  rw [foldRegion_eq_univ]; exact isOpen_univ

/-- `foldRegion` contains the origin. -/
theorem zero_mem_foldRegion (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) : (0 : Fin (flatDim d) → ℝ) ∈ foldRegion d e p := by
  rw [foldRegion_eq_univ]; exact Set.mem_univ _

/-- **The b-chain one-step ratio (seat-L4 consumer, `hratio`).** `foldB (p.extend ed) = u_pivot^δ ·
(foldB p ∘ stepMap)`, `δ = edgeδ d p ∈ {0,1}`. This is the exact ratio the generalized-CommRing Q̂
commutation consumes; iterated along a path it is the prefix-monomial structure `b = ∏_edges u_pivot^δ`.
(A `Dvd` Prop over ℝ-valued `foldB` would be vacuous — the honest content is this ratio.) -/
theorem foldB_extend_eq (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (u : Fin (flatDim d) → ℝ) :
    foldB d e (p.extend ed) u
      = (u ed.pivot) ^ (if edgeδ d p then 1 else 0) * foldB d e p (stepMap d ed u) := rfl

/-- **The foldState step invariant at a path node** (the merged-roads form): a divisibility witness
`q` for the accumulated `StepInv (coreGen) (foldG p) (foldB p) (foldResid p) q (foldRegion p)`. The
state IS the fold's own accumulated data — no free state/residual to instantiate. -/
def FoldStepInv {N : ℕ} (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) : Prop :=
  ∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ,
    StepInv (coreGen d e) (foldG d e p) (foldB d e p) (foldResid d e p) q (foldRegion d e p)

/-! ## L3 / L4 — the foldState one-step preservations (DLN-side; elder-locked round-5)

The free-standing `∀-(state, spec)` form was not honest (`Core.PrincipalInv` closing principle). Three
of its four refutations (constant, Σw², `|S|=1` on the STATE axis) die BY DEFINITION in the foldState
form (there is no free state or residual to instantiate; the state IS `foldG`/`foldB`/`foldResid p`).
The FOURTH — the `SupportedOn`-gap on the CENTER axis — does NOT die by definition: `ed.center` is a
free field of `TreeEdge` (the coordinate derivation is bridge-blocked), so a center not covering the
state's support re-admits the `δ=1` refutation. It is closed by the EXPLICIT hypothesis `hsupp :
SupportedOn (foldResid d e p) ed.center (foldRegion d e p)` (elder round-5 ruling (B)+(i), ideal-
membership form) on BOTH leaves (ruling (ii): the root edge is case-2 `δ=1`, so case-2 needs it too).
The hypothesis is the construction's DEFINITIONAL truth — Aoyagi's center IS the residual block's
coordinates (pp. 16/19) — so L5 discharges it for free at every real fold edge; no spurious-hypothesis
smell. Each leaf is the one-step `FoldStepInv d e p → FoldStepInv d e (p.extend ed)`, indexed by the
path node and one outgoing edge; `δ = [J=0]` off `p.conState.cleared` (`edgeδ`, UNIFORM across
sub-cases). Rollover is off the `isCase2`/`isCase1` filters by construction (`localSub = id`). -/

/-- **L3 — a case-2 edge preserves the foldState invariant** (full-block append regime). `hsupp` (the
center covers `foldResid p`'s support, ideal-membership form) is REQUIRED even here — the root edge is
case-2 `δ=1`, where a non-covering center refutes the plain statement (elder ruling (ii)). -/
@[blueprint]
theorem case2_preserves_stepInv
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e)
    (p : TreePath d) (ed : TreeEdge d p) (hcase2 : ed.isCase2)
    (hsupp : SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (hinv : FoldStepInv d e p) :
    FoldStepInv d e (p.extend ed) := by
  -- map: B-L3-case2-preserves-stepInv (foldState; block-center append, δ off the state; hsupp closes center)
  sorry

/-- **L4 — a case-1 edge preserves the foldState invariant. ⟨THE WALL⟩** The coupled block-center
divisibility at corank ≥ 2 with the exact `u_p^δ` factor; seat-L4's `BlockDivision` core (exact
division; the `2u₀u₂` shear-rescue) supplies the proof. `hsupp` (the ideal-membership center-support
link) is what delivers the exact `u_p` division (each `foldResid p` monomial carries a center variable,
so `∘ blockBlowupMap` gains `u_p`). ONE center, the merge/split pivots handled inside the fold — no free
`∀`-branch, no `p_merge`/`p_split` in the statement. -/
@[blueprint]
theorem case1_preserves_stepInv
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e)
    (p : TreePath d) (ed : TreeEdge d p) (hcase1 : ed.isCase1)
    (hsupp : SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (hinv : FoldStepInv d e p) :
    FoldStepInv d e (p.extend ed) := by
  -- map: B-L4-case1-coupled-preserves-stepInv ⟨THE WALL — coupled block-center divisibility, seat-L4⟩
  sorry

/-! ## L5 — the path fold: `StepInv` folded to per-chart terminal `PrincipalInv`

**DISSOLVED named gaps (rev-leaves FIX 2 + FIX 5; elder second delta — recorded so no one re-invents
them).** Two Props were originally carried here as `∀ d`-hypotheses ("D3 named gaps"); both are gone:

* `StructuralChainResidual` — the per-leaf SCALAR `∣`-comparability of `divExp` — is **OUTRIGHT FALSE**
  (elder witness, corroborated by the `g-monument-mval-instances.py` battery): the binding leaf of
  `(3,3,4)` carries divisor exponents (`jac+1`) `{9 (ρ), 8 (E), 4 (α)}`, and `8 ∤ 9`, `9 ∤ 8`. It
  re-introduced the paper's EXCISED T-profile total-comparability (worked.tex T-F) in scalar form.
  What thread-31's closed form actually discharges is the PER-PATH MONOMIAL law — `b' = u_p^δ·(b∘σ)`,
  `u_p` FRESH, `δ ∈ {0,1}` — i.e. prefix-divisibility in exponent VECTORS along a branch, which is
  ALREADY the content of `Case1Preservation`/`BlockChild`'s witness law (Core) and what L6's
  squarefree-`b₁` and L8's ledger alignment consume. So it dissolves into the invariant; DELETED.
* `PivotOrderingK0` — a scalar `argmin` over a nonempty finite ℕ-family — is trivially TRUE and was
  never a gap; if a pre-compression step genuinely selects a dominant monomial the honest object is
  pointwise-≤ VECTOR minimality (the `hchain` shape), carried by `GeoAtlasData.bexp` + `hsqfree`, not a
  separate hypothesis. DELETED.
-/

/-- **L5 — the path fold produces the geometric atlas.** Folding the interior `StepInv` from the
trivial root state (`g = id`, `b = 1`, residual `= coreGen`) down each root→leaf branch of the built
tree, via the one-step preservations (`case2_preserves_stepInv`, `case1_preserves_stepInv`) at each
edge, reaching the terminal state where `terminal_bezout` upgrades divisibility to the terminal
`PrincipalInv` (both directions). Produces a `GeoAtlasData` that (a) satisfies `FoldProduced` — the
provenance RECORD of its own construction (one chart per tree leaf, exponents read off the ledger,
pivots = the leaf's `divCoord`, doms nontrivial), cheap since L5 builds exactly that — and (b) carries
the terminal `PrincipalInv` for each chart's path map on its region.

Hypotheses = the three one-step obligations (L3/L4/`terminal_bezout`) ONLY (the two former D3 gaps
dissolved — see the section note). **Region-shrink ordering (elder D2', the no-implicit-shrinking
discipline at assembly):** `terminal_bezout` legitimately SHRINKS each chart's region to
`V ∩ {q i₀ ≠ 0}`, so the fold must choose each chart's compact `dom` / open `region` AFTER all
per-step and terminal shrinkings — the emitted `atlas.dom c ⊆ atlas.region c` (a `GeoAtlasData` field)
sits inside the FINAL shrunken region, never a pre-shrink one. The `srcBox`-seam pathwise coherence
(module docstring) is the decorrelated-check gate riding the `CenterCoordAligned` fields. -/
@[blueprint]
theorem leaf_stepInv_of_path (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0)
    (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ atlas : GeoAtlasData d e, FoldProduced d e atlas ∧
      ∀ c : Fin atlas.n, ∃ q r : Fin (d (Fin.last N) * d 0) → (Fin (flatDim d) → ℝ) → ℝ,
        PrincipalInv (coreGen d e) (atlas.gmap c) (monoOf (atlas.bexp c)) q r (atlas.region c) := by
  -- map: B-L5-path-fold (fold FoldStepInv via the foldState leaves along tree branches;
  --      terminal_bezout at each leaf; emits the FoldProduced provenance record of the construction)
  -- Reference the foldState one-step leaves + terminal_bezout: the fold consumes these, so they sit
  -- on the monument cone (records them for #audit_blueprint even while the fold body is sorried).
  have _hc2 := case2_preserves_stepInv (d := d)
  have _hc1 := case1_preserves_stepInv (d := d)
  have _hterm : TerminalBezout := terminal_bezout
  sorry

/-! ## L6 — the chart geometry: assemble a certified `Chart` from a branch -/

/-- **L6 — the chart geometry.** For a chart `c` of the atlas, the path map `gmap c` (a composition of
shear ∘ blow-up steps) is analytic, origin-fixing, and a.e.-injective, with `|det D(gmap c)| =
jacWeight (jac c) · unit` (unit ≡ 1 — the shear-pin Jacobian, the shears Jacobian-exactly-1 and the
exceptional coordinates untouched by later shears) and squarefree dominant `b₁` (binding axes carry
exponent 1). Given the two region-ideal inclusions (from L1, on the region), it ASSEMBLES a certified
`Chart (coreGen d e) 0` whose map/domain/region/exponents are the atlas's. The GENUINE content is the
fold of the per-step geometry (`GeoStep` fields) into the path-map geometry. Region-quantified
(condition (1)): all certificates on `region c`.

**L6 HARD LOCK (elder-locked, gate-enforced).** `Chart.nbhd` must be the `terminal_bezout`-shrunk `V′`,
NEVER `univ` — the two-sided ideal identity is LOCAL; `RegionRepresents`-on-`univ` is false in general.
The gate REFUSES any L6 render with `nbhd = univ`. (`edgeChartDom = univ` in the current foldState
stand-in is the D2'-deferred region for the SPINE; the Chart this leaf emits must carry the bounded
shrunk region, not univ.) -/
@[blueprint]
theorem leafPath_chartGeometry (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (atlas : GeoAtlasData d e) (c : Fin atlas.n)
    (hfwd : RegionRepresents (fun i ↦ coreGen d e i ∘ atlas.gmap c)
      (fun _ : Fin 1 ↦ monoOf (atlas.bexp c)) (atlas.region c))
    (hbwd : RegionRepresents (fun _ : Fin 1 ↦ monoOf (atlas.bexp c))
      (fun i ↦ coreGen d e i ∘ atlas.gmap c) (atlas.region c)) :
    ∃ chart : Chart (coreGen d e) 0,
      chart.g = atlas.gmap c ∧ chart.dom = atlas.dom c ∧ chart.nbhd = atlas.region c ∧
        chart.bexp chart.k₀ = atlas.bexp c ∧ chart.jac = atlas.jac c := by
  -- map: B-L6-chart-geometry (fold per-step analytic/inj/Jacobian into the path-map Chart; unit ≡ 1)
  sorry

/-! ## L7 — the compact cover (pnp-cover verdict: FULL cover, empty escape) -/

/-- **L7 — the compact cover (STRONGER inclusion form, pnp-cover thread 35).** For a FOLD-PRODUCED
atlas (`hfold`: the charts are the tree's branches — one per leaf, pivots = the leaf's `divCoord`,
doms nontrivial), a ball around the origin is FULLY covered (empty escape) by the images of the
charts' compact source domains: `ball 0 ρ ⊆ ⋃ c, (gmap c) '' (dom c)`. Without `hfold` the statement
is FALSE (`l7probe`: the degenerate `n=1, steps=[], dom={0}` atlas has union `{0}`). Routing =
top-down argmax lift `x ↦ (leaf, resolved w)` descending the REAL tree (the `hfold` correspondence);
the shear inverses are polynomial; each atom is the BLOCK-CENTER bounded-spectator cover
(`blockBlowupMap`, spectators bounded in a `cubeBox × cubeBox`, never `pivotDomain × univ`),
generalized R = 1 → R-parametric (the no-inflation trick dies once shears give bound 2). The driver
closes the record `hcover` by `Set.diff_eq_empty.2 hsub ▸ measure_empty` (the landed `OriginBlowup`
idiom, the `S = univ` single-level instance of the block cover). -/
@[blueprint]
theorem leafPath_compactCover (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (atlas : GeoAtlasData d e) (hfold : FoldProduced d e atlas) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball (0 : Fin (flatDim d) → ℝ) ρ ⊆ ⋃ c, (atlas.gmap c) '' (atlas.dom c) := by
  -- map: B-L7-compact-cover (fold-provenance argmax lift; R-parametric block-center atom; empty escape)
  sorry

/-! ## L8 — the exponents ↔ ledger match (feeds `AtlasRealizesExponents`) -/

/-- **L8 — the atlas exponents realize the built tree's terminal spectrum.** The two clauses of
`AtlasRealizesExponents`, phrased on the atlas's own `bexp`/`jac`: (i) every chart binding-axis
exponent `jac a + 1` is a terminal exponent of `buildTree d (conOracle d) conRoot`; (ii) every
`minAdm`-attaining leaf divisor exponent is matched by some chart's binding-axis exponent. This is the
value-support match (NOT a structural chart↔leaf correspondence — RecursionAdapter). For a
FOLD-PRODUCED atlas (`hfold`), the geometric blow-up exponents are linked to the combinatorial divisor
exponents through the provenance's read-off (`jac a + 1` IS a `leafOf c` divisor exponent; surjective
onto leaves) — WITHOUT `hfold` the statement is FALSE (`l8probe`: adversarial `jac := Σ+1` exceeds the
terminal spectrum). Uses the per-path monomial law, NOT the former false `StructuralChainResidual`
(see the L5 dissolution note). Generalizes the LANDED `exists_atlasRealizesExponents_d12` match
(`jac a + 1 = flatDim − 1 + 1 = 2 = minAdm ![1,2]`) to general `d`. -/
@[blueprint]
theorem leafPath_realizesExponents (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (atlas : GeoAtlasData d e)
    (hfold : FoldProduced d e atlas) :
    (∀ (c : Fin atlas.n) (a : Fin (flatDim d)), a ∈ bindingAxes (atlas.bexp c) →
        (atlas.jac c a + 1) ∈
          ResolutionTree.terminalExponents (buildTree d (conOracle d) (conRoot : ConState N))) ∧
      (∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
        ∀ k : Fin l.numDiv, l.divExp k = minAdm d →
          ∃ (c : Fin atlas.n) (a : Fin (flatDim d)),
            a ∈ bindingAxes (atlas.bexp c) ∧ atlas.jac c a + 1 = l.divExp k) := by
  -- map: B-L8-exponents-ledger (geometric blow-up exponents = tree divExps; value-support match)
  sorry

/-! ## The composition driver — the residual goal of `exists_coreResolution` -/

/-- **The composition driver — general `d`.** Folds the leaves into
`∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res` (the residual goal of
`exists_coreResolution` after `exists_hlb_hattain_of_exists_atlasRealizesExponents`). Sorried ONLY via
the leaves: L5 (`leaf_stepInv_of_path`) supplies the atlas + per-chart terminal `PrincipalInv`
(itself folding L3/L4/`terminal_bezout`); L1 (`principalInv_regionRepresents`) turns each into the two
`RegionRepresents`; L6 (`leafPath_chartGeometry`) assembles each certified `Chart`; L7
(`leafPath_compactCover`) gives the full cover; L8 (`leafPath_realizesExponents`) gives the exponent
match. Generalizes the LANDED `exists_atlasRealizesExponents_d12` from `d = ![1,2]` to all `d`.
`@[blueprint]` — it rests on the (still-forecast) leaves; strikes to banked when they land. -/
@[blueprint]
theorem exists_atlasRealizesExponents (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res := by
  -- L5: the geometric atlas + its FoldProduced provenance + per-chart terminal PrincipalInv.
  obtain ⟨atlas, hfold, hprin⟩ := leaf_stepInv_of_path d hd hN hpos e he0 he_lin
  -- Per chart: L1 (ideal) then L6 (assemble the certified Chart), matching the atlas's data.
  have hchart : ∀ c : Fin atlas.n, ∃ chart : Chart (coreGen d e) 0,
      chart.g = atlas.gmap c ∧ chart.dom = atlas.dom c ∧ chart.nbhd = atlas.region c ∧
        chart.bexp chart.k₀ = atlas.bexp c ∧ chart.jac = atlas.jac c := by
    intro c
    obtain ⟨q, r, hpt⟩ := hprin c
    obtain ⟨hfwd, hbwd⟩ :=
      principalInv_regionRepresents (coreGen d e) (atlas.gmap c) (monoOf (atlas.bexp c)) q r
        (atlas.region c) hpt
    exact leafPath_chartGeometry d e atlas c hfwd hbwd
  choose charts hg hdom _hnbhd hbexp hjac using hchart
  -- L7: the full cover of a ball by the charts' domain images (rides the FoldProduced provenance).
  obtain ⟨ρ, hρ, hcov⟩ := leafPath_compactCover d e atlas hfold
  -- L8: the exponent match (rides the FoldProduced provenance).
  obtain ⟨hspec_lb, hspec_attain⟩ :=
    leafPath_realizesExponents d hd hN hpos e atlas hfold
  -- assemble the Resolution.
  haveI : Nonempty (Fin atlas.n) := ⟨⟨0, atlas.hn⟩⟩
  refine ⟨⟨atlas.n, charts, Finset.univ_nonempty, Metric.ball 0 ρ, Metric.ball_mem_nhds 0 hρ, ?_⟩,
    ?_, ?_⟩
  · -- hcover: the ball is fully covered by the charts' domain images (empty escape).
    have hsub : Metric.ball (0 : Fin (flatDim d) → ℝ) ρ ⊆ ⋃ c, (charts c).g '' (charts c).dom := by
      refine hcov.trans (Set.iUnion_mono (fun c ↦ ?_))
      rw [hg c, hdom c]
    rw [Set.diff_eq_empty.2 hsub]; exact measure_empty
  · -- AtlasRealizesExponents clause (i): transfer via the chart exponent equalities.
    intro c a ha
    rw [hjac c]
    refine hspec_lb c a ?_
    have : (charts c).bexp (charts c).k₀ = atlas.bexp c := hbexp c
    rwa [this] at ha
  · -- AtlasRealizesExponents clause (ii): transfer via the chart exponent equalities.
    intro l hl k hlk
    obtain ⟨c, a, ha, hval⟩ := hspec_attain l hl k hlk
    refine ⟨c, a, ?_, ?_⟩
    · rw [hbexp c]; exact ha
    · rw [hjac c]; exact hval

/-- **The FULL `exists_coreResolution` statement, re-proved by the monument composition.** Identical
to `LearningCoefficient.exists_coreResolution` but discharged via `exists_atlasRealizesExponents` +
the salvage adapter `exists_hlb_hattain_of_exists_atlasRealizesExponents` (NO `sorry` of its own; the
`sorryAx` cone is exactly the leaf set). No residual-assumption hypotheses: the former D3 named gaps
dissolved (see the L5 note). See the module docstring on the wiring.
`@[blueprint]` — rests on the forecast leaves; strikes to banked when they land. -/
@[blueprint]
theorem exists_coreResolution_via_monument (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (hne : (qipFeasible d).Nonempty)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ res : Resolution (coreGen d e) 0,
      (∀ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
        qipMin d hne ≤ ((res.charts c).jac a + 1 : ℤ)) ∧
      (∃ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
        ((res.charts c).jac a + 1 : ℤ) = qipMin d hne) := by
  refine exists_hlb_hattain_of_exists_atlasRealizesExponents d hd hN hpos hne ?_
  exact exists_atlasRealizesExponents d hd hN hpos e he0 he_lin

end DLNFibre.DLN.Aoyagi

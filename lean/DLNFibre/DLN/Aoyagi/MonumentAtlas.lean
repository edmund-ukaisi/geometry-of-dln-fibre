import DLNFibre.Core.Aoyagi.PrincipalInv
import DLNFibre.Core.Aoyagi.PathAtoms
import DLNFibre.Core.Aoyagi.BlockDivision
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
* `foldNR`/`foldResid` implement the rev-leaves check-#2 EXACT-CLEAR: `root ↦ d_N·d_0`; a step reaching a
  TERMINAL child (`N ≤ nextState.layer`, the oracle's leaf guard) collapses to `foldNR = 1`,
  `foldResid = fun _ ↦ 1` — the M'=1 unit `terminal_bezout` consumes. A NON-terminal step carries the
  residual at full width (`foldResid p ∘ stepMap`, cast by `Fin.cast (if_neg h)`); the per-case ATOM the
  seat fires is selected by the case-aware `stepMapRaw` (case-1(1) sh=id ⇒ `blockBlowup_center_comb_eq`;
  case-1(2)/case-2 ⇒ `weightedCofactor_transport`; rollover = reindex). Total, proof-free, NEVER a
  division / exactness choice (that belongs to the `∃q`). The terminal residual is a CONSTANT (`fun _ ↦ 1`
  ignores the index), so it types at any width with no cast; `foldNR root` is a bare arm so it is
  `d_N·d_0` DEFINITIONALLY. (The per-case count deltas of the earlier stand-in — case-2 `Fin.snoc` +1 —
  are SUBSUMED: the residual is carried full-width until the terminal collapse, a cleaner total model.)
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
  /-- **The shear keeps the pivot coordinate** (elder φ-ruling; the shears' exceptional-coords-untouched
  fact, shear-pin-certified): with `B∘S` (blow-up OUTERMOST) this is what makes the δ=1 strict transform
  well-defined — the pivot coordinate is never written by the shear, so the blow-up's `u_pivot` factor on
  a center coordinate is the only one, and its removal (`blockBlowupCoordQuot`) is exact. Replaces the
  withdrawn `hshear_center`. -/
  hshear_pivot : ∀ v, (blockShear shearφ) v pivot = v pivot
  /-- **The shear is analytic** (seat-w0l3; elder-ratified). The Q/Schur φ is polynomial, so the shear
  is analytic (⟹ continuous). One field, three consumers: δ=0's `q′=q∘σ` continuity, δ=1's
  strict-transform quotient continuity, and L6's `Chart.hg_analytic`. Matches `GeoStep.hσ_an`'s shape. -/
  hshear_analytic : AnalyticOnNhd ℝ shearφ Set.univ

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
* **ROOT CENTER = the LAYER-1 block, NOT `univ`** (anchor (iv), elder): the paper's root step blows up
  the FIRST-layer block only; deeper-layer coordinates are SPECTATORS. Each `coreGen` entry is a
  cross-layer product with EXACTLY ONE layer-1 factor, so it gains `u_pivot`-order exactly 1 ⟹ ONE
  division balances (entries order `d` vs `b'·resid' = u_p·(order d−1) = order d`). `center = univ` is
  correct ONLY when the current layer is the whole space (the `d=(1,2)` instance — why `blowupResolution`
  was right there), NOT for general `d`. At (3,3,4) the root layer-1 block is `d_1·d_0 = 9` coords
  (matches the S=1 codim-9 append), spectators = `d_2·d_1 = 12`. CORRECTION to earlier round-5 prose:
  "`hsupp` forces root center = `univ`" was WRONG — `hsupp` is IDEAL-membership, and `coreGen` entries
  ARE in ⟨layer-1 coords⟩, so the LAYER-1 center discharges `hsupp` at the root. NOTHING here hardcodes
  `center = univ` at the root: `center` is a free `TreeEdge` field and L5's (sorried) root-edge
  construction must set it to the layer-1 block (computed once the RLCT↔Aoyagi bridge lands; documented
  here as the intended value + hand-check meanwhile).

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

/-- The step map on stored edge data: `blockBlowupMap center pivot ∘ edgeShearRaw case φ` — blow-up
OUTERMOST (thread-34's order; elder φ-ruling 2026-07-21). The fold uses this form so the defining
equations hold on the raw `TreePath.step` fields, per-case. -/
def stepMapRaw (d : Fin (N + 1) → ℕ) (cse : StepCase) (center : Finset (Fin (flatDim d)))
    (pivot : Fin (flatDim d)) (shearφ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  blockBlowupMap center pivot ∘ edgeShearRaw d cse shearφ

/-- One step's coordinate change: block-center blow-up ∘ (per-case) shear (blow-up OUTERMOST). Equals
`stepMapRaw d ed.case ed.center ed.pivot ed.shearφ` definitionally. -/
def stepMap (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  blockBlowupMap ed.center ed.pivot ∘ edgeShear d ed

/-- **Def-lemma** — `jacDet (edgeShear d ed) u = 1` (shear-pin): `id` at merge/rollover (`jacDet_id`),
`blockShear` elsewhere (`hshear`). -/
theorem jacDet_edgeShear (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (u : Fin (flatDim d) → ℝ) : jacDet (edgeShear d ed) u = 1 := by
  unfold edgeShear edgeShearRaw
  split <;> first | exact jacDet_id u | exact ed.hshear u

/-- **Def-lemma** — `stepMap d ed 0 = 0` (the step map fixes the origin; blow-up ∘ shear both fix `0`). -/
theorem stepMap_zero (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    stepMap d ed 0 = 0 := by
  change blockBlowupMap ed.center ed.pivot (edgeShear d ed 0) = 0
  rw [show edgeShear d ed 0 = 0 from edgeShearRaw_zero d ed.case ed.shearφ ed.hshear0,
    blockBlowupMap_zero]

/-- **Def-lemma** — `edgeShear d ed` is analytic (`id` at merge/rollover; `blockShear` via
`hshear_analytic`). -/
theorem analyticOnNhd_edgeShear (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    AnalyticOnNhd ℝ (edgeShear d ed) Set.univ := by
  unfold edgeShear edgeShearRaw
  split <;>
    first
      | exact analyticOnNhd_id
      | exact analyticOnNhd_blockShear ed.shearφ ed.hshear_analytic

/-- **Def-lemma** — `stepMap d ed` is analytic (`blockBlowupMap` polynomial ∘ analytic shear, `B∘S`). -/
theorem analyticOnNhd_stepMap (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    AnalyticOnNhd ℝ (stepMap d ed) Set.univ :=
  (analyticOnNhd_blockBlowupMap ed.center ed.pivot).comp (analyticOnNhd_edgeShear d ed)
    (Set.mapsTo_univ _ _)

/-- **Def-lemma** — `stepMap d ed` is continuous (from analytic). Feeds δ=0's `q′=q∘σ` continuity, δ=1's
strict-transform quotient continuity, and L6's `hg_analytic`. -/
theorem continuous_stepMap (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p) :
    Continuous (stepMap d ed) :=
  continuousOn_univ.mp (analyticOnNhd_stepMap d ed).continuousOn

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

/-- The residual family length along a path (rev-leaves check-#2 EXACT-CLEAR). `root ↦ d_N·d_0`; a step
reaching a TERMINAL child (`N ≤ nextState.layer`, the oracle's leaf guard) collapses to `1` — the
M'=1 unit `terminal_bezout` consumes (`StepInv … (fun _ : Fin 1 ↦ 1) …`); a non-terminal step carries
the residual at full width (the pullback, progressively absorbed into `foldB`). Root is a bare arm so
`foldNR root = d_N·d_0` DEFINITIONALLY (root non-vacuity `q = Kronecker` still elaborates). -/
def foldNR (d : Fin (N + 1) → ℕ) : TreePath d → ℕ
  | .root => d (Fin.last N) * d 0
  | .step p _ _ _ nextState _ => if N ≤ nextState.layer then 1 else foldNR d p

/-- The residual family along a path (rev-leaves check-#2 EXACT-CLEAR + FIX-RESID δ=1 strict transform).
`root ↦ coreGen d e`; a TERMINAL-reaching step (`N ≤ nextState.layer`) collapses to the M'=1 unit
`fun _ ↦ 1`. A NON-terminal step: at **δ=0** (`¬ edgeδ`) the pure pullback `foldResid p ∘ stepMap`
(b' carries no `u_pivot`, order balances); at **δ=1** (`edgeδ`) the STRICT TRANSFORM — the blow-up
substitution's `u_pivot` factor is removed via `BlockDivision.blockBlowupCoordQuot` (pivot→1, other
center coords→their value), applied to the SHEARED point (blow-up is outermost, `B∘S`), so
`b'·resid' = u_pivot¹·(…) = entry` and the child quotient law is `q' = q ∘ σ` — NO division on the
witness (the codex `u₀ = q'·u₀²` witness dies: `resid = v_pivot ⟹ strict = 1`).

**DESIGN-GUARD AMENDED (elder, verbatim):** "division-by-monomial in a def is banned; the total
closed-form quotient of a center coordinate under its own blow-up is data." (`blockBlowupCoordQuot` is
that datum: for `j ∈ center\{p}` the strict transform is `v_j`, for `j = p` it is `1`.)

**Thread-34 addendum:** thread-34's certificate bookkept the division on the q-side; mathematically
equivalent — the elder corrects it to the resid-side because the data/proof split demands it.

**ELDER RULING (A′), degree-1 obligation:** this substitution form equals the factored strict transform
exactly under center-degree-1 (each residual entry = a single center coordinate × a center-disjoint tail
— the "v_j / 1" regime). The elder RULED (A′): the substitution STANDS; **degree-1-preservation =
the re-factoring content of L3/L4, not an additional frontier item** (the child re-factors in the child
center — the proof content moves nowhere, only the accounting of where it lives moves). Structural
soundness: `foldResid` is total on `TreePath` and every `TreePath` is a real path (built from the
construction), so there are NO expressible unreachable degree-≥2 states to junk on. Anchor (v) verifies
the discharge: the case11 re-factoring check at (3,3,4), reconciled by seat-L4's wire-up recipe when the
wall lands. (The alternative (A″) — a `foldResid` representation carrying `(center-factor, tail)` — was
NOT taken; no representation redesign.) -/
noncomputable def foldResid (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    (p : TreePath d) → (Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ)
  | .root => coreGen d e
  | .step p center pivot cse nextState shearφ =>
      if h : N ≤ nextState.layer then
        fun _ => 1
      else
        fun j u =>
          if edgeδ d p then
            -- δ=1 STRICT TRANSFORM: remove the blow-up's `u_pivot` via `blockBlowupCoordQuot` (data).
            foldResid d e p (Fin.cast (if_neg h) j)
              (fun k => blockBlowupCoordQuot pivot k (edgeShearRaw d cse shearφ u))
          else
            -- δ=0: pure pullback (order balances; no `u_pivot` in b').
            foldResid d e p (Fin.cast (if_neg h) j) (stepMapRaw d cse center pivot shearφ u)

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

/-- **The foldState step invariant at a path node, PARAMETRIC in the center `C`** (elder re-statement —
THE FIX for the fidelity defect). Two conjuncts: (1) a divisibility witness `q` for the accumulated
`StepInv (coreGen) (foldG p) (foldB p) (foldResid p) q (foldRegion p)`; (2) the residual is CENTER-EXACT
degree-1 supported on `C` — `Deg1SupportedOn (foldResid p) C (foldRegion p)`. Conjunct (2) is exactly
what the δ=1 `blockBlowupCoordQuot` strict transform needs (each residual monomial carries EXACTLY one
center factor) and what the old ideal-membership `hsupp` FAILED to force — `SupportedOn` is monotone in
the center, so it admitted the over-large `d=![1,2,1]`, `center={0,1,2}` witness where the substitution
over-divides and the leaf is false. Carried through the fold, not re-established per-node. -/
def FoldStepInvAt {N : ℕ} (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (C : Finset (Fin (flatDim d))) (p : TreePath d) : Prop :=
  (∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ,
    StepInv (coreGen d e) (foldG d e p) (foldB d e p) (foldResid d e p) q (foldRegion d e p)) ∧
    Deg1SupportedOn (foldResid d e p) C (foldRegion d e p)

/-- **The foldState step invariant** — `∃ C, FoldStepInvAt C p`. Shape → assumed delivery → stated
obligation: this is the third and final form of the same content — degree-1 was never optional
bookkeeping; it was the invariant the paper's inductive statement carried all along (the residual IS
the block matrix). -/
def FoldStepInv {N : ℕ} (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) : Prop :=
  ∃ C : Finset (Fin (flatDim d)), FoldStepInvAt d e C p

/-! ### The fold-realization predicate — combinatorial branch-membership (FIX 2; elder/coordinator (a))

`FoldRealizes` is the SECOND provenance predicate L5 emits (beside `FoldProduced`): each chart's map
`gmap c` IS the accumulated coordinate change `foldG` along a REAL root→leaf branch of
`buildTree d (conOracle d) conRoot`, and that branch reaches the chart's leaf. "Real branch" is
COMBINATORIAL: each step's `(case, nextState)` is realised by SOME oracle `StepChild` at the parent
node's state (`ecase`/`child` matched; the child's `esubst` = `runLen`/`mergeIdx` rides along as the
witness), and the terminal state emits the leaf. It reads NO `center`/`pivot`/`shearφ` — the oracle
emits none (`ConState` is combinatorial; `StepChild.esubst.localSub = id` placeholder).

**Severance taxonomy — four free-field axes, one exemplar each** (elder guardrail, the L3/L4 note): a
free field on a quantified structure is a severance axis, so the audit is per-FIELD.
* CONTENT — the constant / `Σw²` spectator-support residuals — dies by the `foldResid p` pin (no free
  residual to instantiate).
* SIZE — the `|S|=1`, `sh=id` lazy witness — dies by the same pin.
* PATH — the `n` charts all sharing ONE tree branch (the all-charts-one-path collision) — dies HERE:
  distinct leaves force distinct combinatorial branches, so a surjective `leafOf` (`FoldProduced`) plus
  `reachesLeaf` forbids the collision.
* COORDINATE — every chart blowing up the SAME coordinate `x`, so all `gmap` images concentrate on `x`
  and the ball's `y`-directions stay uncovered — is NOT killed here: `reachesLeaf` is combinatorial and
  `foldG` reads the unpinned `center`/`pivot`/`shearφ`, while `FoldProduced` stays ℕ-valued `divExp`,
  never `divCoord`. This is L7's bridge-gated coordinate-coverage residual (see `leafPath_compactCover`).
-/

/-- The construction decision at a state terminates emitting leaf `l` (combinatorial leaf-match). -/
def decisionEmitsLeaf {L : ℕ} {M : Fin (L + 1) → ℕ} {s : ConState L} :
    ConDecision M s → LeafData M → Prop
  | .terminal l' _, l => l' = l
  | .step _ _ _ _ _, _ => False

/-- **A real root→node branch of `buildTree d (conOracle d) conRoot`** — COMBINATORIAL: each step's
`(case, nextState)` is one of the oracle's `stepChildren` at the parent node's state (`ecase`/`child`
matched; the matched child's `esubst` = `runLen`/`mergeIdx` is the witness). Reads NO
`center`/`pivot`/`shearφ` (the oracle emits none). -/
def TreePath.IsRealBranch {N : ℕ} {d : Fin (N + 1) → ℕ} : TreePath d → Prop
  | .root => True
  | .step p _ _ cse nextState _ =>
      p.IsRealBranch ∧
        ∃ sc ∈ (conOracle d p.conState).stepChildren, sc.ecase = cse ∧ sc.child = nextState

/-- **The path reaches the leaf** — a real branch whose terminal state emits `l`. Ties chart `c`'s fold
to the tree leaf its branch reaches; the coordinate-level coverage this would give L7 is bridge-gated. -/
def TreePath.reachesLeaf {N : ℕ} {d : Fin (N + 1) → ℕ} (p : TreePath d) (l : LeafData d) : Prop :=
  p.IsRealBranch ∧ decisionEmitsLeaf (conOracle d p.conState) l

/-- **The fold-realization provenance** (L5's second record, beside `FoldProduced`): each chart's map is
the accumulated `foldG` of a real tree branch (`reachesLeaf`) reaching a leaf, and every tree leaf is
reached by some chart (`leafOf` SURJECTIVE). Self-contained (its own `pathOf`/`leafOf`) so it threads as
the single conjunction `FoldProduced ∧ FoldRealizes` without re-opening the elder-locked `FoldProduced`.

The SURJECTIVITY conjunct is what makes `reachesLeaf` kill the all-charts-one-path (PATH-axis) severance:
a collision atlas (all charts sharing one branch `p₀`) forces `leafOf` CONSTANT (`reachesLeaf p₀ l ⟺
l = ` the unique leaf `p₀` reaches), which is not surjective once the tree branches. WITHOUT the
conjunct the collision survives — `FoldProduced` sees only leaves, never paths, so a decoupled `leafOf`
could be surjective there yet constant here (fidelity fix, rung C FIX 2; flagged to arch-C for the bake).
The all-charts-one-coordinate (COORDINATE-axis) severance is NOT killed — it uses distinct real branches
(surjective) all blowing up one coordinate; that is L7's bridge-gated residual (taxonomy note above and
`leafPath_compactCover`). -/
def FoldRealizes {N : ℕ} (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (atlas : GeoAtlasData d e) : Prop :=
  ∃ (pathOf : Fin atlas.n → TreePath d) (leafOf : Fin atlas.n → LeafData d),
    (∀ c : Fin atlas.n,
      atlas.gmap c = foldG d e (pathOf c) ∧ (pathOf c).reachesLeaf (leafOf c)) ∧
    (∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
      ∃ c, leafOf c = l)

/-! ## L3 / L4 — the foldState one-step preservations (DLN-side; elder-locked round-5)

The free-standing `∀-(state, spec)` form was not honest (`Core.PrincipalInv` closing principle). Three
of its four refutations (constant, Σw², `|S|=1` on the STATE axis) die BY DEFINITION in the foldState
form (there is no free state or residual to instantiate; the state IS `foldG`/`foldB`/`foldResid p`).
The FOURTH — the CENTER-axis severance — is the one that bit: `ed.center` is a FREE `TreeEdge` field, so
the leaf `∀`-ranges over ALL centers, and the round-5 `hsupp = SupportedOn` (ideal membership) is
MONOTONE in the center, admitting over-large ones for which the δ=1 substitution over-divides — the
CONFIRMED fidelity defect (rev-rungc-fidelity 2026-07-21; machine-checked witness in the L4 docstring).
It is FIXED by the elder re-statement: the leaves carry `FoldStepInvAt ed.center p`, whose
`Deg1SupportedOn` conjunct forces the residual center-EXACT degree-1 (each monomial has EXACTLY one
center factor). That EXCLUDES the bad `{0,1,2}` and admits the construction's layer center, so the δ=1
`blockBlowupCoordQuot` substitution equals the strict transform. Degree-1 is a CARRIED invariant (a
`FoldStepInvAt` conjunct each leaf preserves), NOT deferrable proof content — the (A′) "no-obligation"
framing was falsified and retired.

**GUARDRAIL (elder, per the defect):** every free field on a quantified structure is its own severance
axis — the audit is per-FIELD, never per-statement. (`ed.center` free ⟹ the center severance, fixed by
`Deg1SupportedOn`; the analogous `GeoAtlasData.jac` free field is the L6/L7 provenance severance,
carried by `FoldProduced`.)

Each leaf is the one-step `FoldStepInv d e p → FoldStepInv d e (p.extend ed)`, indexed by the
path node and one outgoing edge; `δ = [J=0]` off `p.conState.cleared` (`edgeδ`, UNIFORM across
sub-cases). Rollover is off the `isCase2`/`isCase1` filters by construction (`localSub = id`).

**EXACT-CLEAR (rev-leaves check-#2).** `foldResid (p.extend ed)` dispatches on the terminal guard
`N ≤ ed.nextState.layer`: a TERMINAL-reaching step collapses to the M'=1 unit `fun _ ↦ 1`, else the
full-width pullback. For a REALIZED case-1/case-2 edge the child keeps `layer < N` (only rollover
advances to `N`), so the terminal branch is vacuous and the proof uses the pullback branch; but `ed`
is quantified freely, so the proof must still discharge the guard (`if_neg` from `¬(N ≤ nextState.layer)`,
or the trivial unit branch). The earlier `Fin.snoc` case-2 append is subsumed — full-width until the
terminal collapse. -/

/-- **L3 — a case-2 edge preserves the foldState invariant** (full-block append regime). The
false-as-stated `hsupp` (ideal-membership, monotone in the center) is RETIRED; the fidelity fix is the
carried `FoldStepInvAt ed.center p` hypothesis — its `Deg1SupportedOn` conjunct forces the residual to
be center-EXACT degree-1 at the edge's own center, excluding the over-large centers that refuted the
prior statement. The child re-factors in the child center `C'` (the wall's re-factoring content). WEAKEST
HYPOTHESES (elder trim): NO `he0`/`he_lin` — the child's S3 vanishing is inherited from `hinv` via
`stepMap_zero`, the step divisibility is pullback-structural, and the degree-1 support is CONSUMED (not
proved) from `hinv` (root-anchored linearity stays on L5). -/
@[blueprint]
theorem case2_preserves_stepInv
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase2 : ed.isCase2)
    (hinv : FoldStepInvAt d e ed.center p) :
    ∃ C' : Finset (Fin (flatDim d)), FoldStepInvAt d e C' (p.extend ed) := by
  -- map: B-L3-case2-preserves-stepInv (foldState; block-center append, δ off the state; Deg1 carries center)
  sorry

/-- **L4 — a case-1 edge preserves the foldState invariant. ⟨THE WALL⟩** The coupled block-center
divisibility at corank ≥ 2 with the exact `u_p^δ` factor; seat-L4's `BlockDivision` core (exact
division; the `2u₀u₂` shear-rescue) supplies the proof. The fidelity fix (elder re-statement): the
carried `FoldStepInvAt ed.center p` — its `Deg1SupportedOn` conjunct forces the residual center-EXACT
degree-1, so the δ=1 `blockBlowupCoordQuot` substitution EQUALS the strict transform (each monomial has
exactly one center factor); the child re-factors in the child center `C'`. ONE center, the merge/split
pivots handled inside the fold — no free `∀`-branch, no `p_merge`/`p_split`. NB `CenterCoordAligned` is
NOT the division mechanism (injectivity ≠ divisibility; seat-L4 `shear_gap.lean`) — it stays a
geometry/injectivity field for L6/L7. WEAKEST HYPOTHESES: NO `he0`/`he_lin`.

**Fidelity history (why the statement changed; rev-rungc-fidelity 2026-07-21).** The earlier
`hsupp = SupportedOn` (ideal membership) was FALSE-AS-STATED: ideal membership is MONOTONE in the center,
admitting the over-large `d=![1,2,1]`, `center={0,1,2}` witness (`coreGen 0 = u₀u₂+u₁u₃`; at
`u=(2,1,1,-1)` the pullback is `2` while `b'·resid'=0`) where the `blockBlowupCoordQuot` substitution
over-divides (it removes the pivot ONCE, exact only at center-degree-1). Degree-1 was a MISSING
HYPOTHESIS, now supplied structurally by `Deg1SupportedOn` in `FoldStepInvAt` — which the layer-1 center
`{0,1}` satisfies and the bad `{0,1,2}` does not. The prior (A′) "no additional obligation" framing was
RETRACTED/falsified (a deferrable obligation must be true-but-unproven; that leaf was false). This is the
honest re-statement; L5 supplies only layer centers, so the composition intent survives. -/
@[blueprint]
theorem case1_preserves_stepInv
    {N : ℕ} (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase1 : ed.isCase1)
    (hinv : FoldStepInvAt d e ed.center p) :
    ∃ C' : Finset (Fin (flatDim d)), FoldStepInvAt d e C' (p.extend ed) := by
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
pivots = the leaf's `divCoord`, doms nontrivial), cheap since L5 builds exactly that — (a′) satisfies
`FoldRealizes` (each chart's map is the accumulated `foldG` of its REAL tree branch reaching its leaf —
combinatorial branch-membership; the coordinate-level coverage L7 would take from it is bridge-gated) —
and (b) carries the terminal `PrincipalInv` for each chart's path map on its region.

Hypotheses = the three one-step obligations (L3/L4/`terminal_bezout`) ONLY (the two former D3 gaps
dissolved — see the section note). **Region-shrink ordering (elder D2', the no-implicit-shrinking
discipline at assembly):** `terminal_bezout` legitimately SHRINKS each chart's region to
`V ∩ {q i₀ ≠ 0}`, so the fold must choose each chart's compact `dom` / open `region` AFTER all
per-step and terminal shrinkings — the emitted `atlas.dom c ⊆ atlas.region c` (a `GeoAtlasData` field)
sits inside the FINAL shrunken region, never a pre-shrink one. The `srcBox`-seam pathwise coherence
(module docstring) is the decorrelated-check gate riding the `CenterCoordAligned` fields. -/
@[blueprint]
theorem leaf_stepInv_of_path (d : Fin (N + 1) → ℕ) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0)
    (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ atlas : GeoAtlasData d e, FoldProduced d e atlas ∧ FoldRealizes d e atlas ∧
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
    (atlas : GeoAtlasData d e) (c : Fin atlas.n) (hfold : FoldProduced d e atlas)
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
idiom, the `S = univ` single-level instance of the block cover).

**BRIDGE-GATED (FIX 2, elder/coordinator (a)).** The FULL cover above is a COORDINATE-level fact —
WHICH coordinate each chart blows up — that neither `FoldProduced` (ℕ-valued `divExp`, never `divCoord`)
nor the COMBINATORIAL `FoldRealizes`/`reachesLeaf` (`hreal`; `center`/`pivot`/`shearφ` unread) pins. The
all-charts-one-coordinate atlas (every `gmap c` concentrated on a single coordinate `x`, the ball's
`y`-directions uncovered) passes BOTH hypotheses yet falsifies this `⋃`. So L7 is HONEST
FALSE-AS-STATED-PENDING-BRIDGE: it closes once the Engine↔Aoyagi coordinate bridge (`edgeCenter`,
deferred; the center/pivot spec §) lands and pins each real branch's blow-up coordinate to the leaf's
`divCoord`.
* The (c)-road — `canonCenter`, the paper's DLN-side slot bookkeeping computed from `(S, J, mergeIdx, d)`
  (NOT the engine `divCoord`) — had its rollover slot-transfer checkpoint return STABLE, so it is the
  SCHEDULED follow-round; the gate lifts bridge-free there (not this bake), pinning each real branch's
  blow-up coordinate without the Engine↔Aoyagi bridge.
* Nothing about L7 blocks the wall (L4), L3, L5's proof-content, L6, or L8 — this banner is the
  coordinate-coverage residual ONLY; do not over-read it. -/
@[blueprint]
theorem leafPath_compactCover (d : Fin (N + 1) → ℕ) (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (atlas : GeoAtlasData d e) (hfold : FoldProduced d e atlas) (hreal : FoldRealizes d e atlas) :
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
theorem leafPath_realizesExponents (d : Fin (N + 1) → ℕ) (hN : 0 < N)
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
theorem exists_atlasRealizesExponents (d : Fin (N + 1) → ℕ) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res := by
  -- L5: the geometric atlas + its FoldProduced + FoldRealizes provenance + per-chart terminal PrincipalInv.
  obtain ⟨atlas, hfold, hreal, hprin⟩ := leaf_stepInv_of_path d hN hpos e he0 he_lin
  -- Per chart: L1 (ideal) then L6 (assemble the certified Chart), matching the atlas's data.
  have hchart : ∀ c : Fin atlas.n, ∃ chart : Chart (coreGen d e) 0,
      chart.g = atlas.gmap c ∧ chart.dom = atlas.dom c ∧ chart.nbhd = atlas.region c ∧
        chart.bexp chart.k₀ = atlas.bexp c ∧ chart.jac = atlas.jac c := by
    intro c
    obtain ⟨q, r, hpt⟩ := hprin c
    obtain ⟨hfwd, hbwd⟩ :=
      principalInv_regionRepresents (coreGen d e) (atlas.gmap c) (monoOf (atlas.bexp c)) q r
        (atlas.region c) hpt
    exact leafPath_chartGeometry d e atlas c hfold hfwd hbwd
  choose charts hg hdom _hnbhd hbexp hjac using hchart
  -- L7: the full cover of a ball by the charts' domain images (rides FoldProduced + FoldRealizes;
  --      the coordinate-level coverage is bridge-gated — see the L7 banner).
  obtain ⟨ρ, hρ, hcov⟩ := leafPath_compactCover d e atlas hfold hreal
  -- L8: the exponent match (rides the FoldProduced provenance).
  obtain ⟨hspec_lb, hspec_attain⟩ :=
    leafPath_realizesExponents d hN hpos e atlas hfold
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
  exact exists_atlasRealizesExponents d hN hpos e he0 he_lin

end DLNFibre.DLN.Aoyagi

# GeoChart + geometricLeafPaths — provisional design note (coverage, post-gate9)

*Author: `coverage-t08`. Pins the GeoChart type shape + the edge-driven `geometricLeafPaths` skeleton.
**FIELD-LOCKED (2026-07-19) against architect-t06's first carrier green** — `qOfCenter` clean-three,
the four seam questions answered (below). Lean build starts at t06's `qEdgeOf` wrapper green (its
`divBirthCoord` ripple + wrapper are in flight). Binding rulings: elder-gate9 (amendments 1 per-edge
emission, 2 buck-stops, 3 uniform-u) + the ownership addendum (I CONSUME the carrier defs, t06 builds).*

## 0. The seam — LOCKED against t06's carrier (what I consume)

From `CenterIndices.lean` (merged) + t06's carrier (`qOfCenter` green; `divBirthCoord` + `qEdgeOf` in flight):
- `flatCoordOf M s i j : Fin (flatDim M)` — the `(i,j)` entry of the `s`-th matrix as a flat index (inj).
- `resBlockCenterIndices M s J rows cols _ _ : Fin (rows*cols) → Fin (flatDim M)` — residual sub-block,
  flattened, injective.
- `qOfCenter M (c : Fin d → Fin (flatDim M)) (hinj) : Params M ≃ₜ (Fin d → ℝ) × (Fin (flatDim M − d) → ℝ)`
  — **PARAMETRIC in the center selector `c`** (Q1); node/edge enters ONLY through `c`. Its `Fin d` is the
  **PER-EDGE** count (Q4), so my `β_e`'s `pivotChart` index matches the `Fin d` factor DIRECTLY — no
  node-sum slicing.
- `qEdgeOf (node) (e) : Params M ≃ₜ (Fin (dCenterOfEdge node e) → ℝ) × …` — t06's thin per-edge wrapper
  computing `c` (resBlock for case-2/case-1(2); the birth-corner singleton for case-1(1)). **My
  `geoChartMap` calls `qEdgeOf`** (edge-keyed).
- `StepData.divBirthCoord : Fin numDiv → ℕ × ℕ` (Q2) — the immutable birth `(layer, cleared)` per divisor
  (flat slot `= flatCoordOf M s ⟨J⟩ ⟨J⟩`, slot-stable). Case-1(1) u-coord = `node.divBirthCoord mergeIdx`
  (via the wrapper).
- `dCenterOfEdge (node) (e) : ℕ` (Q3) — CONSUME t06's helper (don't inline the counts).

## 1. Amendment 1 — per-edge emission (the enumeration structure, t05-independent)

The pivot family PARTITIONS across a case-1 node's TWO edges. Per-edge center-dimension:

    dCenterOfEdge (n : StepData M) (e : Edge M) : ℕ :=
      match e.case with
      | .case11   => 1                       -- the u-pivot (one chart)
      | .case12   => e.subst.runLen * n.resCols   -- the d-family (NOT resRows)
      | .case2    => n.resRows * n.resCols
      | .rollover => 0                       -- chartless

Node `d_center = Σ over its edges` (case-1 node: `1 + runLen·resCols` = page-pin's `J₁(M^{S+1}−J)+1`).
NEVER emit the node total on the case-1(2) edge (u double-count — the off-by-one class the gate named).
This is fully pinned + t05-independent; it is the count the `geometricLeafPaths` fan-out uses.

## 2. GeoChart — the type shape (amendment 2: buck-stops, NO free geometry)

GeoChart is the per-(edge, pivot-choice) RECIPE — node-derived DATA only; the chartMap/`β̃` is COMPUTED
(never a stored free field, else a fabricated atlas satisfies (D) internally — obligation-instance-#5
class). LOCKED fields (edge-keyed, per t06's `qEdgeOf`):

    structure GeoChart (M) where
      node  : StepData M   -- the parent blow-up node (passed to qEdgeOf + divBirthCoord)
      edge  : Edge M       -- the edge (its .case/.subst fix the family + count; qEdgeOf is keyed on it)
      pivot : ℕ            -- the pivot choice within this edge's family (< dCenterOfEdge node edge)
      -- NO chartMap / β̃ field — computed by `geoChartMap` below from node/edge/pivot + banked atoms.

`geoChartMap (g : GeoChart M) : Params M → Params M` (the COMPUTED geometry, a function of `g`'s data
+ `qEdgeOf` + banked atoms — the fails-on-fake teeth):

    let q  := qEdgeOf g.node g.edge               -- t06's edge-keyed Homeomorph; its Fin d = PER-EDGE count
    let p  : Fin (dCenterOfEdge g.node g.edge) := ⟨g.pivot, _⟩   -- pivot index MATCHES q's Fin d directly (Q4)
    let β  := fun w => q.symm (Prod.map (pivotChart p) id (q w))   -- banked PivotCover atom, q-conjugated
    let α  := elemShearHomeomorph (schur indices)  -- banked ShearReconcile atom (α_u = .refl on case11)
    β ∘ α.symm                                     -- = β̃ = β ∘ α_e⁻¹ (R-b source reparam)

`α_u = .refl` (case11) is a field VALUE (amendment 3), not a type split. Schur `(a,b,c)` for case12/case2
are read from the residual block coords (`qEdgeOf` computes `c` via `resBlockCenterIndices`). The case11
u-coord = `g.node.divBirthCoord g.edge.subst.mergeIdx` → `flatCoordOf` at the birth corner (slot-stable;
`qEdgeOf` handles this internally, so `geoChartMap` reads it uniformly).

## 3. geometricLeafPaths — edge-driven skeleton (amendment 1)

Mirror `edgesLeafPaths` (the banked `leafPaths` companion) but fan out per edge over its pivot family:

    geometricLeafPaths (acc) : ResolutionTree M → List (GeoChart-path)
      | leaf l      => [(l, acc)]
      | branch n es => geomEdges acc n es
    geomEdges (acc) (n) : List (Edge M) → List (…)
      | []            => []
      | (mk c s ch)::es =>
          -- fan out: one geometric chart per pivot in this edge's family
          (List.finRange (dCenterOfEdge n ⟨c,s,ch⟩)).flatMap (fun p =>
             geometricLeafPaths (acc ∘ geoChartMap ⟨n, ⟨c,s,ch⟩, p⟩) ch)
          ++ geomEdges acc n es

The fold is a function of `t` alone (buck-stops): `acc` threads `geoChartMap` (computed), never a free
map. The atlas = `geometricLeafPaths id t` materialized as `List (LeafData M)` (each with its computed
`chartMap`, `srcBox = qNodeOf-preimage of the pivot sub-cube`, `divCoord` from `centerIndices`, `divExp`
from the fold). This is the flat virtual-leaf atlas the corrected `ChartBridge` quantifies over.

## 4. How the ChartBridge clauses discharge over this atlas

- **(A) cover:** the pure `node_pivotCover_of_atom` per node (R-b: `β̃_e '' (α_e '' D_e) = β_e '' D_e`
  by `reparam_image` — the domain-reparam identity BANKED; so the gauge doesn't move the covering set and
  the pure atom tiles), folded up the geometric tree via `ownCovers_branch`.
- **(B) 3 Props per piece:** a.e.-InjOn (`pivotChart_ae_injOn` ∘ α homeo ∘ q); LeafJacobian
  (`|det Dβ̃| = |det Dβ| = ∏|u|^{divExp−1}` — BOTH inputs BANKED: `abs_det_fderiv_pivotChart` +
  `abs_det_fderiv_elemShear` `|det Dα|=1`); LeafPullback (o5 analytic side).
- **(C) exponent-agreement:** each geometric chart's `divExp` = its ledger leaf's (chart-independent
  bump), so `∈ terminalExponents t`.
- **(D) fidelity:** `∀ c ∈ atlas, ∃ p ∈ geometricLeafPaths id t, c.chartMap = geoChartMap-fold p` —
  provable over the constructed atlas, FALSE on a generic one (the fold is a function of `t`; a
  free chartMap can't equal any `geoChartMap` composite). Buck-stops teeth satisfied.

## 5. Status — banked NOW vs seam-gated on `qEdgeOf`

- BANKED (green, clean-three, ShearReconcile): α_e frame (`elemShearHomeomorph` + `abs_det_fderiv_elemShear`,
  `|det Dα|=1`) + `reparam_image` (domain-reparam identity) + `abs_det_fderiv_pivotChart` (β-det,
  `|u_i|^{d−1}`). Both `LeafJacobian` det inputs in hand: `|det Dβ̃| = |det Dβ| = |u_i|^{d−1}`.
- SEAM-GATED (build starts at t06's `qEdgeOf` green): `geoChartMap` (consumes `qEdgeOf`),
  `geometricLeafPaths` materialization, the cover fold, clauses (A)/(C)/(D), the 3 Props. Fields LOCKED
  above against t06's `qOfCenter`/`qEdgeOf` signature.

## 6. Pins — RESOLVED at field-lock

- **u-coord: RESOLVED** — slot-stable (`cert-slot-stability`); the case11 u-coord = `divBirthCoord` at the
  birth corner, handled INSIDE t06's `qEdgeOf`; `geoChartMap` reads it uniformly (amendment 3). Coherence
  bonus: case-1(2)'s rescale-rename-in-place = my R-b `α_d` at the value level — cite in the (D)/fold docstrings.
- **GeoChart field granularity: LOCKED** — `node : StepData M` + `edge : Edge M` + `pivot : ℕ`; `qEdgeOf`
  is keyed on `(node, edge)` (Q1), so no free geometry, buck-stops teeth intact.
- **The two fill-batch retirement flags** (task #15): PivotCoverFold's spine-fold + EngineObligations:40-49
  caveat retire when this atlas fill lands (they describe the struck id-edge spine plan → vacuous).

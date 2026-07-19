# GeoChart + geometricLeafPaths — provisional design note (coverage, post-gate9)

*Author: `coverage-t08`. Pins the GeoChart type shape + the edge-driven `geometricLeafPaths` skeleton
PROVISIONALLY against t05's `carrier-remainder-spec.md` (d5f1f89c2) — so the carrier executor's `qNodeOf`
green drops straight into the coverage build. NOT Lean yet (Lean against a not-yet-real `qNodeOf` risks
rework; team-lead-approved to design-note it first). Final lock at the executor's first green.
Binding rulings: elder-gate9 (amendments 1 per-edge emission, 2 buck-stops, 3 uniform-u) + the ownership
addendum (I CONSUME `qNodeOf`, t05/t07 build it).*

## 0. The seam (what I consume)

From `CenterIndices.lean` (merged, clean-three) + the carrier remainder (t07 builds):
- `flatCoordOf M s i j : Fin (flatDim M)` — the `(i,j)` entry of the `s`-th matrix as a flat index (inj).
- `resBlockCenterIndices M s J rows cols _ _ : Fin (rows*cols) → Fin (flatDim M)` — residual sub-block,
  flattened, injective.
- `qNodeOf (node) : Params M ≃ₜ (Fin d_center → ℝ) × (Fin (flatDim M − d_center) → ℝ)` — node-indexed
  (seam pin: node-derived, never existential), assembled `paramsEquivFlatCLE.toHomeomorph` ∘ permutation
  (from `centerIndices` range+complement) ∘ `arrowCongr` split.

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
class). Provisional fields:

    structure GeoChart (M) where
      node    : StepData M          -- the parent blow-up node (source of qNodeOf + counts)
      case    : StepCase            -- which edge kind (fixes the family + exponent)
      subst   : ChartSubst M        -- the edge's subst (runLen for the case12 count)
      pivot   : ℕ                   -- the pivot choice within this edge's family (< dCenterOfEdge)
      -- NO chartMap / β̃ field — computed by `geoChartMap` below from node + pivot + banked atoms.

`geoChartMap (g : GeoChart M) : Params M → Params M` (the COMPUTED geometry, a function of `g`'s data
+ `qNodeOf` + banked atoms — the fails-on-fake teeth):

    let q  := qNodeOf g.node                      -- t05/t07's node-indexed Homeomorph
    let p  : Fin d_center_edge := ⟨g.pivot, _⟩    -- the pivot index (bounded by dCenterOfEdge)
    let β  := fun w => q.symm (Prod.map (pivotChart p) id (q w))   -- banked PivotCover atom, q-conjugated
    let α  := elemShearHomeomorph (schur indices from CenterIndices)  -- banked ShearReconcile atom (α_u = .refl)
    β ∘ α.symm                                     -- = β̃ = β ∘ α_e⁻¹ (R-b source reparam)

α_u = .refl (case11) is a field VALUE (amendment 3), not a type split; the Schur `(a,b,c)` for case12/case2
are read from `resBlockCenterIndices` (which flat coords the block occupies). The u-coord (case11) is the
single center index from §2 of the spec (pnp-slot verdict: `flatCoordOf` at the birth corner if slot-stable).

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
             geometricLeafPaths (acc ∘ geoChartMap ⟨n, c, s, p⟩) ch)
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
  (`|det Dβ̃| = |det Dβ| = ∏|u|^{divExp−1}` — needs the pivotChart det atom [IN PROGRESS] + `|det Dα|=1`
  BANKED `abs_det_fderiv_elemShear`); LeafPullback (o5 analytic side).
- **(C) exponent-agreement:** each geometric chart's `divExp` = its ledger leaf's (chart-independent
  bump), so `∈ terminalExponents t`.
- **(D) fidelity:** `∀ c ∈ atlas, ∃ p ∈ geometricLeafPaths id t, c.chartMap = geoChartMap-fold p` —
  provable over the constructed atlas, FALSE on a generic one (the fold is a function of `t`; a
  free chartMap can't equal any `geoChartMap` composite). Buck-stops teeth satisfied.

## 5. What's t05/t07-independent (buildable NOW) vs seam-gated

- NOW (banked or in progress): α_e frames + `reparam_image` (BANKED, ShearReconcile); the pivotChart det
  atom (IN PROGRESS); `dCenterOfEdge` counts (§1, pinned).
- SEAM-GATED (at `qNodeOf` green): `geoChartMap` (consumes `qNodeOf`), `geometricLeafPaths` materialization,
  the cover fold over the geometric tree, clauses (A)/(C)/(D), the 3 Props. Provisional GeoChart fields
  above lock against t05's `qNodeOf` signature; FINAL lock at the executor's first green.

## 6. Open pins (resolve at seam)

- **u-coord (pnp-slot):** case11's single center index — `flatCoordOf` at the birth corner IF slot-stable;
  else a dynamic map (surfaces to controller). GeoChart's case11 `pivot`/index carries whatever pnp-slot
  sizes; my `geoChartMap` reads it uniformly (amendment 3).
- **GeoChart field granularity:** whether `node`/`subst` are stored or the chart is indexed by a tree
  position — settle with t07 to match `qNodeOf`'s exact argument (StepData vs a node handle).
- **The two fill-batch retirement flags** (task #15): PivotCoverFold's spine-fold + EngineObligations:40-49
  caveat retire when this atlas fill lands (they describe the struck id-edge spine plan → vacuous).

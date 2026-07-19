# Carrier interface proposal — the q / t_geo / R-b source-reparam surface

*Author: `coverage-t08`. The carrier trigger t05 is warm on: the SURFACE the construction must expose so
coverage discharges clause (D) [fidelity], clause (A) [cover], and clause (B) [3 fed Props] over the flat
virtual-leaf atlas (`ChartBridge`, `EngineDefs.lean:75`). Grounded in: the ψ adjudication
`threads/15-psi-adjudication/cert-psi-mix.md` (route = R-b, decisive), the tick-163 4-part carrier spec
(REVISED here: field (3) target-ψ → source-α), and the live tree at HEAD `d514c6a85`. This is a PROPOSAL
for t05 + the elder; no Lean re-typed. Division of labour at the end.*

## 0. Why this shape (the settled inputs)

- The atlas is a flat `List (LeafData M)` of geometric chart pieces; each piece's `chartMap` is a
  root→leaf fold of per-edge `localSub`s (`ChartSubst.localSub`, `ResolutionTree.lean:67`). Currently
  `leafOfState.chartMap = id` (placeholder, `EngineConstruction.lean:1766`) and the edges carry no real
  blow-up — the carrier makes both real.
- The ψ adjudication settled: **R-b (source reparameterization)**, not target-ψ. Target per-edge ψ is
  UNSOUND (1176 interior cover misses; `cert-psi-mix.md` T2b). R-b keeps chart IMAGES equal to the pure-β
  images, so the cover is the **pure** `node_pivotCover_of_atom` (the sheared variant retires to `ψ=.refl`),
  and `|det Dα|=1` leaves the Jacobian + monomial exponents untouched.
- The fan-out (per-node `d_center` pivot family) lives ENTIRELY in the atlas List, NEVER in `Edge`/`StepRel`
  (sub-gap-3 pin) — realized via a `geometricLeafPaths t` traversal, not a spine change.

## 1. The concrete coordinate split `q` (the one dependency my counter-sign named)

`node_pivotCover_of_atom` (`PivotCoverFold.lean:187`) takes `q : Params M ≃ₜ (Fin d → ℝ) × E` as a
HYPOTHESIS. For clause (D)'s non-opacity bar (and for the cover to be non-vacuous), `q` must be a CONCRETE
`Homeomorph`, per blow-up node, not an existential.

**Proposed:** a per-node `centerSplit` builder
`q_node : Params M ≃ₜ (Fin d_center → ℝ) × (Fin (flatDim M − d_center) → ℝ)` that permutes the flat
coordinates (via `paramsEquivFlat`) so the first `d_center` are the node's center coordinates and the rest
are spectators. The center coordinates are:
- Case 1: the `J₁ × (M^{(S+1)}−J)` residual `d`-block entries **plus** the one divisor coord `u_{s,k}`
  (`page-pin-centers.md`; `d_center = runLen·resCols + 1`).
- Case 2: the whole residual block `(M(S)−J) × (M^{(S+1)}−J)` (`d_center = resRows·resCols`; no `u`).

Construction: a coordinate PERMUTATION homeomorphism = `paramsEquivFlat M` composed with a
`Fin (flatDim M) ≃ Fin d_center ⊕ Fin (rest)` `Equiv.Perm` selecting the center indices, then
`(finSumEquiv).arrowCongr`. This is a banked-shape build (finite-coordinate permutation + `paramsEquivFlat`);
the center-index selector reads the node's `divCoord`/center data. **Owed Lean piece (mine): `centerSplit`
+ its `Homeomorph` proof.**

## 2. The per-edge R-b fields (revision of the tick-163 4-part spec)

Per blow-up edge `e` (one pivot choice in the node's `d_center` family), expose STRUCTURED data (on
`ChartSubst` or a sibling record — t05's call on where it lives):

1. **pivot** `pivotOf e : Fin d_center` (the center coordinate this chart pivots on) + its exponent
   contribution (feeds `divExp`; `d_center` per node from §1).
2. **β_e** `= q_node.symm ∘ (Prod.map (pivotChart (pivotOf e)) id) ∘ q_node` — the banked atom
   (`PivotCover.pivotChart`); `|det Dβ_e| = |flat-pivot-coord|^{d_center − 1}` (the monomial blow-up).
3. **α_e** `: Params M ≃ₜ Params M` — the SOURCE det-1 gauge, `|det Dα_e| = 1`, PROOF-CARRYING:
   - `α_u = .refl` (case-1(1) `u`-pivot — no Schur clean; `cert-single-psi`, `cert-psi-mix` T1).
   - `α_d =` the inverse Schur update in ratio coordinates `r_{ij} ↦ r_{ij} − r_{ip} r_{pj}` (a banked
     polynomial unipotent, det 1; `cert-psi-mix` §R-b + Codex Q4).
4. **localSub_e** `= β̃_e = β_e ∘ α_e⁻¹`, on the reparametrized domain `α_e(D_e)` where
   `D_e = q_node ⁻¹' (pivotChartDom (pivotOf e) R ×ˢ univ)`. `leaf.chartMap = fold of localSub_e` down the
   root→leaf path (the path-accumulator through `buildTree`).

**The load-bearing identity (owed Lean piece, mine — cert-specified):**
`β̃_e '' (α_e '' D_e) = β_e '' D_e` (α_e does not touch the image). Consequence: the per-node image union
is `⋃_e β̃_e '' (α_e D_e) = ⋃_e β_e '' D_e = cube` — the PURE `node_pivotCover_of_atom` tiles, no gap. This
is why R-b reuses the banked pure atom and the sheared lemma is not needed for the cover.

## 3. The per-node `d_center` family emission (the `hbij` contract)

Each blow-up node must emit its FULL `d_center` pivot family (one edge per center coordinate), so
`node_pivotCover_of_atom`'s `hbij : ∀ i : Fin d_center, ∃ e ∈ edges, pivotOf e = i` holds by construction.
This is the `pivotComplete` amendment (`cert-cov-rungs12`): the 2-representative ledger emission
undershoots at `d_center ≥ 3`. `d_center` is computable from the node (§1). Per the sub-gap-3 pin the
fan-out lives in the atlas, so this is realized in the `geometricLeafPaths` traversal (§4), NOT by adding
`d_center` real edges to the spine tree (`StepRel` stays the quotient).

## 4. `geometricLeafPaths t` (the fan-out enumeration → the flat atlas)

A `leafPaths`-analog (`PivotCoverFold.lean:216` is the quotient version) that, at each node, fans out over
the `d_center` pivot choices and recurses into the (shared) profile child. It produces the flat atlas
`List (LeafData M)` = one piece per (root→leaf pivot-choice sequence), each piece's `chartMap` = the fold
of its path's `β̃_e`. **Owed Lean piece (mine): the `geometricLeafPaths` recursion** (structural, analog of
`leafPaths`/`edgesLeafPaths`; needs only `d_center` per node + the per-edge fields of §2). Clause (D) is the
coherence over this: `∀ c ∈ atlas, ∃ p ∈ geometricLeafPaths t, c.chartMap = fold(p)` — provable over the
constructed atlas, false on a generic one (the two-sided honesty test).

## 5. What coverage consumes (my side, after the carrier lands)

- **Clause (A) cover:** `chartBridge_imageCover_of_ownCovers` over the geometric tree, folding
  `node_pivotCover_of_atom` (PURE, via §2's image identity) up `ownCovers_branch`; `atlas = leaves t_geo`.
- **Clause (B) 3 Props per piece:** a.e.-InjOn (`pivotChart_ae_injOn` ∘ α_e-homeo ∘ q, banked atom +
  transport); `LeafJacobian` (`|det Dβ̃_e| = |det Dβ_e|`, α det-1 — needs the β-det atom, item 5b below);
  `LeafPullback` (the monomial pullback identity — the analytic side, o5/carrier, NOT coverage geometry).
- **Clause (C) exponent-agreement:** geometric chart `divExp` = its ledger-quotient leaf's `divExp`
  (chart-independent bump `runLen·resCols`), so `∈ terminalExponents t`.

## 6. Division of labour

- **t05 (construction/carrier):** the per-edge structured fields of §2 on the construction side (pivot,
  β_e via the banked atom, α_e proof-carrying det-1, `localSub_e = β̃_e`); the buildTree path-accumulator so
  `leafOfState.chartMap` = the fold (replaces the `id` placeholder); the per-node `d_center` count exposed.
- **coverage (me):** `centerSplit`/concrete `q` (§1); the α_e frames + the domain-reparam identity `β̃ '' αD
  = β '' D` (§2, cert-specified banked-atom step); `geometricLeafPaths` (§4); the cover fold, the 3 Props,
  clause (D) (§5). Clause (D) then lands IN `ChartBridge` — the cordon gate (task #10) before
  `chartBridge_buildTree` discharges.
- **o5:** `LeafPullback`'s monomialization pullback identity (the analytic side).

## 7. Owed Lean pieces, named (none blocks the interface; all banked-atom-shaped)

1. `centerSplit` (concrete per-node `q` `Homeomorph`) — §1.
2. α_e frames (`α_u=.refl`, `α_d`=inverse-Schur unipotent, det 1) + `β̃_e '' α_e(D_e) = β_e '' D_e` — §2
   (the cert-psi-mix owed piece).
3. The `pivotChart` Jacobian-det atom `|det D(pivotChart i)| = |u_i|^{d−1}` in Lean (docstring/battery
   only today) — feeds `LeafJacobian`; counter-sign item 5b.
4. `geometricLeafPaths` recursion + clause (D) coherence — §4.

## 8. One open question for t05 + elder

Where do the §2 structured fields live — extend `ChartSubst` (per-edge, on the spine), or a sibling record
attached to the geometric traversal only (keeping `ChartSubst` minimal, fan-out fully off-spine)? The
sub-gap-3 pin favours the latter (fan-out is atlas data), but β_e/α_e are naturally per-edge. My lean:
a sibling `GeoChart` record consumed by `geometricLeafPaths`, so `ChartSubst`/`StepRel` stay the untouched
quotient. t05's call — flag it at the elder gate with the type change (if any).

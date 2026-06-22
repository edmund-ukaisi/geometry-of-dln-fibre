# (S-min) achiever path `i₀` — re-spelled in fm3's exact `routeMIota` encoding (pp-hall, 2026-06-22, #148)

**The final transcription aid.** fm3's `routeMIota` is surfaced (`RouteMTree.lean`); this re-spells the
g147 achiever path `i₀` in that exact encoding so fm3 transcribes `IsResolutionAtlas.achiever` with no
translation gap. The g147 datum is unchanged (encoding-independent); this pins it to fm3's concrete ι.

## fm3's encoding (read from `RouteMTree.lean`)
- `RouteState = ⟨L, M⟩` (the node carrier); `routeAtlas : (S : RouteState) → NodeChartFamily S` built by
  `WellFounded.fix routeRel_wf` matching `classify S : RouteCase S`.
- `routeMIota S := (routeAtlas S).ι`, a **Σ/⊕-tree of leaves** (the `match classify S` branches):
  - `.leaf md` → `ι = PUnit`;
  - `.c1 cs dec` → `ι = Σ c : cs, (routeAtlas (schurState S c.1)).ι` (pick a pivot cell, recurse on the residual);
  - `.c2 c dec` → `ι = (routeAtlas (passState S c)).ι` (descend, same ι);
  - `.c4 s ..` → `ι = AL.ι ⊕ AR.ι` (left/right block);
  - `.c5 cs p ..` → `ι = (Σ c : cs, A1.ι) ⊕ A2.ι` (C1-Σ complement ⊕ C2 survivor).
- per-leaf data: `routeD S i = ((routeAtlas S).data i).d`, `routeK`/`routeH` likewise (accumulated by
  `addC1Data`/`addC2Data`/`addLData`/`addRData` down the tree).
**Indexing note for the bridge:** `routeMIota` is indexed by `RouteState ⟨L,M⟩`, while
`IsResolutionAtlas M ι d k h` takes `M` + an external `ι`. The wiring is `ι := routeMIota ⟨L,M⟩`,
`d := routeD ⟨L,M⟩`, `k := routeK ⟨L,M⟩`, `h := routeH ⟨L,M⟩`. So `achiever` reads
`∃ i : routeMIota ⟨L,M⟩, monomialThreshold (routeD _ i)(routeK _ i)(routeH _ i) = ½·m₀`.

## The achiever path `i₀` (the nested Σ/Sum term)
A leaf `i : routeMIota S` is a nested term of `Sigma.mk` / `Sum.inl`/`Sum.inr` / `PUnit.unit` tracing the
root-to-leaf path. The achiever `i₀` for the minimiser `T* = (t_1,…,t_L)` is built by the SAME
`WellFounded.fix` recursion, picking at each node the constructor + sub-choice that resolves the active
factor to its `T*`-rank:
- `classify S = .c1 cs dec` (coupled defect, `T*` wants rank `t_s < t_{s-1}`):
  `i₀ at S = ⟨c*, i₀'⟩ : Σ c : cs, (routeAtlas (schurState S c.1)).ι`, where `c* ∈ cs` is the
  `PivotChoice` dropping ONE rank-unit toward `t_s` (fm3's per-factor recursion: resolving `C_s` from
  rank `t_{s-1}` to `t_s` takes `(t_{s-1}−t_s)` such C1 steps, each a Schur `ΣM−2` drop), `i₀'` the
  achiever of the residual. The achiever follows the C1 pivot-cell at each step until `C_s` is at rank
  `t_s`, then proceeds to the next factor.
- `classify S = .c2 c dec` (full-rank pass-through, `t_s = t_{s-1}`): `i₀ at S = i₀' : (routeAtlas (passState S c)).ι` (same ι, descend).
- `classify S = .c5 cs p ..` (mixed): `i₀ at S = Sum.inl ⟨c*, i₀'⟩` — the complement-via-C1 branch
  (the minimiser's binding center is the complement's codim-`m₀` divisor, so `Sum.inl`).
- `classify S = .c4 s ..` (pinch): `i₀ at S = Sum.inl i₀'` or `Sum.inr i₀'` — the block containing `T*`'s
  binding center.
- residual at the binding center: `classify = .leaf md` → `i₀ = PUnit.unit`, with `md` the `MonoData`
  carrying the binding divisor `(k,h) = (1, m₀−1)`.
So `i₀ = ⟨c*₁, ⟨c*₂, … , PUnit.unit⟩⟩` (Σ-nesting through C1 nodes, `Sum.inl`/`inr` at C4/C5), bottoming at
the `PUnit` leaf whose `MonoData` has the binding `(1, m₀−1)`.

## The (2,2,2) concrete instance (`S₀ = ⟨2, ![2,2,2]⟩`) — TWO C1 nodes (fm3's authoritative depth)
`T* = (1,0)`, `m₀ = 3`, `lambdaCore = 3/2`. **CORRECTION (fm3 #47): fm3's dispatcher resolves PER-FACTOR
incrementally (each C1 a one-rank-unit Schur `ΣM−2` step), so the achiever path is TWO C1 nodes, not one.
My earlier 1-node `⟨c*, PUnit.unit⟩` used the r1-design §2 abstract "codim-3 in one blow-up" form (the
banked `Case222` ρ-chart); fm3's RouteMTree is the authoritative per-factor recursion.**
- `classify S₀ = .c1 cs dec` (resolve `C₁` from rank 2 → rank 1, the rank-1 drop). `c*₁ ∈ cs` = the
  A-block pivot cell. `schurState S₀ c*₁` = the residual node (the incidence locus still to resolve).
- `classify (schurState S₀ c*₁) = .c1 cs' dec'` (resolve the residual at the incidence pivot — the
  `A₁A₂ = 0` alignment). `c*₂ ∈ cs'` = the incidence pivot cell (the `Case222` ρ-chart pivot). Its
  `pivotBlowupOn` center is the full codim-`m₀` (=3) stratum, so its axis is the binding divisor
  `(k,h) = (1, m₀−1) = (1, 2)` (`Case222`: ρ-chart, `|det Dφ| = |ρ|²`, `F = α²ρ²·[unit]`).
- `classify (schurState … c*₂) = .leaf md` → `PUnit.unit`.
- ⟹ `i₀ = ⟨c*₁, ⟨c*₂, PUnit.unit⟩⟩ : routeMIota S₀` (TWO nested `.c1` Σ's, then the leaf).
- ⟹ the binding axis `j₀` (on the `c*₂` step) has `routeK S₀ i₀ j₀ = 1`, `routeH S₀ i₀ j₀ = 2 = m₀−1`, so
  `monomialThreshold (routeD S₀ i₀)(routeK S₀ i₀)(routeH S₀ i₀) = ⨅_j axisRatio = (2+1)/(2·1) = 3/2 = ½·m₀`. ✓
**`IsResolutionAtlas.achiever` for `S₀`:** `⟨i₀, (proof: threshold = ½·m₀)⟩`, `i₀ = ⟨c*₁, ⟨c*₂, PUnit.unit⟩⟩`.

## What fm3 transcribes
The `achiever` field (or `of_mult_and_achiever`'s `(i₀, j₀)`):
- `i₀ : routeMIota ⟨L,M⟩` = the nested Σ/Sum term following the `T*`-rank `PivotChoice` at each node
  (built by the same `WellFounded.fix` as `routeAtlas`, selecting the `T*`-rank cell). For the `(2,2,2)`
  anchor: `i₀ = ⟨c*₁, ⟨c*₂, PUnit.unit⟩⟩` (two C1 nodes), `c*₂` the ρ-chart (incidence) pivot cell.
- `j₀ : Fin (routeD ⟨L,M⟩ i₀)` = the binding-divisor coordinate on `i₀`'s `MonoData`, with
  `routeK _ i₀ j₀ = 1` (`hk₀`) and `routeH _ i₀ j₀ = m₀−1` (`hh₀`). **Which axis is `j₀`:** the
  `monomialThreshold = ⨅_j axisRatio` is the MIN over the path's C1 axes; `j₀` is the axis with the
  LARGEST `card = m₀` (the C1 step whose `pivotBlowupOn` center is the full codim-`m₀` stratum — the last
  step completing `T*`'s resolution). That axis binds the `⨅` at `½·m₀`; the others (smaller `card`) have
  larger ratio. So `j₀` = the codim-`m₀` C1 axis (the `c*₂` step for `(2,2,2)`).
- then `monomialThreshold_eq_half_of_binding` (already wired in `of_mult_and_achiever`) closes `achiever`.

**Realizability (why `i₀` exists, the (S-min) obligation):** `classify S` returns `.c1`/`.c5` with a `cs`
CONTAINING the `T*`-rank `PivotChoice` — nonempty because `T*` is realizable
(`Core.OrbitKostant`/`Orbit.baseChange_normalForm`: the Gabriel normal form realizes the rank pattern with
prefix `T*`, so the rank-`t_s` minor is selectable at each node). Once `classify`/`PivotChoice` are
un-stubbed (the rank-pattern combinatorics, #39), `i₀` is concretely "the Σ/Sum term following the
`T*`-rank choices." Only the MINIMISER need be reached (S-min, weaker than full surjectivity).

## Dependency flag for fm3 (the one thing that gates the concrete `i₀`)
`classify` and `PivotChoice` are STUBBED in `RouteMTree.lean` (`PivotChoice S := ⟨dummy : Unit⟩`,
`classify S := sorry`). The achiever `i₀` is concrete only once those carry the real rank-pattern content
(the `PivotChoice` indexing the `argmaxCellOn` pivot cells, `classify` reading rank relative to the active
prefix image). Until then, `i₀` is specified structurally (the nested term following the `T*`-rank cell at
each node), and the `(2,2,2)` anchor is the concrete check (`⟨c*₁, ⟨c*₂, PUnit.unit⟩⟩` two C1 nodes, `c*₂` the ρ-chart pivot).
The realizability (`cs` nonempty at the `T*`-rank cell) rides `Core.baseChange_normalForm` — independent of
the stub. So fm3 can wire `achiever`'s SHAPE now (the recursion selecting the `T*`-cell) and fill the
concrete `c*` when `classify`/`PivotChoice` land.

## Provenance
Re-spells g147's encoding-independent achiever datum (`T*` = `inf' Mval` minimiser, binding divisor
`(1,m₀−1)`) into fm3's `RouteMTree.lean` `routeMIota` Σ/⊕-tree encoding. Reads `RouteMTree.lean`
(`routeAtlas`, `routeMIota`, `routeD/K/H`, the `RouteCase` constructors). The `(2,2,2)` anchor is the
concrete instance (`i₀ = ⟨c*₁, ⟨c*₂, PUnit.unit⟩⟩` two C1 nodes, the ρ-chart incidence pivot — fm3 #47).
Script: `g148_iota_respell.py` in `g129-scripts/`.
Builds on #147 (the achiever cert), #134 ((S-min)), `Core.OrbitKostant` (realizability), fm3's G1 (#39).

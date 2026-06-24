# RouteMTree (d,k,h) accumulation semantics — derived from the banked (2,2,2) (fm3, for the leaf arm)

The per-leaf (d,k,h) for crux2's IsRouteMCover, grounded in Case222's unitK8/unitH8 (the path-accumulated
monomial), NOT a fresh smooth block per node.

## The semantics (from Case222Resolution unitK8/unitH8)
- unitK8 = ![1,0,1,0,0,0,0,0], unitH8 = ![3,0,2,0,0,0,0,0] on Fin 8 (the FLAT ambient dim).
- These are PATH-ACCUMULATED: axis u0 = step-1 pivot (k,h)=(1,3); axis u2=z1 = step-2 pivot (k,h)=(1,2);
  all other axes are spectators (k,h)=(0,0).
- So per leaf: d = the FLAT AMBIENT DIM (constant down the path, = the chart's Fin d carrier), and the
  (k,h) vector has (1, card−1) SET at each pivot axis the path blew up, (0,0) elsewhere (the unit/
  spectator directions). monomialThreshold d k h = ⨅ axisRatio(h)(k) = 3/2 (binding axes) ∧ ⊤ (spectators).

## Encoding in the WF.fix RouteAtlas/NodeChartFamily recursion
- MonoData.d = the flat ambient dim (CONSTANT across all leaves of a given M's tree — it's flatDim-shaped
  at the node, fixed down the path; the spectator coords carry through).
- LEAF md = { d := (flat ambient at the leaf), k := 0, h := 0 } — the UNIT (no monomial; all singular
  directions already blown up; F ≥ 1).
- addC1Data S c (the C1 node, wrapping OUTWARD): SET the pivot axis p's exponents to (k,h)=(1, active.card−1)
  in the MonoData's k/h vectors (the x_p² weight + the |x_p|^{card−1} Jacobian). The pivot axis is a
  distinct ambient coordinate, so accumulation = setting that index; the rest unchanged.
- addC2Data / addLData / addRData: C2 sets no new monomial (pass-through, the descended chain's monomial
  rides); C4 the two blocks' (k,h) on disjoint coordinate ranges (the Fubini split severs the coords).

## The subtlety to handle in the build
The ambient d is CONSTANT down a path but the recursion nests Σ/Sum over child families — so MonoData.d
must be threaded as the ambient (the node's flat dim), and the pivot-axis SET must target the right Fin d
index. The Fin d index of the pivot = its position in the flat ambient (from PivotChoice.pivot mapped into
the flat layout). This is the one careful piece: PivotChoice.pivot : Fin ambDim ↦ the Fin (MonoData.d)
index. Likely MonoData.d = PivotChoice.ambDim (the node's ambient = the chart carrier), threaded constant
since the blow-up is dimension-preserving on the flat ambient (pivotBlowupOn : Fin N → Fin N).

## Why this matches the monomial route (not the squeeze)
The leaf is the UNIT (k=h=0), NOT a smooth block d/2 (that would be the additive squeeze, off-path). The
d/2-type RLCT contributions come ENTIRELY from the accumulated pivot (k,h)=(1,card−1) axes via
monomialThreshold = ⨅ axisRatio, never from an additive nReg/2. Confirms the forced framing.

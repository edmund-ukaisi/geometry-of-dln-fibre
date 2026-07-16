# genm-tideD-edgedispatch — building `edge_coupledBox_lt_top` (the edge dispatch arm)

**Seat:** formaliser (tide). **Picks up:** the edge dispatch arm (coordinator-assigned). **Base:**
`origin/genm-integration @d9891f5f5` (arch1build's coherent-unit merge; my R2 atoms merged in). **Branch:**
`expedition/genm-tideD-edgedispatch`. **Scope (coordinator):** build the **b=1, a<u** restricted instance
as a multi-turn build; isolate (don't build) R3, a≥u, W2-backbone.

## Target
`edge_coupledBox_lt_top` — `∫_p coupledBoxIntegrand M u c' p < ⊤` over the generic EDGE cell
(`cellRankIndex i = deepTailMin M`, `deepTailMin M < a+b`, a=M₀−u, b=M₁−u). Discharges the edge case of
`RouteMSJHcellNull.coupledBox_cell_lt_top_of_generic`'s `hgen`. Skeleton (signature + `sorry`) in
`RouteMSJEdgeAssembly.lean`, uncommitted.

## LANDED this build — R1 (corank-collapse reduction), clean-three

`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeLeaf.lean` (network-free, `[propext, Classical.choice, Quot.sound]`):
- `frobSq_ge_sumSq_mulVec` — `∑ᵢ((of M)·ω i)² ≤ frobSq M` for sub-unit ω (per-row Cauchy-Schwarz). R1 core.
- `corank_afortiori` — `frobSq(Matrix.of C * Qp + γ⊗q_b) ≥ ‖(of C)·v + σγ‖²` (v=Qp·ω, ω=q_b/‖q_b‖, σ=‖q_b‖).
  Drops the transverse corank directions, keeps the single fragile direction.
- `corank_integrand_le` — `(W+frobSq(...))^{−c'} ≤ (W+‖C·v+σγ‖²)^{−c'}` (ofReal, W>0, c'≥0), via rpow
  base-antitonicity. The pointwise R1 output feeding the C-shift atoms.
Commits `@990c55165` (core), `@f26ca830f` (R1 complete).

## The reduction chain (edgeasm's recipe + couplerad's R3 dissolution + the W2 finding)

coupledBoxIntegrand (edge cell) → **R1** (corank_integrand_le: split pivot core W=frobSq(P·Q̃ₚ), drop the
≥0 transverse, corank→‖C·v+σγ‖²; LANDED) → **Fubini transport** (∫_x∫_Γ over outerDom×genBox →
∫_{P,B₁₂,z,A_cor}∫_γ∫_C; template RouteMSJChartShear:248-306; a-fortiori + enlarge-Γ + Tonelli) → **atoms**
(edge_leaf_gamma_bound / edge_C_shift_bound, RouteMSJEdgeCShift, LANDED) → **|v|^{−a} disposal** over the
reduced params (corner_block_lintegral_lt_top, a<u; RouteMSJRadialPolar) → **W2** (see below).

## R3 DISSOLVES (couplerad) — the b=1 leaf is the FULL-edge leaf

couplerad: `coupledBox(b) ≤ det(Q_b'Q_b'ᵀ)^{−a/2}·β(a(b−1),c')·[b=1 leaf at c''=c'−a(b−1)/2]` — peel the
(b−1) full-rank corank rows via an EXACT Γ'-Gaussian (= arch1build's (D) charge pull-out at (a,b−1), FINITE
at the immediate-edge boundary a+(b−1)≤ρ_d), the last coupled row is the b=1 leaf. NO new measure theory.
**My c'' check PASSES strictly:** edge window c'>ab/2 ⟹ c''>a/2 ⟹ a<2c'' = my atoms' finiteness threshold.
So R3 is NOT a wall — it's (D)-boundary + my b=1 leaf. My b=1,a<u leaf CLOSES THE FULL EDGE (all b) via the
peel. (Pending: couplerad's Codex corroboration before treating fully banked.)

## W2 IH-thread IS the recursion backbone — NOT edge-local (flagged to controller)

`RouteMSJJointReduce` docstring (explicit): reducing the peeled integral to strictly-shorter chains is "the
UNBUILT resolution-of-singularities chart-tree" — the general (S,J) descent. My edge W2 (match
`∫_{reduced} frobSq(P·Q̃ₚ)^{a/2−c'}·(...)` into `routeMLayerBoxIntegral(redChain u M)` at the shifted
exponent, so the arity−1 IH `RouteMBoxThresholdFinite(redChain u M)` applies) needs exactly this
shorter-chain shape-match. The arithmetic gate `sjChargeBudget_le` IS banked; the reduction TO it is NOT.
edgeasm's "1 IH call" + satred's "single-chain verified" both GLOSS this. **Recommendation (controller's
steer #1 trigger): commission a dedicated backbone build (shared across interior/edge/deep, not
edge-specific); my edge brick CONSUMES it as an interface + hIH, not builds it.**

## Remaining for the b=1,a<u brick (next turns)
Fubini transport + freedSchurLoss wiring (instantiate corank_integrand_le at the hsQ shapes on the edge
cell; W=frobSq(P·Q̃ₚ), v=Q̃ₚ·ω) + {q_b=0} null (a.e., like coupledBox_deficientCell_null) + |v|^{−a}
disposal (corner_block, a<u) + [W2 backbone interface — consume, don't build]. Then couplerad's (b−1)-peel
lifts b=1 → all-b.

## Isolated (not building, per coordinator)
- **R3 (b≥2):** dissolves via couplerad's peel (above) — pending Codex corroboration; corankrec's
  dispatch-reachability scan now moot for the wall (dissolves regardless).
- **a≥u:** satred, recursion-driven (qbox per-level PIVOT-Gram det(Q̃ₚQ̃ₚᵀ)^{−a/2} + reduced-chain IH;
  NEVER qbox-on-corank-at-edge — the corank Gram diverges at edge dims a=q−b+1). D-cert §3bis.
- **W2 backbone:** the shorter-chain shape-match (above) — controller to commission.

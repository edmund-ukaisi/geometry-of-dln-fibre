"""
Q2 — Trace the Route-B assembly closure for resolution_charts = ⨅ monomialThreshold.

The gate:  rlctAtOn(dlnLoss M 0)(0) = ⨅_i monomialThreshold(dᵢ,kᵢ,hᵢ).
RHS value already proven = ½·minAdm M (routeLayerAtlas_value_eq_half_minAdm).
So the gate ≡  rlctAtOn(dlnLoss M 0)(0) = ½·minAdm M  AS A VALUE, but stated as ⨅ over leaves.

ROUTE A (cover): resolution_charts_of_layerCover consumes an IsRouteMCover and applies the
  bridge routeM_rlctAtOn_eq_iInf. The cover carries BOTH directions:
    cover_le   -> rlctAtOn ≥ ⨅   (finiteness below threshold; UPPER bound on rlct... actually ≥)
    cover_ge_div -> rlctAtOn ≤ ⨅ (divergence at/above threshold)
  i.e. the cover gives the min-over-leaves structure directly: the ⨅ is read off the leaf exponents.

ROUTE B (squeeze): the per-node step gives
    rlctAtOn(flatCore)(0,0) = nReg/2 + rlctAtOn(G²)(0)
  Iterating down ONE branch (a sequence of peels) gives
    rlctAtOn(core) = Σ_nodes nReg/2  =  (one branch's accumulated codim)/2.
  But WHICH branch? The squeeze at a node fixes a SINGLE peel rank t (the hnode datum's bcol/SΓ
  encode ONE chart). To get rlctAtOn = ½·minAdm = ½·MIN_t Mval(t), Route B must:
    (B1) show the squeeze along the ACHIEVER branch gives ½·minAdm  (the ≤ direction... or the value), AND
    (B2) show NO OTHER branch gives a SMALLER rlct (the min is attained, not undershot).
"""
print("=== The connective gaps in Route B's assembly ===\n")

print("GAP 1 (carrier re-home): GeneralR1Recursion is on the OLD fixed-arity ChainDimSplit carrier")
print("  (drop+red = M, SAME arity Fin(L+1)). The gate is routed through the LayerSplit carrier")
print("  (redChain t M = (t,M₂,…), ONE FEWER LAYER). The squeeze step's `S.red` (ChainDimSplit)")
print("  must be re-homed to LayerSplit's redChain. The SOUNDNESS NOTE + RouteMLayerSplit docstring")
print("  say the fixed-arity carrier STRUCTURALLY CANNOT express the layer-collapsing recursion")
print("  (it was the documented sorry). So a full re-home of GeneralR1Recursion's per-node squeeze")
print("  onto LayerSplit is REQUIRED, not cosmetic.\n")

print("GAP 2 (single-branch vs min-over-branches): the squeeze gives rlctAtOn along ONE branch.")
print("  resolution_charts's RHS is ⨅_i (MIN over ALL leaves). To connect:")
print("   - the ACHIEVER branch's squeeze value = ½·minAdm  (achievable),")
print("   - BUT the LOWER bound (no branch gives a smaller rlct) is the missing content. The squeeze")
print("     computes rlctAtOn EXACTLY at the deepest point, so a single squeeze along the achiever")
print("     gives rlctAtOn = ½·minAdm DIRECTLY (not just ≥). That IS the value. So actually...\n")

print("  REFINEMENT: rlctAtOn(dlnLoss M 0)(0) is a SINGLE number. If the squeeze computes it")
print("  EXACTLY (= ½·minAdm) along the achiever decomposition, then we have rlctAtOn = ½·minAdm")
print("  as a VALUE. The ⨅ monomialThreshold = ½·minAdm is ALREADY PROVEN (value lane). So the")
print("  gate would close by  rlctAtOn = ½·minAdm = ⨅ monomialThreshold,  TRANSITIVITY — NO cover needed!")
print("  This is the POTENTIAL Route-B shortcut: bypass IsRouteMCover entirely.\n")

print("GAP 3 (the squeeze computes rlctAtOn EXACTLY only if hnode holds at EVERY node on the")
print("  achiever branch). By Q1: hnode fails at corank-≥2 nodes. The (3,3,4) achiever branch")
print("  t=(1,0) HAS a corank-2 node. So the squeeze CANNOT compute rlctAtOn exactly there —")
print("  the per-node hnode is unprovable at that node (Q1 + Codex Q-A/Q-D).\n")

print("GAP 4 (the analytic monomial bound — Codex Q-C): even where hnode holds (corank-≤1),")
print("  the per-node step rlctAtOn(flatCore) = nReg/2 + rlctAtOn(G²) uses rlct_additive_smooth_block")
print("  (S1.5, the Fubini/smooth-block split) — an ANALYTIC fact, not derived from the squeeze.")
print("  And the LEAF rlct (terminating the recursion) must ultimately be a monomialThreshold —")
print("  which requires monomial_rlct (the S2 citation). So Route B STILL imports the S2 analytic")
print("  extraction at the leaves; it does not avoid it. (Soundness gate: that is S2's job, fine,")
print("  as long as it is not smuggled into hnode.)\n")

print("=== Q2 VERDICT ===")
print("The Route-B assembly has a POTENTIAL shortcut (transitivity via the value lane, GAP 2),")
print("bypassing IsRouteMCover. But it requires the squeeze to compute rlctAtOn EXACTLY along the")
print("achiever branch (GAP 3), which fails at corank-≥2 achiever nodes (Q1). For corank-≤1 width")
print("vectors (rank-1 chains, c₁=0 peels) the squeeze-assembly IS a sound closure; for general M")
print("(corank-≥2 binding branches) it is NOT — the per-node hnode is unprovable there.")

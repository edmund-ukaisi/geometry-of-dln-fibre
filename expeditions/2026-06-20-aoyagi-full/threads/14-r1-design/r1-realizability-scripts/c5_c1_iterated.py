# pp2's precision flag: C1 s=6 (2→0) = ONE rank-2 node (ΣM-drop 4) or TWO iterated rank-1 nodes (drop 2 each)?
# The banked schurState: drop = 1 at each of the two pivot vertices per step (ΣM drops by 2, a single
# rank-1 Schur peel). NO rank-r parameter. ⟹ the LIVE machinery is ITERATED RANK-1.
# So a rank-2→0 full drop = TWO rank-1 C1 steps. Verify the iterated reading is consistent.
#
# Iterated: at s=6 the partial product rank goes 2→0. As iterated rank-1 schurState peels:
#   step A: peel 1 unit (rank 2→1 at this layer's resolution), ΣM drops 2.
#   step B: peel 1 unit (rank 1→0), ΣM drops 2.
# Total ΣM drop 4 = 2r (r=2), matching the rank-2 reading's total — but TWO nodes, not one.
print("Banked schurState: drop=1 per pivot vertex per step (ΣM drop 2, single rank-1 peel). No rank-r param.")
print("⟹ LIVE machinery = ITERATED RANK-1. A rank-2→0 full drop = TWO rank-1 C1 steps (ΣM drop 2 each).")
print()
# Re-spell the FULL per-node chain for t=(3,3,2,2,2,0) under the iterated-rank-1 reading.
# rank chain t_0..t_6 = 3,3,3,2,2,2,0. Drops: s=3 (3→2, drop 1), s=6 (2→0, drop 2).
# Under iterated rank-1: each rank-k drop = k single-unit steps.
tt = [3,3,3,2,2,2,0]
nodes=[]
for s in range(1,len(tt)):
    a,b = tt[s-1],tt[s]
    drop = a-b
    if drop==0:
        nodes.append((s,a,b,0,"C2 gauge"))
    elif b==0:
        # full drop to 0: 'drop' iterated rank-1 C1 steps
        nodes.append((s,a,b,drop,f"C1 full ({drop} iterated rank-1 steps)"))
    else:
        # partial drop: 'drop' iterated rank-1 C5 steps (here drop=1, one C5 step)
        nodes.append((s,a,b,drop,f"C5 partial ({drop} iterated rank-1 step{'s' if drop>1 else ''})"))
total_steps=0
total_sigmaM=0
print("Per-node (iterated-rank-1 reading):")
for (s,a,b,drop,typ) in nodes:
    if drop>0:
        steps=drop; sigma=2*drop
        total_steps+=steps; total_sigmaM+=sigma
        print(f"  s={s}: {a}→{b}  [{typ}]  ⟹ {steps} recursion node(s), ΣM drop {sigma}")
    else:
        print(f"  s={s}: {a}→{b}  [{typ}]  (no node, no drop)")
print()
print(f"TOTAL recursion/divisor NODES (iterated rank-1): {total_steps}")
print(f"  = 1 (C5 at s=3, drop 1) + 2 (C1 at s=6, drop 2 = two rank-1 steps) = 3 nodes")
print(f"TOTAL ΣM drop: {total_sigmaM} (= 2·(1+2) = 6 = 2·total-rank-dropped). ΣM: 6→... wait, this is")
print(f"  the per-layer width drop; the ACHIEVER codim-list has {total_steps} divisors (one per rank-1 step).")
print()
# CONTRAST with the rank-r reading (one node per layer-drop):
print("CONTRAST — rank-r reading (one node per layer, ΣM-drop = 2·layer-rank-drop):")
print("  s=3: one C5 node (ΣM drop 2); s=6: one rank-2 C1 node (ΣM drop 4). = 2 nodes.")
print("  Both terminate (ΣM>0 each step); the DIFFERENCE is node count (3 vs 2) + codim-list length.")
print()
print("PINNED: the BANKED schurState is rank-1 (drop=1/vertex), so the LIVE reading is ITERATED RANK-1")
print("⟹ s=6 (2→0) = TWO rank-1 C1 nodes. Total: 3 divisor nodes (1 C5 + 2 C1), 4 C2 gauge nodes.")
print("UNLESS the formaliser defines a rank-r schurState variant (drop=r/vertex) — then 2 nodes. The")
print("banked def is rank-1, so default = iterated (3 nodes).")

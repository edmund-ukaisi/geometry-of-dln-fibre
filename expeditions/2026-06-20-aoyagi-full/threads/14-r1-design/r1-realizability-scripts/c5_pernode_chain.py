# Spell the per-node ChainDimSplit chain for t=(3,3,2,2,2,0), classifying each node C2/C5/C1.
# t_j = rank(C_1···C_j). Convention: t_0 = M^1 (=M[0]). The chain has L layers; t=(t_1..t_L).
# Here t = (3,3,2,2,2,0) — that's 6 entries, so L=6 (a 6-layer chain), t_6=0.
# Need a width vector M (Fin 7). For the achiever context use M generous; the NODE TYPES depend only
# on the drop profile (t_{s-1} vs t_s), not the exact widths (beyond admissibility).
t = [3,3,2,2,2,0]
M0 = 3                 # t_0 = M^1
tt = [M0] + t          # tt[0..6] = t_0..t_6 = 3,3,3,2,2,2,0
L = len(t)             # 6 layers
print(f"rank chain t_0..t_L: {tt}")
print()
print("Per-node classification (node s resolves the step t_{s-1} -> t_s, for s=1..L):")
print("  C2 = no drop (t_{s-1}=t_s, full-rank pass-through, gauge-absorbed)")
print("  C5 = partial drop (t_{s-1} > t_s > 0)")
print("  C1 = full drop to 0 (t_{s-1} > t_s = 0)")
print()
nodes=[]
for s in range(1, L+1):
    a, b = tt[s-1], tt[s]
    if a == b:
        typ = "C2 (pass-through, gauge)"
    elif b == 0 and a > 0:
        typ = "C1 (full drop to 0)"
    elif a > b > 0:
        typ = f"C5 (partial drop {a}->{b}, complement {a-b}, survivor {b})"
    else:
        typ = "?"
    nodes.append((s,a,b,typ))
    print(f"  node s={s}: t_{s-1}={a} -> t_{s}={b}   [{typ}]")
print()
# The ChainDimSplit per node: drop the complement units at the active edge. For the achiever cascade
# the recursion only branches/steps at DROPS; pass-throughs are gauge (absorbed). So the RECURSION
# steps are the C5/C1 nodes; C2 nodes are gauge.
print("ChainDimSplit recursion steps (the non-gauge nodes — where ΣM drops):")
drops=[(s,a,b,typ) for (s,a,b,typ) in nodes if a>b]
for (s,a,b,typ) in drops:
    print(f"  step at node s={s}: ΣM drops by 2·{a-b}={2*(a-b)}  [{typ}]")
print()
print(f"TOTAL recursion steps (drops): {len(drops)}; C2 gauge nodes: {len(nodes)-len(drops)}")
print(f"  The achiever leaf's codim-list accumulates one divisor per drop step (appendDivisor).")

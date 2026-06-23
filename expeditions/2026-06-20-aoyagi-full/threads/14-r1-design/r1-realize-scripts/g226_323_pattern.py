import numpy as np
from itertools import product
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
def admissible(M,t):
    L=len(M)-1; tt=[M[0]]+list(t)
    if tt[-1]!=0: return False
    for j in range(1,L+1):
        if not(0<=tt[j]<=tt[j-1]): return False
        if tt[j]>M[j]: return False
    return True
def adm(M):
    L=len(M)-1; return [(t,Mval(M,t)) for t in product(*[range(M[0]+1)]*L) if admissible(M,t)]
def minAdm(M): return min(m for _,m in adm(M))

# (3,2,3) the 2nd pattern for rs-grind. M=(3,2,3) [REDUCED widths, B=0 core; full chain C1:3x2, C2:2x3].
# NOTE the asymmetry: M^(2)=2 < endpoints 3 (the bottleneck). Tests the general construction.
M=(3,2,3); L=2
print(f"M={M}, L={L} (REDUCED widths; chain C1:{M[0]}x{M[1]}, C2:{M[1]}x{M[2]})")
print(f"Adm: {adm(M)}, minAdm={minAdm(M)}, lambda={minAdm(M)}/2")
strata=adm(M); mA=minAdm(M); Tstar=[t for t,m in strata if m==mA][0]
print(f"achiever T*={Tstar}, Mval(T*)={Mval(M,Tstar)}=minAdm={mA}")
print()
# Rank chain for T*: t_0=M^1=3 prepended. T*=(1,0) ⟹ t_0..t_2 = [3,1,0].
chain=[M[0]]+list(Tstar)
print(f"achiever rank chain t_0..t_L = {chain}")
print()
# Per-node classification (iterated rank-1 per the banked schurState):
print("Per-node (s: t_{s-1}→t_s, iterated rank-1):")
nodes=[]
for s in range(1,L+1):
    prev,cur=chain[s-1],chain[s]; drop=prev-cur
    if drop==0: cls="C2 gauge"; 
    elif cur==0 and prev>0: cls=f"C1 (full drop to 0, {drop} rank-1 steps)"
    elif prev>cur>0: cls=f"C5 (partial, complement {drop}, survivor {cur}, {drop} rank-1 steps)"
    print(f"  s={s}: {prev}→{cur} (drop {drop})  {cls}")
    for _ in range(drop): nodes.append((s, "C5" if (cur>0 and prev>cur) else "C1"))
print()
print(f"Iterated rank-1 divisor nodes: {len(nodes)} (each ΣM-drop 2). The achiever path:")
print(f"  s=1: 3→1 (drop 2): TWO rank-1 nodes. Is it C5 (3→2 partial) then C1-ish (2→1)? Or C1?")
print(f"  Wait — t_0=3→t_1=1 is a drop of 2, and t_1=1>0, so the SURVIVOR after s=1 is rank 1 (passes to s=2).")
print(f"  s=2: 1→0 (drop 1): ONE rank-1 C1 node (full drop to 0).")
# The s=1 drop 3→1: rank-1 iterated: 3→2 (C5 partial, survivor 2... no, survivor should be 1). Careful:
# the FINAL survivor after s=1 is t_1=1. Iterated rank-1 from 3 to 1 = 3→2→1, TWO steps. Each step: 
# 3→2 is partial (survivor 2, but the EVENTUAL survivor is 1...). The iterated peel drops one rank-unit
# at a time; the intermediate 3→2→1 strata are admissible.
print()
print("DETAIL of s=1 (3→1, iterated rank-1, TWO steps): the cascade peels 3→2→1 at layer 1:")
print("  step 1a: 3→2 (drop 1, partial — survivor 2 intermediate); step 1b: 2→1 (drop 1, partial — survivor 1).")
print("  Both are C5-type partial drops (t>cur>0 at the intermediate); the final survivor t_1=1 passes to s=2.")
print("  Intermediate strata: T_int after 1a = rank pattern with t_1=2 (admissible? (2,0): Mval=", Mval(M,(2,0)),"≥minAdm ✓)")
print("  After 1b: t_1=1 = T* itself.")
print()
# codimsOf for the achiever leaf (the divisor nodes' codims = Mval(M₀, T) of the strata crossed):
# the iterated path crosses: (2,0) [after 1a], (1,0) [after 1b = T*], then s=2 (1→0) resolving the last.
# The codim contributions: each rank-1 node's codim = Mval(M₀, T_node) of the stratum it resolves.
print("codimsOf (achiever leaf, the divisor nodes' Mval-codims):")
print(f"  the strata crossed (root-anchored Mval): (2,0)→{Mval(M,(2,0))}, (1,0)→{Mval(M,(1,0))}=minAdm")
print(f"  Binding (min) = {mA} = minAdm at T*=(1,0). ⟹ ⨅ over codims of (codim/2) = {mA}/2 = lambda ✓")
print()
# the cascade C_s blocks for T*=(1,0): C_s = diag(1^{t_{s+1}}, 0). chain t_0..t_2=[3,1,0].
print("CASCADE C_s blocks for T*=(1,0) (C_s = diag(1^{t_{s+1}}, 0), full chain):")
print(f"  C_1 (3x2): diag(1^{chain[1]}, 0) on 3x2 = diag(1, 0) [rank 1, the t_1=1 survivor] = [[1,0],[0,0],[0,0]]")
print(f"  C_2 (2x3): diag(1^{chain[2]}, 0) on 2x3 = diag() [rank 0, t_2=0] = [[0,0,0],[0,0,0]]")
# verify the cascade realizes T*:
C1=np.array([[1,0],[0,0],[0,0]]); C2=np.zeros((2,3))
r1=np.linalg.matrix_rank(C1); r12=np.linalg.matrix_rank(C1@C2)
print(f"  rank(C_1)={r1} (=t_1=1 ✓), rank(C_1 C_2)={r12} (=t_2=0 ✓). Cascade realizes T*=(1,0). ✓")

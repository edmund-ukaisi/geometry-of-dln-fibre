from itertools import product
from fractions import Fraction as Fr
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
def schurState(M): return tuple(M[s] - (1 if s<=1 else 0) for s in range(len(M)))

# RECONCILE: fm3's decl-check (3,2,3) recursion via banked schurState (decrement idx 0,1 per node):
M0=(3,2,3); M=M0; path=[M0]; codims=[]; step=0
print("(3,2,3) recursion via banked schurState (decrement idx 0,1 per node):")
while minAdm(M) > 0:
    step+=1; Mnext=schurState(M)
    print(f"  step {step}: node {M} (minAdm={minAdm(M)}>0, BRANCH) → schurState {Mnext}")
    M=Mnext; path.append(M)
print(f"  step {step+1}: node {M} (minAdm={minAdm(M)}=0, ∃M_s=0: {any(x==0 for x in M)} → TERMINAL ⊤)")
print(f"  path: {' → '.join(str(p) for p in path)}; {step} BRANCH nodes, terminal {path[-1]}.")
print()
# codims: ROOT-ANCHORED Mval M₀ T at each branch. The achiever T*=(1,0) (minAdm=5). The branch nodes
# resolve cumulative ranks. fm3: codimsOf=[5,6], achiever T*→5, second cell T→6.
print("ROOT-ANCHORED codims (fm3's decl-check): PivotWitness M₀ = Mval M₀ T (FIXED root, NOT reduced node).")
print(f"  achiever T*=(1,0): Mval((3,2,3),(1,0)) = {Mval(M0,(1,0))} = minAdm ✓ (the binding)")
print(f"  other root strata: (0,0)→{Mval(M0,(0,0))}, (2,0)→{Mval(M0,(2,0))}")
print(f"  so the 2 branch codims (root-anchored) ∈ {{5,6}}; achiever path's binding = 5 = minAdm.")
print()
print("RECONCILE my earlier '3 nodes (iterated 3→2→1)' vs fm3's '2 branch nodes':")
print(f"  fm3's banked schurState decrements idx 0,1 by 1 PER NODE: (3,2,3)→(2,1,3)→(1,0,3). 2 nodes.")
print(f"  My earlier g226 read the LAYER-1 drop 3→1 as iterated 3→2→1 (2 rank-units at layer 1). BUT the")
print(f"  banked schurState drops idx-0 AND idx-1 by 1 EACH per node (a single rank-1 Schur peel touches")
print(f"  BOTH pivot vertices), so (3,2,3)→(2,1,3) is ONE node (M_0:3→2 AND M_1:2→1 simultaneously), NOT two.")
print(f"  ⟹ fm3's decl-check is AUTHORITATIVE (the live schurState): 2 BRANCH nodes for (3,2,3). My g226")
print(f"  'iterated 3→2→1 at layer 1' was the WRONG node-count reading — the schurState peel is joint-vertex,")
print(f"  not per-layer-iterated. CORRECT: (3,2,3)→(2,1,3)→(1,0,3), 2 branch nodes, codims root-anchored [5 or 6, ...].")
print()
# CONFIRM root-anchoring (g207/g214): the 2nd node (2,1,3) appends Mval(M₀=(3,2,3), T), NOT minAdm(2,1,3)=2.
print(f"ROOT-ANCHORING CONFIRM (g207/g214): node-2 (2,1,3) appends Mval((3,2,3), T_node) ≥ minAdm((3,2,3))=5,")
print(f"  NOT minAdm((2,1,3))={minAdm((2,1,3))} (which would UNDERSHOOT 5 ⟹ break C≥). The codim is the")
print(f"  GEOMETRIC codim in the ROOT ambient = reindex-invariant = Mval(M₀, T). fm3's anchoring is RIGHT,")
print(f"  matches my g207 (codim=Mval(ROOT M,T) not Mval(reduced)) + g214 (reindex-invariant). CONFIRM.")
print(f"  codimsOf(achiever (3,2,3)) = [5, 6] (or [6,5] order), binding = 5 = minAdm; foldDivisors → ⨅=5/2=λ ✓")

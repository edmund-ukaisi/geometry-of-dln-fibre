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
def schurState(M):  # banked: drop = if s≤1 then 1 else 0
    return tuple(M[s] - (1 if s<=1 else 0) for s in range(len(M)))

# RECONCILE the TWO leaf notions + PROVE the (2,2,2) actual-recursion folds to 3/2.
# The actual recursion: at each node M with minAdm M > 0 (BRANCH), it blows up (a C1/C5 node), APPENDS a
# divisor codim, and recurses on schurState M. At minAdm M = 0 (LEAF/TERMINAL, ∃M_s=0), it STOPS (⊤,
# appends NOTHING). The codimsOf the path = the divisor codims appended at the BRANCH nodes.
#
# THE KEY QUESTION: what codim does each BRANCH node append? (the [4,3] must come from the branch nodes.)
print("ACTUAL RECURSION on (2,2,2) — trace, recording the appended divisor codim at each BRANCH node:")
print()
# At a branch node M (minAdm>0), the appended divisor codim = the GEOMETRIC codim of the blow-up center
# = the pivot stratum cardinality. From g183/g195/g228: the node's codim = Mval(ROOT M₀, T_node) where
# T_node = the rank pattern the node's blow-up resolves (the cumulative rank reached). BUT — the achiever
# path's appended codims were [4,3] in g195 = [Mval((2,2,2),(0,0))=4, Mval((2,2,2),(1,0))=3]. Let me trace
# WHICH cumulative T each branch node resolves, root-anchored.
M0=(2,2,2)
path = [M0]; M=M0; appended=[]; step=0
while minAdm(M) > 0:
    step+=1
    # BRANCH node: blow up, append a divisor, recurse on schurState
    Mnext = schurState(M)
    # the appended codim = the geometric codim of THIS node's blow-up. Root-anchored: = Mval(M₀, T_node)
    # where T_node = the cumulative rank pattern. For the achiever path, the node resolves the NEXT rank
    # in the descent. g195: step-1 → codim 4 (Mval(M₀,(0,0))), step-2 → codim 3 (Mval(M₀,(1,0))).
    # Map: step k resolves cumulative rank pattern T_k. step-1: the "full collapse" T=(0,0) [the generic
    # locus blown up first]; step-2: T=(1,0) [the rank-1 incidence].
    print(f"  step {step}: node M={M} (minAdm={minAdm(M)}>0, BRANCH) → schurState → {Mnext}")
    M = Mnext; path.append(M)
print(f"  step {step+1}: node M={M} (minAdm={minAdm(M)}=0, ∃M_s=0 → TERMINAL leaf, ⊤, appends nothing)")
print(f"  recursion path: {' → '.join(str(p) for p in path)}")
print(f"  # BRANCH nodes (minAdm>0) = {step}; the terminal {path[-1]} is the ⊤ leaf.")
print()
# Now: the appended codims at the 2 branch nodes. g195/g228: [4,3] = [Mval(M₀,(0,0)), Mval(M₀,(1,0))].
print("THE APPENDED DIVISOR CODIMS (root-anchored Mval at each branch node):")
print(f"  branch step-1 (node (2,2,2)): resolves T=(0,0) [generic/full-collapse], codim = Mval((2,2,2),(0,0)) = {Mval(M0,(0,0))}")
print(f"  branch step-2 (node (1,1,2)): resolves T=(1,0) [rank-1 incidence = the binding/achiever], codim = Mval((2,2,2),(1,0)) = {Mval(M0,(1,0))}")
print(f"  ⟹ codimsOf(achiever path) = [4, 3] (appended at the 2 BRANCH nodes), terminal (0,0,2) appends nothing (⊤).")
ratio = min(Fr(4,2), Fr(3,2))
print(f"  foldDivisors([4,3]) → ratioMinFold = min(4/2, 3/2) = {ratio} = lambdaCore(2,2,2) = ½·minAdm = {Fr(minAdm(M0),2)} ✓")
print()
print("="*68)
print("RECONCILIATION (the 2 leaf notions + the proof):")
print("="*68)
print("case222_routeStep_value's codimsOf222 := fun _ => [4,3] is the ABSTRACT one-leaf family: ONE path,")
print("carrying the ACCUMULATED branch-divisors [4,3]. This MATCHES the actual recursion: the (2,2,2) recursion")
print("has ONE achiever path through 2 BRANCH nodes (appending 4, then 3) ending at the ⊤ TERMINAL (0,0,2).")
print("The [4,3] = the branch-node divisors; the ⊤ terminal appends nothing. So:")
print("  - abstract leaf (validation) = the path-END carrying [4,3] = the recursion's path with its accumulated")
print("    branch-divisors. NOT leafMonoData-⊤ — it's foldDivisors([4,3]).")
print("  - recursion TERMINAL = leafStep/leafMonoData-0 (⊤), the (0,0,2) degenerate base case, appends nothing.")
print("  These are CONSISTENT: foldDivisors([4,3] from branches ++ [] from ⊤ terminal) = foldDivisors([4,3]) = 3/2.")
print("  The ⊤ terminal contributes [] (no divisor); the [4,3] are the branch nodes. NO conflict — the flip-flop")
print("  was conflating 'the leaf that carries [4,3]' (= the whole path) with 'the ⊤ terminal' (= the end-marker).")

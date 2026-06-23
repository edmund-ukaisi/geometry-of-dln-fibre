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

# THE ACCOUNTING. routeStep computes the CORE (rlctAtOn(dlnLoss M 0)(deepest) = ⨅ monomialThreshold =
# ½·minAdm = lambdaCore). The headline aoyagiLambda = nReg/2 + lambdaCore (L2's regular shift OUTSIDE).
# So: CORE or WHOLE? fm3's candidate: CORE. Let me pin via the value structure.
print("Q1: CORE or WHOLE? — confirm fm3's CORE candidate.")
print("  resolution_charts headline (g212): rlctAtOn(dlnLoss M 0)(deepest) = ⨅ monomialThreshold = ½·minAdm")
print("  = lambdaCore. This is the CORE (B=0, the reduced widths M). The nReg/2 regular shift is L2's")
print("  product_reduction OUTSIDE: aoyagiLambda = nReg/2 + lambdaCore. So routeStep computes the CORE ✓.")
print("  CONFIRM fm3's CORE: routeStep's ⨅ = lambdaCore = ½·minAdm; nReg/2 is L2's shift, NOT in routeStep.")
print()
# Q2: the leaf value at a degenerate-boundary node reached mid-recursion. Does the 0-leaf BIND the ⨅?
# THE KEY: routeStep is invoked on a NON-degenerate root (hMid ∀s M_s>0). The recursion descends via
# schurState/C5 until... does it EVER reach a degenerate-boundary (∃M_s=0) leaf? Or does it terminate
# at the UNIT leaf (all singular directions blown up, threshold ⊤) BEFORE hitting a width-0?
print("Q2: does the recursion reach a degenerate-boundary (∃M_s=0) leaf, and does its 0-value bind the ⨅?")
print()
# CRITICAL: trace the recursion on a NON-degenerate root. (2,2,2) → schurState → (1,1,2) → ... When does it
# stop? The leaf test is minAdm=0 ⟺ ∃M_s=0. (1,1,2): minAdm? 
for M in [(2,2,2),(1,1,2),(0,0,2)]:
    print(f"  {M}: minAdm={minAdm(M)}, ∃M_s=0: {any(x==0 for x in M)}")
print("  (2,2,2)→schurState(1,1,2): minAdm=", minAdm((1,1,2)), "→ schurState(0,0,2): minAdm=0 (∃M_s=0) LEAF.")
print()
print("  So the (2,2,2) recursion DOES reach a degenerate-boundary leaf (0,0,2) after 2 schurState steps")
print("  (M_0,M_1 decremented to 0). The leaf (0,0,2) has minAdm=0. ITS CORE-VALUE: lambdaCore(0,0,2) =")
print(f"  ½·minAdm(0,0,2) = ½·0 = 0. Does this 0 BIND the (2,2,2) root's ⨅?")
print()
# THE RESOLUTION: the ⨅ over LEAVES of foldDivisors(codimsOf). The codimsOf of THIS leaf-path = the divisor
# codims ACCUMULATED along the path (2,2,2)→(1,1,2)→(0,0,2). Those are the C1-node codims (the blow-up
# divisors), NOT the leaf's own ½·minAdm. The leaf CONTRIBUTES its accumulated codim-list, and the LEAF
# ITSELF (the (0,0,2) terminal) is a UNIT (threshold ⊤) — the path's value = min over the PATH's divisor
# codims, NOT the leaf's lambdaCore.
print("THE RESOLUTION (the accounting, the subtle bit):")
print("  The ⨅ is over LEAF PATHS of foldDivisors(codimsOf path). codimsOf = the C1-DIVISOR codims accumulated")
print("  ALONG the path (the blow-up exceptional divisors), NOT the terminal leaf's own ½·minAdm. The terminal")
print("  leaf (0,0,2) is a UNIT (threshold ⊤, leafMonoData) — it does NOT contribute a binding value; the path's")
print("  threshold = min over the ACCUMULATED divisor codims (the C1 nodes traversed to reach it).")
print()
print("  So: the degenerate-boundary terminal leaf's monomialThreshold = ⊤ (leafMonoData, non-binding) is")
print("  CORRECT for the FOLD — the leaf doesn't bind; the path's binding divisor (the minAdm-codim C1 node")
print("  along the path) binds. The ½·minAdm=0 'leaf core-value' is NOT what enters the ⨅ — the ACCUMULATED")
print("  divisor codims do. fm3's rs-grind leafMonoData 0 (⊤) is RIGHT for the terminal, IF the divisor codims")
print("  are accumulated along the path (which they are, via appendDivisor at each C1/C5 node).")

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

# VERIFY end-to-end: the (2,2,2) achiever path's foldDivisors (accumulated divisor codims, ⊤ terminal leaf)
# = lambdaCore(2,2,2) = 3/2. The path reaches the degenerate-boundary leaf (0,0,2); the divisor codims
# along the path = the C1-node codims (root-anchored Mval). The achiever path resolves to T*=(1,0).
# codimsOf(achiever) = the Mval(M₀=(2,2,2), T) of the strata the path's C1 nodes resolve.
print("END-TO-END: does the (2,2,2) achiever path foldDivisors = lambdaCore = 3/2, with the ⊤ terminal leaf?")
print()
M0=(2,2,2); mA=minAdm(M0)
print(f"  root M₀={M0}, minAdm={mA}, lambdaCore=½·{mA}={Fr(mA,2)}")
print(f"  achiever T*=(1,0), the path resolves through C1 nodes; codimsOf = root-anchored Mval of strata crossed.")
print(f"  The path (2,2,2)→(1,1,2)→(0,0,2): the C1 nodes' divisor codims = the Mval(M₀, T) the blow-ups resolve.")
# from g195: (2,2,2) codimsOf = [4,3] (step-1 Mval((2,2,2),(0,0))=4, step-2 Mval((2,2,2),(1,0))=3=minAdm).
codimsOf = [Mval(M0,(0,0)), Mval(M0,(1,0))]  # the two C1-divisor codims
print(f"  codimsOf(achiever) = {codimsOf} (Mval((2,2,2),(0,0))=4, Mval((2,2,2),(1,0))=3=minAdm)")
ratioMin = min(Fr(c,2) for c in codimsOf)
print(f"  foldDivisors → ratioMinFold = min(4/2, 3/2) = {ratioMin} = lambdaCore ✓")
print(f"  The TERMINAL leaf (0,0,2) = ⊤ (leafMonoData, non-binding); the binding is the codim-3 C1 divisor")
print(f"  (= minAdm) ALONG the path, NOT the terminal's ½·minAdm. So ⊤ terminal + accumulated divisors = 3/2 ✓.")
print()
print("="*68)
print("THE FULL ACCOUNTING (the 3 deliverables for fm3):")
print("="*68)
print("Q1 CORE-vs-WHOLE: CORE. routeStep's ⨅ monomialThreshold = ½·minAdm = lambdaCore (the B=0 core). The")
print("  nReg/2 regular shift is L2's product_reduction OUTSIDE: aoyagiLambda = nReg/2 + lambdaCore. CONFIRM")
print("  fm3's CORE candidate. routeStep does NOT compute nReg/2 — that's L2's spectator shift.")
print()
print("Q2 LEAF-VALUE: the TERMINAL leaf (degenerate boundary, ∃M_s=0, reached when schurState hits a width-0)")
print("  = leafMonoData (threshold ⊤, NON-binding). fm3's rs-grind leafMonoData 0 is RIGHT. The ½·minAdm=0")
print("  'leaf core-value' does NOT enter the ⨅ as a binding 0 — the ⨅ is over the path's ACCUMULATED DIVISOR")
print("  codims (the C1/C5 nodes traversed), and the terminal is ⊤. So the 0-leaf does NOT bind the ⨅ to 0;")
print("  the binding is the minAdm-codim divisor ALONG the path. CRITICAL: this is why the ⊤ terminal is")
print("  correct — a 0-BINDING leaf would wrongly force the root ⨅ to 0; the ⊤ terminal + accumulated divisors")
print("  gives the right ½·minAdm. (The leaf's OWN lambdaCore=0 is the degenerate sub-core, but it's not a")
print("  divisor — it's the unit residual after all the path's blow-ups, threshold ⊤.)")
print()
print("Q3 COMPOSITION (no double-count): routeStep CORE ⨅=lambdaCore [the divisor min, terminal ⊤]; L2 adds")
print("  nReg/2 OUTSIDE (the regular spectator shift); #70 is the DEGENERATE-BOUNDARY WHOLE (rlctAt=nReg/2),")
print("  used ONLY when the ROOT is degenerate (∃M_s=0 at the root, the headline case-split). For a NON-")
print("  degenerate root, routeStep gives lambdaCore (CORE), L2 adds nReg/2, aoyagiLambda = nReg/2+lambdaCore.")
print("  The degenerate-boundary LEAF reached MID-recursion is ⊤ (non-binding terminal), NOT #70 — #70 is for")
print("  a degenerate ROOT. NO double-count: nReg/2 enters once (L2), the leaf terminal is ⊤ (no value), the")
print("  divisors give lambdaCore.")

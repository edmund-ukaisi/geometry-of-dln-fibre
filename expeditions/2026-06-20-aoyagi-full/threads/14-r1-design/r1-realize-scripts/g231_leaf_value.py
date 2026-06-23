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

# EXACTNESS — the value-consistency of the leaf test (the "too-weak/too-strong" concern):
# The value foldFamily: lambdaCore M = ½·minAdm M. A LEAF contributes monomialThreshold = ⊤ (no binding
# divisor — leafMonoData k≡0, threshold ⊤). For the recursion to give the right value, stopping at a
# minAdm=0 node must be CORRECT: the node's lambdaCore = ½·0 = 0, and a leaf (threshold ⊤) at value 0...
# wait — lambdaCore = ½·minAdm = 0 when minAdm=0. The leaf's CONTRIBUTION to the ⨅ must be consistent.
print("VALUE-CONSISTENCY of the leaf test (the EXACTNESS check):")
print("  lambdaCore M = ½·minAdm M. At a leaf (minAdm=0): lambdaCore = 0.")
print()
# The leaf's rlct/threshold: a minAdm=0 node is a UNIT core (the codim-0 stratum is the generic point,
# the loss is a unit there) ⟹ its rlctAtOn contribution... the cover ⨅ over leaves. A minAdm=0 leaf has
# the MINIMAL stratum codim 0 ⟹ the binding divisor codim 0 ⟹ ratio 0/2 = 0 ⟹ threshold... 0? or ⊤?
print("  THE SUBTLETY: minAdm=0 means the binding stratum has codim 0. In the cover, codim-0 = NO blow-up")
print("  (the stratum is the generic point, already smooth/unit). So the leaf has NO exceptional divisor")
print("  ⟹ codimsOf = [] (empty) ⟹ foldDivisors [] = leafMonoData ⟹ monomialThreshold = ⊤ (the unit leaf).")
print("  BUT lambdaCore = ½·minAdm = ½·0 = 0. ⨅ over leaves... if the leaf threshold is ⊤, it doesn't bind,")
print("  and the ⨅ = 0 must come from ELSEWHERE. CONTRADICTION? Let me check what minAdm=0 means for the VALUE.")
print()
# Resolve: when minAdm=0, lambdaCore=0. The RLCT of dlnLoss M 0 at the deepest = lambdaCore = 0?? rlct=0
# means the loss is... NOT integrable to any negative power = a NON-singular / the function doesn't vanish?
# No — rlct measures the singularity. lambdaCore=0 is the MOST singular (rlct 0). Hmm. Let me reconsider:
# is minAdm=0 actually a LEAF (recursion stops, value 0) or does it mean something degenerate?
print("RECONSIDER: minAdm=0 ⟹ lambdaCore = 0. What IS dlnLoss M 0 when minAdm=0? Take (2,2,0): M_2=0, so")
print("the LAST width is 0 — the chain ends in a width-0 layer. dlnLoss (2,2,0) 0 = ‖C_1 C_2‖² with C_2 a")
print("2×0 matrix = the empty matrix ⟹ C_1 C_2 = the 2×0 product = 0 (vacuous) ⟹ dlnLoss ≡ 0.")
print("  rlctAtOn(0) = ⊤ (the team's sSup convention — |0|^{-c} integrable all c). So lambdaCore should be")
print("  ⊤, NOT 0! But ½·minAdm = ½·0 = 0 ≠ ⊤. So minAdm=0 ⟹ the DEGENERATE BOUNDARY (some M_s=0), where")
print("  lambdaCore (the ½·minAdm formula) does NOT equal rlctAtOn(dlnLoss M 0)=⊤ — the #70 ⊤-trap!")
print()
# So minAdm=0 with some M_s=0 is the DEGENERATE BOUNDARY (#70), NOT a clean leaf of the core recursion.
# But the recursion is on the CORE (B=0); the degenerate boundary is handled SEPARATELY (#70). So:
print("KEY: split the minAdm=0 cases by WHETHER some M_s=0:")
for M in [(2,2,0),(0,0,2),(2,0,2),(1,1,0),(2,0,0),(0,1,0),(1,0,1),(0,0,0)]:
    hasM0 = any(x==0 for x in M)
    print(f"  M={M}: minAdm=0, some M_s=0: {hasM0}  ⟹ {'DEGENERATE BOUNDARY (#70, ⊤-trap, handle separately)' if hasM0 else 'genuine interior leaf'}")
# Are there minAdm=0 nodes with ALL M_s≥1 (a genuine interior leaf)?
print()
print("Are there minAdm=0 nodes with ALL M_s ≥ 1 (genuine interior leaf, not degenerate boundary)?")
found=[]
for M in product(range(1,4),repeat=3):
    if minAdm(M)==0: found.append(M)
for M in product(range(1,4),repeat=4):
    if minAdm(M)==0: found.append(M)
print(f"  minAdm=0 with all M_s≥1 (L=2,3): {found if found else 'NONE'}")

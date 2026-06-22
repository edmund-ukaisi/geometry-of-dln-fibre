import sympy as sp, itertools
# CRITICAL scope check: is resolution_charts on the CORE M=H-r (so (2,2,2),r=1 → M=(1,1,1) trivial),
# OR on something where (2,2,2) gives a nontrivial tree? Re-read the Skeleton statement intent.
# resolution_charts M : rlctAtOn (dlnLoss M 0) 0 = ⨅ monomialThreshold. The dlnLoss M 0 is ‖∏C‖² with
# C the factors of widths M. For M=(1,1,1): C=(c1,c2), ∏C=c1·c2 (scalars), dlnLoss=(c1c2)². 
c1,c2 = sp.symbols('c1 c2', real=True)
core111 = (c1*c2)**2
print("M=(1,1,1): dlnLoss = (c1·c2)² — monomial, normal-crossing, rlctAtOn=1/2, ι trivial (2 axes).")
# BUT: is the (2,2,2) HEADLINE rlct=3/2 the CORE rlct or the FULL rlct? aoyagiLambda(2,2,2) 0 = 3/2 with r=0!
# r=0 means M=H-r=H=(2,2,2), NOT (1,1,1). Let me recheck: the AxCheck headline is rlctAt(dlnLoss H222) deepest = 3/2.
# For r=0 the core M=(2,2,2) and dlnLoss (2,2,2) 0 = ‖A1·A2‖² (2x2 matrices). THAT's the nontrivial core.
A1=sp.Matrix(2,2,sp.symbols('a0:4')); A2=sp.Matrix(2,2,sp.symbols('b0:4'))
P=sp.expand(A1*A2); core222=sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
print("M=(2,2,2), r=0: dlnLoss=‖A1·A2‖² (2x2) — NONTRIVIAL core, the 24-leaf tree IS its resolution.")
print("  ⟹ I was WRONG above: resolution_charts is on M directly (the reduced widths, r the deepest rank).")
print("  For the (2,2,2) HEADLINE r=0: M=(2,2,2), core=‖A1A2‖², the 24-leaf tree is resolution_charts' ι. ✓")
print("  The r=1 case (M=(1,1,1)) is a DIFFERENT, smaller instance (the reduced core after r=1).")
# So the (2,2,2) banked tree IS the template for M=(2,2,2). Good — fm3's map is directly on-point.
# Verify lambdaCore(2,2,2) = 3/2:
def admBound(M,j,L): return min(M[0],M[1]) if j==0 else M[j+1]
def adm_cone(M):
    L=len(M)-1; cone=[]
    for T in itertools.product(*[range(admBound(M,j,L)+1) for j in range(L)]):
        if all(T[j]<=T[i] for i in range(L) for j in range(L) if i<=j) and T[L-1]==0: cone.append(T)
    return cone,L
def Mval(M,T,L):
    tP=lambda j: M[0] if j==0 else T[j-1]
    return sum((tP(j)-T[j])*(M[j+1]-T[j]) for j in range(L))
cone,L=adm_cone((2,2,2)); mn=min(Mval((2,2,2),T,L) for T in cone)
print(f"  lambdaCore(2,2,2) = ½·minAdm Mval = ½·{mn} = {sp.Rational(mn,2)} ✓ (matches the 24-leaf ⨅=3/2)")
print()
print("CORRECTION to my scope note: resolution_charts M is on the FULL reduced-width core ‖∏C‖² for")
print("widths M. The (2,2,2) 24-leaf banked tree IS resolution_charts' ι for M=(2,2,2) — fm3's map is")
print("the direct template. The C1/C2/C4/C5 recursion GENERALIZES that tree to arbitrary M.")

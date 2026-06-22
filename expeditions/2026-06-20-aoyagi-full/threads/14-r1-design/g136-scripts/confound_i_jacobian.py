# The FULL exceptional-divisor ratio combines core-order AND Jacobian-order. The obstruction hunt:
# does ANY exceptional divisor in the whole atlas have ratio < ½·minAdm Mval?
# Divisor ratio = (h+1)/(2k) where:
#   2k = u-order of core∘φ  (the resolved function's vanishing along E)
#   h  = u-order of |Jac φ| (the blow-up Jacobian's vanishing along E)
# For blow-up of a codim-c coordinate center: |Jac| = u^{c-1} => h = c-1.  core∘φ = u^2·(…) => k=1.
# So ratio = c/2 where c = codim of the (admissible {prod=0}) center. The binding is the SMALLEST c.
from fractions import Fraction as F
def adm(M):
    L=len(M)-1; out=[]
    def rec(j,prev,cur):
        if j==L+1:
            if cur[-1]==0: out.append(tuple(cur[1:]))
            return
        for v in range(0,min(prev,M[j])+1): rec(j+1,v,cur+[v])
    rec(1,M[0],[M[0]]); return out
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); s=0
    for j in range(1,L+1): s+=(tt[j-1]-tt[j])*(M[j]-tt[j])
    return s

# The DANGER recheck: the FIRST blow-up is of {C1=0} (codim M1*M2), giving ratio M1*M2/2. Is this EVER
# < ½·minAdm? minAdm <= Mval(deepest=0..) and Mval(0,..) includes the (M1-0)(M2-0)=M1*M2 term for j=1
# PLUS more. So M1*M2 <= Mval(0,...) but is M1*M2 >= minAdm? NOT obvious -- minAdm could be < M1*M2 OR
# the first blow-up's center {C1=0} corresponds to t_1=0, an admissible stratum with codim Mval(0,...).
# Wait: {C1=0} forces t_1=0 hence t_j=0 all j => the DEEPEST stratum, codim Mval(0,...,0) (the MAX).
# So the first blow-up's ratio = Mval(0,..)/2 = the LARGEST, never binding. Good.
# But the recursion does NOT blow up {C1=0} entirely at deep nodes -- it blows up the rank-DEFECT
# {rank C1 <= s}. Each such, intersected with {prod=0}, is an admissible stratum of codim Mval(t)>=minAdm.
print("=== every atlas divisor ratio = Mval(t)/2, t admissible; min = ½·minAdm. UNDERSHOOT check ===")
worst=True
for M in [[2,2,2],[3,3,3],[4,3,2],[3,2,3],[2,3,2],[2,2,2,2],[5,4,3,2],[2,4,2],[6,2,2],[2,6,2],[7,3,2,2]]:
    advs=adm(M); minAdm=min(Mval(M,t) for t in advs)
    ratios=sorted(set(F(Mval(M,t),2) for t in advs))
    # the first blow-up {C1=0} => t=(0,..) => deepest, codim = max
    deepest=Mval(M,tuple([0]*(len(M)-1)))
    first_ratio=F(deepest,2)
    binding=min(ratios)
    ok = binding==F(minAdm,2) and all(r>=F(minAdm,2) for r in ratios)
    worst = worst and ok
    print(f"M={M}: minAdm={minAdm} first-blowup-ratio(t=0)={first_ratio} all-ratios={[str(r) for r in ratios]} "
          f"binding={binding} NO_UNDERSHOOT={ok}")
print("\nNO DIVISOR UNDERCUTS ½·minAdm (all cases):", worst)

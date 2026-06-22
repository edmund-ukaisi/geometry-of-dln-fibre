# CONFOUND (i) SHARPEST: the first-factor blow-up center {rank C1 <= s} is NOT contained in {prod=0}.
# Points with C1 rank-deficient but product nonzero are in this center. Blowing it up creates an
# exceptional divisor. Codim of {rank C1 = s} in the WHOLE space = (M1-s)(M2-s) -- could be SMALLER
# than minAdm Mval => its divisor ratio (M1-s)(M2-s)/2 could UNDERCUT the lower bound!
# This is the genuine undershoot trap: a SPURIOUS divisor from blowing up a non-{prod=0} center.
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

# {rank C1 = s} has codim (M1-s)(M2-s) in C1-space. Compare to minAdm Mval.
print("=== Does blowing up the FIRST FACTOR's rank-defect introduce a divisor UNDER ½·minAdm? ===")
for M in [[2,2,2],[3,3,3],[4,3,2],[3,2,3],[2,3,2],[2,2,2,2],[5,4,3,2],[2,4,2],[6,2,2]]:
    M1,M2=M[0],M[1]
    minAdm=min(Mval(M,t) for t in adm(M))
    # first-factor rank strata s=0..min(M1,M2)-1 (s=full => no blow-up)
    ff_codims={s:(M1-s)*(M2-s) for s in range(min(M1,M2))}
    # the DANGER: a first-factor codim < minAdm
    dangerous={s:c for s,c in ff_codims.items() if c < minAdm}
    print(f"M={M}: minAdm={minAdm} (½·={F(minAdm,2)})  first-factor-rank codims={ff_codims}  "
          f"UNDERSHOOT_RISK={dangerous or 'none'}")

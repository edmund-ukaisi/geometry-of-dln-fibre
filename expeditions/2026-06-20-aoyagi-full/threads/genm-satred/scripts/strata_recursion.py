"""(D) mechanism: the JOINT rank-sector reduction reaches minAdm via the minAdm recursion.
Single-chain per-stratum red_r = a·r/2+(b−r)(ρ−r)/2 (corneradj, = joint_corank S-fixed): min undershoots
ab/2 by (k−1)/2 at k=a+b−ρ≥2. Joint (multi-chain): stratum r ↔ deeper cut u'=u+(b−r), reduce to
redChain u' M (arity−1 IH); min_r[peelCharge(u')+minAdm(redChain u' M)] = minAdm(M) EXACTLY."""
from fractions import Fraction as F
def minAdmRec(M):
    M=list(M);L=len(M)
    if L==1:return 0
    if L==2:return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec([t]+M[2:]) for t in range(min(M[0],M[1])+1))
def single_chain(a,b,rho):  # corneradj red_r, min-over-r
    reds={r:F(a*r,2)+F((b-r)*(rho-r),2) for r in range(b+1)}; return reds,min(reds.values())
def joint(M,u):  # min over strata r ↔ cut u'=u+(b-r) of peelCharge(u')+minAdm(redChain u' M)
    M0,M1,M2,M3=M; b=M1-u; terms={}
    for r in range(b+1):
        up=u+(b-r)
        if up>min(M0,M1): continue
        terms[r]=(up,(M0-up)*(M1-up),minAdmRec([up,M2,M3]),(M0-up)*(M1-up)+minAdmRec([up,M2,M3]))
    return terms,min(v[3] for v in terms.values())
if __name__=="__main__":
    for M,u in [((2,1,2,2),0),((2,2,3,3),0),((4,2,3,4),1),((2,3,4,4),0)]:
        M0,M1,M2,M3=M; a=M0-u; b=M1-u; rho=min(M1,M2,M3); mM=minAdmRec(list(M))
        reds,sc=single_chain(a,b,rho); terms,jt=joint(M,u); k=a+b-rho
        print(f"M={M} u={u} (a={a},b={b},ρ={rho},k={k}): minAdm={mM} ab/2={F(a*b,2)}")
        print(f"  single-chain min={sc} (shortfall {F(a*b,2)-sc}, predicted (k−1)/2={F(max(k-1,0),2)})")
        print(f"  JOINT min-over-strata={jt}  {'REACHES minAdm' if jt==mM else 'UNDERSHOOT'}  strata↔cuts {[(r,v[0]) for r,v in terms.items()]}")

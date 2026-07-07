import numpy as np
rng=np.random.default_rng(1)
# CLAIM (exact up to bounded constants): the per-step integrand (a=1) collapses to
#   J(g,h) ≍ min(g^{-2c'}, C g^{-(2c'-1)} h^{-1}) = g^{-2c'} * min(1, g/h)
#          = g^{1-2c'} / max(g,h)
# and with g=||R_top A2|| = sqrt(P1)  (tail chain (t,M2,..)),
#          max(g,h)^2 ≍ g^2+h^2 = ||R_top A2||^2 + ||r_bot A2||^2 = ||A1 A2||^2 = P2 (FULL product (M1,..,ML))
#   => J ≍ P1^{-(c'-1/2)} * P2^{-1/2}      [a=1; general a: P1^{-(c'-a/2)} P2^{-a/2}]
# Verify g^2+h^2 == ||A1 A2||^2 with A1 = [R_top; r_bot] stacked  (EXACT, both cases):
def frob2(M): return (M**2).sum(axis=(-1,-2))
for name,(mr,mc,nc) in [("(2,2,2,2) t=1: R_top 1x2,r_bot 1x2,A2 2x2",(1,1,2)),
                        ("(3,3,3,3) t=2: R_top 2x3,r_bot 1x3,A2 3x3",(2,1,3))]:
    rtop=rng.uniform(-1,1,(5,mr,nc)); rbot=rng.uniform(-1,1,(5,mc,nc)); A2=rng.uniform(-1,1,(5,nc,nc))
    g2=frob2(rtop@A2); h2=frob2(rbot@A2)
    A1=np.concatenate([rtop,rbot],axis=1)          # stack rows -> full middle factor
    P2=frob2(A1@A2)
    err=np.abs(g2+h2-P2).max()
    print(f"{name}\n   max|g^2+h^2 - ||A1 A2||^2| = {err:.2e}  (0 => P2=full product exactly)")

print("""
=> EXACT per-step identity (a=1):  J ≍ P1^{-(c'-1/2)} · P2^{-1/2}
     P1 = ||R_top·A2||^2  = the REDUCED TAIL CHAIN (t,M2,...,ML) loss
     P2 = ||A1·A2||^2     = the FULL remaining product (M1,...,ML) loss  (the COUPLING factor)
   nested loci: {P2=0} ⊂ {P1=0},  and P2 = P1 + ||r_bot·A2||^2 ≥ P1.
""")

from functools import lru_cache
@lru_cache(None)
def minAdmRec(M):
    L=len(M)-1
    if L==0:return 0
    if L==1:return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

print("RLCT-order bookkeeping at the binding cut (target c* = ½minAdm(M)):")
for M,t in [((2,2,2,2),1),((3,3,3,3),2),((4,4,4,4),3),((2,2,2,3),1),((4,4,2,2),2)]:
    a=(M[0]-t)*(M[1]-t)
    tail=(t,)+M[2:]           # reduced chain P1
    full=M[1:]                # full remaining product P2
    cstar=minAdmRec(M)/2
    s1=cstar-a/2; rl1=minAdmRec(tail)/2       # P1 power vs its RLCT
    s2=a/2;       rl2=minAdmRec(full)/2       # P2 (coupling) power vs its RLCT
    print(f"  M={M} t={t}: a={a}  c*={cstar}")
    print(f"      P1=tail{tail}: s1=c*-a/2={s1}  RLCT(P1)={rl1}   {'P1 BINDS (s1=RLCT)' if abs(s1-rl1)<1e-9 else 'P1 slack'}")
    print(f"      P2=full{full}: s2=a/2={s2}    RLCT(P2)={rl2}   {'P2 SUBORDINATE (s2<RLCT)' if s2<rl2-1e-9 else 'P2 CRITICAL/BINDS'}")

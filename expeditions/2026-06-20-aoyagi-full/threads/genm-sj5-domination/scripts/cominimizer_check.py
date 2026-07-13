"""
Does the BANKED deeper co-minimizer rank rho (minAdm_backPeel_cominimizer_ge:
rho >= (M0-t*)+(M1-t*)-1 at a nondegenerate binding cut t*) already SUPPLY the
deep rank the off-sector mountain needs (rho >= a+b), where the Ky-Fan shell
floor m = min(M1,ML)-j UNDERCOUNTS it?

Off-sector u = t*+j, a = M0-u, b = M1-u.  Then
  a*+b*-1 = (M0-t*)+(M1-t*)-1 = (a+j)+(b+j)-1 = a+b + (2j-1) >= a+b+1   for j>=1.
So rho >= a*+b*-1 => rho >= a+b+1 > a+b  (STRICT) on every off-sector shell.

We (i) recompute the actual co-minimizer set rho of redChain(t*,M) = (t*,M2,...,ML),
(ii) confirm min(rho) >= a*+b*-1 (banked bound is tight/valid), and
(iii) confirm min(rho) >= a+b (mountain-required deep rank) on ALL failing shells.
"""
from functools import lru_cache
from itertools import product

@lru_cache(None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def tailMin(M):            # min of widths from index 1 on (front-peel rank cap for leading width)
    return min(M[1:])

def cominimizers(M):
    """front-peel co-minimizing ranks rho of chain M (leading width M0):
       minAdm(M) = min_{rho<=tailMin} [ M0*rho + minAdm( (M1..) shifted by -rho ) ].
       Return the set of rho attaining the min. Uses the geometric charge = M0*rho + minAdm(tail-rho)
       where minAdm(tail-rho) = cCodim = minAdm of the deeper chain with ranks capped; we realise it
       via the SAME layer recursion on (rho, M2, ..., ML)? No: front-peel charge is
       frontCharge(M,rho) = M0*rho + minAdm( shifted tail ).  We compute minAdm via the peeling rec
       directly by the identity minAdm(M) = min_rho frontCharge; recover argmins by brute force using
       the layer recursion value = the peel min.  For our reduced chains (t*,M2,...,ML) the leading
       width is t*, and rho ranges 0..min(M2,...,ML)."""
    lead=M[0]; tail=M[1:]
    tm=min(tail)
    # frontCharge(rho) = lead*rho + minAdm(tail with generic rank capped at rho)
    # minAdm(tail capped at rho) = minAdm of chain (rho, M3.., ) ??? Use the banked reading:
    # cCodim(tail; rho) = minAdm( (rho,) + tail[1:] ) is NOT right either. We instead use the
    # LAYER recursion: minAdm(M) already = min over first-peel t<=min(M0,M1). The co-minimizing
    # DEEPER rank rho for redChain is the first-peel pivot of redChain itself:
    #   minAdm(redChain) = min_{rho<=min(lead,tail0)} [ (lead-rho)(tail0-rho) + minAdm(rho,tail[1:]) ].
    # That pivot is the rank of A1' (front of the reduced chain), NOT the deep product. The DEEP
    # product rank is captured by the FRONT-PEEL identity's rho (leading-width factorisation).
    # Front-peel identity (banked minAdm_eq_frontPeel): minAdm(M) = min_{rho<=tailMin}[M0*rho + minAdm(tail-rho)]
    # with minAdm(tail-rho) = minAdm applied to tail with its leading generic rank forced <= rho,
    # realised as minAdm( (rho,)+tail[1:] ).  We use THAT.
    best=None; args=[]
    for rho in range(tm+1):
        charge = lead*rho + minAdm((rho,)+tuple(tail[1:]))
        if best is None or charge<best:
            best=charge; args=[rho]
        elif charge==best:
            args.append(rho)
    return best, args

def analyse():
    fails=[]; checked=0
    for Llen in [4,5]:                       # L>=1 (>=4 widths) — where Z_deep is nontrivial
        for M in product(range(2,6),repeat=Llen):
            mA=minAdm(M); ML=M[-1]; M1=M[1]
            binds=[t for t in range(1,min(M[0],M1)+1)
                   if (M[0]-t)*(M1-t)+minAdm((t,)+M[2:])==mA]   # t*>=1 (cert convention)
            for tstar in binds:
                # co-minimizer rho of redChain(t*,M) = (t*, M2,...,ML)
                red=(tstar,)+tuple(M[2:])
                _, rhos = cominimizers(red)
                rho_min=min(rhos)
                astar=M[0]-tstar; bstar=M1-tstar
                for j in range(1,min(M[0]-tstar,M1-tstar)+1):
                    u=tstar+j; a=M[0]-u; b=M1-u
                    if a<1 or b<1: continue
                    m=min(M1,ML)-j                     # Ky-Fan shell floor (S1 cert)
                    cur_fail=(m<a+b)
                    if not cur_fail: continue
                    checked+=1
                    banked_bound=astar+bstar-1         # minAdm_backPeel_cominimizer_ge
                    fails.append(dict(M=M,tstar=tstar,u=u,a=a,b=b,j=j,m=m,
                                      rho_min=rho_min, banked_bound=banked_bound,
                                      rho_ge_bound=(rho_min>=banked_bound),
                                      rho_ge_ab=(rho_min>=a+b),
                                      arith=(astar+bstar-1>=a+b)))
    return fails, checked

fails, checked = analyse()
print("failing off-sector shells (t*>=1, L>=1, w2..5):", checked)
print("banked co-minimizer bound valid (rho_min >= a*+b*-1) on ALL:",
      all(f['rho_ge_bound'] for f in fails))
print("PURE ARITH a*+b*-1 >= a+b on ALL (=> j>=1):", all(f['arith'] for f in fails))
print("=> deep co-minimizer rank supplies a+b (rho_min >= a+b) on ALL:",
      all(f['rho_ge_ab'] for f in fails))
bad=[f for f in fails if not f['rho_ge_ab']]
print("shells where BANKED deep rank does NOT reach a+b:", len(bad))
for f in bad[:10]: print("   ", f)
print("\nsample (M,t*,u,a,b,j | shellFloor m | co-min rho | banked a*+b*-1):")
for f in fails[:12]:
    print("   M=%s t*=%d u=%d a=%d b=%d j=%d | m=%d | rho=%d | bound=%d"
          % (f['M'],f['tstar'],f['u'],f['a'],f['b'],f['j'],f['m'],f['rho_min'],f['banked_bound']))

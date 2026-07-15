"""
CORRECTED deep-stratum codim-with-charge scan (charge A_cor-integral resolved, Codex-confirmed).

Corrected worst charge exponent at rank s=rho-k drop (stratify by rank(A_cor|surv)=b-h):
    gamma_s = max_{ max(0,b-s) <= h <= b }  h*(a+b-s-h)
(my earlier pointwise a*(k-d)_+ was only the h=(b-s)_+ term; gamma_s can be strictly larger).

Codim-with-charge:  C_k = min( u*rho , u*(rho-k) + kappa_k - gamma_{rho-k} ),  kappa_k = CR(deep, rho-k).
BOUNDED iff C_k >= minAdm(M) - a*b for every k=1..rho.

Also verifies Codex's clean proof identities:
  R_h = us + (a-h)(b-h) + h*s = ab + us - gamma_s   (at the maximizing h)
  minAdm(M0,M1,s) <= R_h ; and stratify: minAdm(M) <= kappa_k + minAdm(M0,M1,s).
"""
import itertools
from functools import lru_cache

@lru_cache(maxsize=None)
def CR(widths, s):
    v=tuple(widths)
    if len(v)==2:
        return 0 if s>=min(v) else (v[0]-s)*(v[1]-s)
    vpm1,vp=v[-2],v[-1]; best=None
    for r in range(0,min(vpm1,vp)+1):
        val=(vpm1-r)*(vp-r) + (0 if r<=s else CR(v[:-2]+(r,),s))
        if best is None or val<best: best=val
    return best

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    m0,m1=M[0],M[1]; rest=M[2:]; best=None
    for t in range(0,min(m0,m1)+1):
        val=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or val<best: best=val
    return best

def binding_cut(M):
    m0,m1=M[0],M[1]; rest=M[2:]; best=None; targ=None
    for t in range(0,min(m0,m1)+1):
        val=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or val<best: best=val; targ=t
    return targ, min(m0-targ, m1-targ)

def gamma_s(a,b,s):
    lo=max(0,b-s); hi=b
    return max((h*(a+b-s-h) for h in range(lo,hi+1)), default=0)

def analyze(M,u):
    M0,M1=M[0],M[1]; deep=M[2:]
    a=M0-u; b=M1-u; rho=min(deep); n=deep[-1]
    mA=minAdm(M); target=mA-a*b; urho=u*rho
    recs=[]; worst=None; worst_k=None
    for k in range(1,rho+1):
        s=rho-k; kap=CR(deep,s); gs=gamma_s(a,b,s)
        G=u*s+kap-gs; Cs=min(urho,G)
        recs.append((k,s,kap,gs,G,Cs))
        if worst is None or Cs<worst: worst=Cs; worst_k=k
    return dict(a=a,b=b,rho=rho,n=n,minAdm=mA,target=target,urho=urho,worst=worst,worst_k=worst_k,recs=recs,deep=deep)

def scan(nwidths, Wmax):
    viol=[]; cnt=0; min_slack=None; min_charge_slack=None
    for M in itertools.product(*([range(1,Wmax+1)]*nwidths)):
        tstar,r=binding_cut(M)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            info=analyze(M,u); cnt+=1
            sd=info['worst']-info['target']
            if min_slack is None or sd<min_slack: min_slack=sd
            # charge-stratum min slack (strata where gamma_s>0)
            for (k,s,kap,gs,G,Cs) in info['recs']:
                if gs>0:
                    cslack=min(info['urho'],G)-info['target']
                    if min_charge_slack is None or cslack<min_charge_slack: min_charge_slack=cslack
            if sd<0:
                viol.append((M,u,info,sd))
    return cnt, viol, min_slack, min_charge_slack

def verify_codex_identity(nwidths, Wmax):
    """Check minAdm(M) <= kappa_k + minAdm(M0,M1,s) for all binding cuts & k (the stratification bound)."""
    fails=[]; cnt=0
    for M in itertools.product(*([range(1,Wmax+1)]*nwidths)):
        M0,M1=M[0],M[1]; deep=M[2:]; rho=min(deep)
        tstar,r=binding_cut(M)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            for k in range(1,rho+1):
                s=rho-k; kap=CR(deep,s)
                lhs=minAdm(M); rhs=kap+minAdm((M0,M1,s))
                cnt+=1
                if lhs>rhs: fails.append((M,u,k,s,lhs,rhs))
    return cnt, fails

if __name__=="__main__":
    print("=== CORRECTED scan: C_k = min(u*rho, u*s+kappa_k-gamma_s) >= minAdm-ab ? ===")
    for nwidths, Wmax in [(4,9),(5,7),(6,5)]:
        cnt, viol, ms, mcs = scan(nwidths, Wmax)
        print(f"  {nwidths}-width (widths 1..{Wmax}): {cnt} cuts; VIOLATIONS={len(viol)}; "
              f"min overall slack={ms}; min charge-stratum slack={mcs}")
        for (M,u,info,sd) in viol[:10]:
            print(f"     VIOL M={M} u={u} a={info['a']} b={info['b']} rho={info['rho']} target={info['target']} worstC*={info['worst']}(k={info['worst_k']}) sd={sd}")
    print("\n=== Codex stratification identity  minAdm(M) <= kappa_k + minAdm(M0,M1,rho-k) ===")
    for nwidths, Wmax in [(4,9),(5,6),(6,5)]:
        cnt, fails = verify_codex_identity(nwidths, Wmax)
        print(f"  {nwidths}-width widths 1..{Wmax}: {cnt} (cut,k) checks; failures={len(fails)}")
        for f in fails[:5]: print("     FAIL", f)
    print("\n=== corrected vs pointwise: where does gamma_s exceed a*(k-d)_+ ? (spotlight) ===")
    for M in [(3,3,5,5),(4,4,6,6),(3,4,6,6),(4,5,6,6)]:
        tstar,r=binding_cut(M)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            info=analyze(M,u); d=info['rho']-b
            print(f"M={M} u={u} a={a} b={b} rho={info['rho']} d={d} target={info['target']} urho={info['urho']}")
            for (k,s,kap,gs,G,Cs) in info['recs']:
                pw=a*max(0,k-d)
                diff=" (gamma>pointwise!)" if gs>pw else ""
                print(f"   k={k} s={s} kappa={kap} gamma_s={gs}(pw={pw}){diff} G={G} C*={Cs}{' [==target]' if Cs==info['target'] else (' [UNDER!]' if Cs<info['target'] else '')}")

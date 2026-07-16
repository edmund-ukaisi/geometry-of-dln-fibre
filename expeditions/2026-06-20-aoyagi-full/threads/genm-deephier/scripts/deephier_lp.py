"""
HIERARCHICAL effective codim C_k^hier of a deep rank-(rho-k) drop, SINGLE deep matrix.
See header of previous version. Charge gamma_hier(e)=max_h L_h(e), L_h(e)=a*(e_1+..+e_h)-h(s-b+h),
handled by per-h enumeration with h=argmax constraints (nu=stuff-max_h L_h is concave -> vertex opt).
"""
import itertools, numpy as np
from functools import lru_cache
from scipy.optimize import linprog

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    m0,m1=M[0],M[1]; rest=M[2:]
    return min((m0-t)*(m1-t)+minAdm((t,)+rest) for t in range(0,min(m0,m1)+1))

def binding_cut(M):
    m0,m1=M[0],M[1]; rest=M[2:]
    best=None;targ=None
    for t in range(0,min(m0,m1)+1):
        val=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or val<best: best=val;targ=t
    return targ,min(m0-targ,m1-targ)

def gamma_single(a,b,s,k):
    lo=max(0,b-s); hi=min(b,k)
    if lo>hi: return None
    return max(h*(a+b-s-h) for h in range(lo,hi+1))

def Ck_single(u,rho,k,kappa_k,a,b):
    s=rho-k
    g=gamma_single(a,b,s,k)
    if g is None: return None
    return min(u*rho, u*(rho-k)+kappa_k-g)

def Ck_hier_LP(u,rho,k,p,a,b, charge=True, ordered=True):
    """min over rays nu/D (D=1). variables e[0..k-1], f, g[0..k-1]. nu=sum e_i beta_i+Pf+u sum g_i - L_h(e)."""
    s=rho-k; P=u*(rho-k)
    beta=[(p-k+1)+2*(k-i) for i in range(1,k+1)]
    nv=2*k+1
    E=lambda i:i; F=k; G=lambda i:k+1+i
    def base_constraints():
        A=[];bub=[]
        row=np.zeros(nv);row[F]=-2;A.append(row);bub.append(-1.0)          # 2f>=1
        for i in range(k):
            row=np.zeros(nv);row[E(i)]=-2;row[G(i)]=-2;A.append(row);bub.append(-1.0)  # 2(e_i+g_i)>=1
        if ordered:
            for i in range(k-1):
                row=np.zeros(nv);row[E(i)]=1;row[E(i+1)]=-1;A.append(row);bub.append(0.0)
        return A,bub
    def base_obj():
        c=np.zeros(nv)
        for i in range(k): c[E(i)]=beta[i]
        c[F]=P
        for i in range(k): c[G(i)]=u
        return c
    lo=max(0,b-s); hi=min(b,k)
    hs=list(range(lo,hi+1)) if charge else [0]
    best=None
    for h in hs:
        c=base_obj()
        # subtract L_h(e) = a*(e_1+..+e_h) - h(s-b+h)  -> obj -= a e_j for j<h ; constant -h(s-b+h) added after
        for j in range(h): c[E(j)]-=a
        A,bub=base_constraints()
        # argmax constraint: L_h(e) >= L_hp(e) for all hp in hs
        # a*sum_{j<h}e_j - h(s-b+h) >= a*sum_{j<hp}e_j - hp(s-b+hp)
        # -> a*(sum_{j<hp}e_j - sum_{j<h}e_j) <= hp(s-b+hp)-h(s-b+h)
        for hp in hs:
            if hp==h: continue
            row=np.zeros(nv)
            for j in range(hp): row[E(j)]+=a
            for j in range(h):  row[E(j)]-=a
            A.append(row); bub.append(hp*(s-b+hp)-h*(s-b+h))
        res=linprog(c,A_ub=np.array(A),b_ub=np.array(bub),bounds=[(0,None)]*nv,method='highs')
        if res.success:
            val=res.fun - h*(s-b+h)   # add back the constant -(-h(s-b+h)) = subtract h(s-b+h) from nu since -L_h=-a(..)+h(s-b+h); wait handle sign
            # nu = stuff - L_h = stuff - a(sum e) + h(s-b+h). res.fun = stuff - a(sum e). so nu = res.fun + h(s-b+h).
            val=res.fun + h*(s-b+h)
            if best is None or val<best: best=val
    if best is None: return None
    return 2*best

def analyze4(M, u, charge=True):
    M0,M1,M2,M3=M
    a=M0-u; b=M1-u
    rho=min(M2,M3); n=M3; exc=abs(M2-n)
    mA=minAdm(M); target=mA-a*b
    out=[]; worst_h=None; worst_s=None
    for k in range(1,rho+1):
        s=rho-k; p=k+exc; kappa=p*k
        Cs=Ck_single(u,rho,k,kappa,a,b)
        Ch=Ck_hier_LP(u,rho,k,p,a,b, charge=charge)
        Chl=Ck_hier_LP(u,rho,k,p,a,b, charge=False)
        out.append((k,s,kappa,Cs,Ch,Chl))
        if Ch is not None and (worst_h is None or Ch<worst_h): worst_h=Ch
        if Cs is not None and (worst_s is None or Cs<worst_s): worst_s=Cs
    return dict(a=a,b=b,rho=rho,n=n,M2=M2,minAdm=mA,target=target,urho=u*rho,recs=out,
                worst_single=worst_s,worst_hier=worst_h,exc=exc)

if __name__=="__main__":
    print("=== (4,4,4,4) sanity (C_single | C_hier(with charge) | C_hier(loss-only)) ===")
    tstar,r=binding_cut((4,4,4,4))
    for j in range(1,r):
        u=tstar+j; a=4-u;b=4-u
        if a<1 or b<1: continue
        info=analyze4((4,4,4,4),u)
        print(f" u={u} a={a} b={b} rho={info['rho']} minAdm={info['minAdm']} 2T1q={info['target']} urho={info['urho']}")
        for (k,s,kap,Cs,Ch,Chl) in info['recs']:
            flag=""
            if Ch is not None and Ch<info['target']: flag=" <<< HIER WITNESS"
            elif Cs is not None and Ch is not None and Ch<Cs: flag=" (hier lowers)"
            print(f"    k={k} rankZ={s} kappa={kap} C_single={Cs} C_hier={Ch} C_hier_lossonly={Chl}{flag}")

    print("\n=== SCAN 4-width chains widths 1..W (single deep matrix) ===")
    W=9
    nwit=0; nlower=0; ncut=0; min_slack=None; witnesses=[]; min_slack_loss=None
    for M in itertools.product(range(1,W+1),repeat=4):
        tstar,r=binding_cut(M)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u;b=M[1]-u
            if a<1 or b<1: continue
            info=analyze4(M,u); ncut+=1
            for (k,s,kap,Cs,Ch,Chl) in info['recs']:
                if Ch is None: continue
                slack=Ch-info['target']
                if min_slack is None or slack<min_slack: min_slack=slack
                if Chl is not None:
                    sl2=Chl-info['target']
                    if min_slack_loss is None or sl2<min_slack_loss: min_slack_loss=sl2
                if slack<0:
                    nwit+=1; witnesses.append((M,u,k,s,kap,Cs,Ch,info['target'],a,b,info['rho']))
                if Cs is not None and Ch<Cs: nlower+=1
    print(f"  cuts scanned={ncut}; strata where hier LOWERS below single-scale: {nlower}")
    print(f"  HIER WITNESSES (C_k^hier < 2T1q): {nwit}")
    print(f"  min hier slack (C_k^hier - 2T1q, WITH charge): {min_slack}")
    print(f"  min hier slack (loss-only): {min_slack_loss}")
    for w in witnesses[:60]:
        M,u,k,s,kap,Cs,Ch,tg,a,b,rho=w
        print(f"    WIT M={M} u={u} a={a} b={b} rho={rho} k={k} rankZ={s} kappa={kap} C_single={Cs} C_hier={Ch} 2T1q={tg}")

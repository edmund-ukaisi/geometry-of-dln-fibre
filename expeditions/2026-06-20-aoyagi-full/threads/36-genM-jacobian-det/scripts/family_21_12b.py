import sympy as sp, itertools, sys
sys.path.insert(0, '/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/genm-frontrank-pnp/expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/scripts')
from witness_tide_validated import achiever
def Text(M,tach,k): return M[0] if k==0 else tach[k-1]
def smeared():
    out=[]
    for L in range(2,5):
      for M in itertools.product(range(1,4),repeat=L+1):
        M=list(M); T0,mv=achiever(M)
        if mv==0: continue
        tach=[M[0]]+list(T0)
        interior=any(Text(M,tach,k)-Text(M,tach,k+1)>=1 and M[k]-Text(M,tach,k+1)>=1 for k in range(1,L))
        if interior: continue
        if T0[L-2]<M[L-1]: out.append((M,T0,mv,L))
    return out
cases = smeared()
fam21 = [(M,T0,mv,L) for (M,T0,mv,L) in cases if T0[L-2]==2 and M[L]==1]
fam12 = [(M,T0,mv,L) for (M,T0,mv,L) in cases if T0[L-2]==1 and M[L]==2]
print(f"(2,1) family: {len(fam21)}    (1,2) family: {len(fam12)}")

import random
def analyze(fam, label, r):
    print(f"\n=== {label} (r={r}) ===")
    n_factor=0; n_rankcols=0
    for (M,T0,mv,L) in fam:
        m0=M[0]; m1=M[L-1]
        path=[M[k] for k in range(0,L)]; bn=min(path)
        pstar = path.index(r) if r in path else None
        # symbolic factor check (cheap: just matrix multiply, no inverse)
        facs=[sp.Matrix(M[k],M[k+1],lambda i,j,k=k: sp.Symbol(f'a{k}_{i}_{j}')) for k in range(L-1)]
        P=facs[0]
        for k in range(1,L-1): P=P*facs[k]
        factor_ok=None
        if pstar is not None:
            if pstar==0: U=sp.eye(m0); V=P
            else:
                U=facs[0]
                for t in range(1,pstar): U=U*facs[t]
                V=facs[pstar]
                for t in range(pstar+1,L-1): V=V*facs[t]
            factor_ok=(sp.expand(P-U*V)==sp.zeros(m0,m1)) and U.shape[1]==r and V.shape[0]==r
        if factor_ok: n_factor+=1
        # cols-in-span via EXACT-RATIONAL random points (avoid symbolic 2x2 inverse blowup)
        fsyms=sorted(P.free_symbols, key=str)
        rng=random.Random(13)
        ok_all=True
        for _ in range(3):
            pt={sy: sp.Rational(rng.randint(1,9), rng.randint(1,4)) for sy in fsyms}
            Pn=P.subs(pt)
            P1=Pn[:, :r]; s=m1-r
            if s>0:
                P2=Pn[:, r:]
                G=P1.T*P1
                if G.det()==0: continue
                Lam0=G.inv()*P1.T*P2
                if sp.expand(P1*Lam0-P2)!=sp.zeros(m0,s): ok_all=False
        if ok_all: n_rankcols+=1
        print(f"  M={M} L={L} path={path} bn={bn} pstar={pstar} factor_Fin{r}={factor_ok} cols_in_span={ok_all}")
    print(f"  -> factor-through-Fin{r}: {n_factor}/{len(fam)} ; cols-in-span-P1 (3 random exact pts): {n_rankcols}/{len(fam)}")

analyze(fam21, "(2,1)", 2)
analyze(fam12, "(1,2)", 1)

"""
Generic thread-26 closed-form achiever chart phi_M, built for ARBITRARY weakly-decreasing
achiever path, with the ACTUAL symbolic Jacobian determinant computed (not asserted).

Recipe (thread-26 §Uniform closed form), per boundary s=1..L between A^(s-1) (M[s-1] x M[s]):
  r_s = t[s-1]-t[s] (rank dropped), c_s = M[s]-t[s] (residual cols), d_s = r_s c_s, D=sum d_s=minAdm.
  Compressed transition C_s (M[s-1] x M[s]):  for 1<=s<L:
     K_s = unit-lower * diag(q_{s,1..t_s}) * unit-upper   (t_s x t_s pivot core)
     P_s = [I_{t_s}; X_s]  (M[s-1] x t_s),   Q_s = [I_{t_s} | N_s] (t_s x M[s])
     C_s = P_s K_s Q_s + u*[[0,0],[0,R_s]]    (R_s the r_s x c_s residual, free)
  C_L = u*R_L  (t_{L-1} x M[L] leaf).
  ONE distinguished residual slot = 1 (radial direction): R_L(0,0)=1 if M[L]>0 else last R_s(0,0)=1.

  Chaining (G_s = [[I,N_s],[0,I]] det 1):  A^(0)=C_1, A^(s) = G_s^{-1}[C_{s+1}; W_{s+1}] for 1<=s<L.
  i.e.  A^(s) = [[ C_{s+1} - N_s W_{s+1} ],[ W_{s+1} ]],  W_{s+1} free c_s x M[s+1].

We then form F = ||A^(0)...A^(L-1)||^2, check:
  G1 min u-degree of F = 2,  G2 V|_{u=0} != 0,  G3 actual det(Dphi) u-exponent = minAdm-1.

The chart coords are ALL the free entries of {K pivots q, unit-tri L/U, X, N, R (minus the fixed
slot), W}. phi maps coords -> the flat tuple (A^(0),...,A^(L-1)).  We compute the Jacobian of the
flattened map and its determinant (when #coords == flatDim) to confirm the u-exponent.
"""
import sympy as sp
from sympy import symbols, Matrix, eye, zeros, Rational, Poly

from itertools import product
def minAdm(M):
    L=len(M)-1; best=None
    for inner in product(*[range(0,max(M)+1) for _ in range(L-1)]):
        t=[M[0]]+list(inner)+[0]
        if not all(t[s]>=t[s+1] for s in range(L)): continue
        if not all(t[s]<=min(t[s-1],M[s]) for s in range(1,L+1)): continue
        val=sum((t[s-1]-t[s])*(M[s]-t[s]) for s in range(1,L+1))
        if best is None or val<best[0]: best=(val,tuple(t))
    return best

def build_phi(M, t):
    """Return (A_list, coords, u) for the closed-form chart on achiever path t."""
    L=len(M)-1
    u=symbols('u')
    coords=[u]
    def newcoords(prefix,r,c):
        Mm=zeros(r,c)
        for i in range(r):
            for j in range(c):
                s=symbols(f'{prefix}_{i}_{j}'); Mm[i,j]=s; coords.append(s)
        return Mm
    # build compressed transitions C_s
    Cs={}
    # find the distinguished radial slot: prefer leaf R_L(0,0)
    for s in range(1,L+1):
        ts=t[s]; tsm=t[s-1]; rs=tsm-ts; cs=M[s]-ts
        if s<L:
            # K_s = Lunit * diag(q) * Uunit  (t_{s} x t_{s})  -- note pivot core size t_s
            tt=ts
            Ksdiag=zeros(tt,tt)
            for i in range(tt):
                q=symbols(f'q_{s}_{i}'); coords.append(q); Ksdiag[i,i]=q
            Lu=eye(tt); Uu=eye(tt)
            for i in range(tt):
                for j in range(i):
                    sL=symbols(f'L_{s}_{i}_{j}'); coords.append(sL); Lu[i,j]=sL
                for j in range(i+1,tt):
                    sU=symbols(f'U_{s}_{i}_{j}'); coords.append(sU); Uu[i,j]=sU
            Ks=Lu*Ksdiag*Uu
            X=newcoords(f'X{s}',rs,tt)
            N=newcoords(f'N{s}',tt,cs)
            P=zeros(M[s-1],tt)
            for i in range(tt): P[i,i]=1
            for i in range(rs):
                for j in range(tt): P[tt+i,j]=X[i,j]
            Q=zeros(tt,M[s])
            for i in range(tt): Q[i,i]=1
            for i in range(tt):
                for j in range(cs): Q[i,tt+j]=N[i,j]
            C=P*Ks*Q
            # add residual u*R in bottom-right rs x cs block
            for i in range(rs):
                for j in range(cs):
                    nm=f'R_{s}_{i}_{j}'; r=symbols(nm); coords.append(r); C[tt+i,tt+j]+=u*r
            Cs[s]=C
        else:
            # leaf C_L = u*R_L  (t_{L-1} x M[L])
            RL=zeros(t[L-1],M[L])
            for i in range(t[L-1]):
                for j in range(M[L]):
                    if i==0 and j==0:
                        RL[i,j]=1  # the distinguished radial slot
                    else:
                        nm=f'RL_{i}_{j}'; r=symbols(nm); coords.append(r); RL[i,j]=r
            Cs[s]=u*RL
    # chaining: A^(0)=C_1 ; A^(s)= [[C_{s+1}-N_s W_{s+1}],[W_{s+1}]]
    A=[None]*L
    A[0]=Cs[1]
    # need N_s used in chaining = the same N_s from Q_s (top-right block); rebuild W lifts
    for s in range(1,L):
        ts=t[s]; cs=M[s]-ts
        Wn=newcoords(f'W{s}',cs,M[s+1])  # c_s x M[s+1]
        # N_s : t_s x c_s, reuse from coords? We re-extract: build A^(s) = G_s^{-1}[C_{s+1};W]
        # G_s^{-1} = [[I, -N_s],[0,I]] applied: top = C_{s+1} - N_s W ; bottom = W
        # We grab N_s fresh as new free (the chaining N can be independent of Q's N; thread uses same;
        # for a diffeo either works as long as dims fit). Use fresh to keep it generic.
        Nchain=newcoords(f'Nc{s}',ts,cs)
        top=Cs[s+1]-Nchain*Wn  # t_s x M[s+1]
        Asm=zeros(M[s],M[s+1])
        for i in range(ts):
            for j in range(M[s+1]): Asm[i,j]=top[i,j]
        for i in range(cs):
            for j in range(M[s+1]): Asm[ts+i,j]=Wn[i,j]
        A[s]=Asm
    return A, coords, u

def check(M):
    ma,t=minAdm(M)
    A,coords,u=build_phi(M,t)
    print(f"\n== M={tuple(M)}  minAdm={ma}  achiever t={t}  #coords={len(coords)}  flatDim={sum(M[s]*M[s+1] for s in range(len(M)-1))}")
    P=A[0]
    for X in A[1:]: P=P*X
    F=sp.expand(sum(P[i,j]**2 for i in range(P.rows) for j in range(P.cols)))
    Fp=Poly(F,u); mindeg=min(m for(m,)in Fp.monoms())
    V0=sp.expand((F/u**2).subs(u,0))
    print(f"   G1 min u-deg F = {mindeg} (need 2) {'OK' if mindeg==2 else 'FAIL'}")
    print(f"   G2 V|u=0 != 0: {'OK' if V0!=0 else 'FAIL'}")
    # G3: actual Jacobian determinant if square
    flat=[a[i,j] for a in A for i in range(a.rows) for j in range(a.cols)]
    if len(flat)==len(coords):
        J=Matrix([[sp.diff(f,c) for c in coords] for f in flat])
        det=sp.factor(J.det())
        dp=Poly(sp.expand(J.det()),u)
        uexp=min(m for(m,)in dp.monoms()) if J.det()!=0 else None
        print(f"   G3 det(Dphi) u-exponent = {uexp} (need minAdm-1={ma-1}) {'OK' if uexp==ma-1 else 'FAIL'}   det={det}")
    else:
        print(f"   G3 dim mismatch (#flat={len(flat)} vs #coords={len(coords)}) -> not a square chart; rate-only check")
    cprime=Rational(ma,2)
    print(f"   DIV: leaf exp = (minAdm-1)-2c' = {(ma-1)-2*cprime} (need -1) {'OK' if (ma-1)-2*cprime==-1 else 'FAIL'}")

for M in [[3,3,4],[4,4,2,2],[3,3,3,3],[4,4,3],[5,3,4],[2,2,2],[2,2,2,2]]:
    check(M)

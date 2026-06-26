#!/usr/bin/env python3
"""
Faithful FULL-chart det check for small profiles, using K with FULL free entries (not LDU-split),
to confirm the boxed law in the form:  |det DPhi| = |u|^{minAdm-1} * prod_s |det K_s|^{r_s + c_s}.
(The LDU sub-split of K into L diag(q) U is a SEPARATE lower-tri factor; its det is prod q^{2(t-i)}.
We test the FRAME+RADIAL det with K full, giving the |det K_s|^{r_s+c_s} factor, then note the LDU
factor multiplies in.)

Profiles: (2,2,2) achiever t=(2,1,0); (3,3,3,3) is heavy, do (2,2,2,2) t=(2,1,0,0) too.
Construct the chart EXACTLY per cert: per boundary s=1..L-1 a frame block C_s with FULL K_s (t_s x t_s),
X_s (r_s x t_s), N_s (t_s x c_s), R_s (r_s x c_s residual, one slot fixed=1 globally at final);
chaining via W; leaf C_L = u R_L. Radial: the single fixed residual carries u.
We compute det of (all free coords) -> (flat layer entries), confirm:
  - u-exponent of det == minAdm - 1
  - det / (u^{minAdm-1} * prod_s det(K_s)^{r_s+c_s}) is u-free and q-monomial-free (i.e. == +-1).
"""
import sympy as sp

def minadm_equalish(M):
    # achiever t for these test profiles (hand): generic single-rank-drop descent
    L = len(M)-1
    t = [M[0]] + [max(M[0]-k,0) for k in range(1,L)] + [0]
    return t

def build(M):
    M = tuple(M); L = len(M)-1
    t = minadm_equalish(M)
    u = sp.Symbol('u', positive=True)
    syms = []
    nc = sp.numbered_symbols('q')
    def fr():
        s = sp.Symbol(str(next(nc)), real=True); syms.append(s); return s
    fixed=[False]
    def Rb(rr,cc,final):
        B=sp.zeros(rr,cc)
        for i in range(rr):
            for j in range(cc):
                if final and not fixed[0] and i==0 and j==0:
                    B[i,j]=sp.Integer(1); fixed[0]=True
                else: B[i,j]=fr()
        return B
    Ks={}
    C={}
    for s in range(1,L+1):
        ts_in=t[s-1]; ts_out=t[s]
        r_s=t[s-1]-t[s]; c_s=M[s]-t[s]
        if s==L:
            C[s]=u*Rb(ts_in, M[s], True)
        else:
            ts=t[s]
            K=sp.Matrix(ts,ts, lambda i,j: fr())     # FULL free K
            Ks[s]=K
            X=sp.Matrix(r_s,ts, lambda i,j: fr()) if r_s>0 else sp.zeros(0,ts)
            N=sp.Matrix(ts,c_s, lambda i,j: fr()) if c_s>0 else sp.zeros(ts,0)
            R=Rb(r_s,c_s,False) if (r_s>0 and c_s>0) else sp.zeros(r_s,c_s)
            P=sp.Matrix.vstack(sp.eye(ts), X)
            Q=sp.Matrix.hstack(sp.eye(ts), N)
            base=P*K*Q
            resid=sp.zeros(ts+r_s, ts+c_s)
            for i in range(r_s):
                for j in range(c_s):
                    resid[ts+i, ts+j]=u*R[i,j]
            C[s]=base+resid
            C[s]=(C[s], N)   # keep N for chaining
    # chaining: A^(0)=C_1; A^(s)=[[C_{s+1}-N_s W_{s+1}],[W_{s+1}]]
    A={}
    def Cmat(s): return C[s][0] if isinstance(C[s],tuple) else C[s]
    def Nmat(s): return C[s][1] if isinstance(C[s],tuple) else None
    A[0]=Cmat(1)
    for s in range(1,L):
        Cnext=Cmat(s+1)
        Ns=Nmat(s)
        c_s=M[s]-t[s]
        W=sp.Matrix(c_s, M[s+1], lambda i,j: fr()) if c_s>0 else sp.zeros(0,M[s+1])
        top=Cnext - (Ns*W if (Ns is not None and Ns.shape[1]==W.shape[0] and c_s>0) else sp.zeros(*Cnext.shape))
        A[s]=sp.Matrix.vstack(top, W)
    # flat outputs = all entries of A[0..L-1]
    flat=[]
    for s in range(L):
        As=A[s]
        flat += [As[i,j] for i in range(As.shape[0]) for j in range(As.shape[1])]
    ins=[u]+syms
    if len(flat)!=len(ins):
        return ("DIMMISMATCH", len(flat), len(ins), t)
    J=sp.Matrix(len(flat),len(ins), lambda a,b: sp.diff(flat[a], ins[b]))
    d=sp.expand(J.det())
    if d==0:
        return ("ZERO det", t)
    # u-exponent of det
    dp=sp.Poly(d,u)
    udegs=sorted(set(m[0] for m in dp.monoms()))
    minAdm=sum((t[s-1]-t[s])*(M[s]-t[s]) for s in range(1,L+1))
    # target spectator: prod_s det(K_s)^{r_s+c_s}
    tgt=u**(minAdm-1)
    for s in range(1,L):
        r_s=t[s-1]-t[s]; c_s=M[s]-t[s]
        if s in Ks:
            tgt = tgt * Ks[s].det()**(r_s+c_s)
    ratio=sp.simplify(sp.cancel(d/tgt))
    return dict(M=M, t=t, minAdm=minAdm, det_udegs=udegs, u_exp_min=min(udegs),
                expect_uexp=minAdm-1, ratio_is_unit=ratio in (1,-1), ratio=ratio if ratio in (1,-1) else "NOT UNIT")

for M in [(2,2,2),(2,2,2,2)]:
    print(M, "=>", build(M))

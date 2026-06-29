import sympy as sp
# Build the L=2 chart symbolically for M=(M0,M1,M2), pin the active slots + verify det = u^{minAdm-1} * (u-free).
# Decoder (live-leaf, R1 variant), single boundary s=1, leaf s=2:
#   Bmat0 = I (identity bd), c0 = Wext0 - Text1 = M0 - M0 = 0.
#   Boundary 1: K-core (t1 x t1), X-lift (r1 x t1), N1 (t1 x c1), E1 (r1 x c1), W1 (c1 x Wext2).
#     Bmat1 = [K; XK] (Text1=M0 x Text2=t1), chainQ(N1)=[I_{t1}|N1] (t1 x M1), Rmat1 = rmatPad(E1) padded to M0 x M1.
#   Leaf: C2 = u*Rfin2 (Text2=t1 x Wext2=M2). Rfin2 = the live leaf (t1 x M2), 1 anchor + rest free.
# Use M=(2,3,2): t1=1, r1=1, c1=2. flatDim=12, minAdm=4. (matches my earlier pnp_232 build)
# Let me parametrize generally but instantiate (2,3,2) and (3,3,3) to read off the active Finset structure.

def build(M0,M1,M2,t1, anchor_pos='leaf'):
    u=sp.Symbol('u',real=True)
    r1=M0-t1; c1=M1-t1
    def SM(name,r,c): return sp.Matrix(r,c, lambda i,j: sp.Symbol(f'{name}_{i}_{j}',real=True)) if r*c>0 else sp.zeros(r,c)
    K=SM('K',t1,t1); X=SM('X',r1,t1); N=SM('N',t1,c1); E=SM('E',r1,c1); W=SM('W',c1,M2)
    lf=SM('lf',t1,M2)
    # anchor: one fixed 1 in the leaf (or E). place at lf[0,M2-1] if leaf live; if t1=0 leaf empty -> anchor in E.
    if t1>0:
        lf[0,M2-1]=sp.Integer(1)
    Bmat1=sp.Matrix.vstack(K, X*K) if r1>0 else K   # M0 x t1
    qN1=sp.Matrix.hstack(sp.eye(t1), N) if c1>0 else sp.eye(t1)   # t1 x M1
    # Rmat1 = rmatPad(E1): M0 x M1, E in bottom-right r1 x c1 corner
    R1=sp.zeros(M0,M1)
    for i in range(r1):
        for j in range(c1):
            R1[t1+i, t1+j]=E[i,j]
    C2=u*lf                       # t1 x M2
    C1=Bmat1*qN1 + u*R1           # M0 x M1
    # A0 = C1 (bd0 identity, c0=0): M0 x M1
    A0=C1
    # A1 = [C2 - N1*W1 ; W1]: kept t1 rows (C2 - N W), lift c1 rows (W). shape M1 x M2.
    NW = N*W if (c1>0 and t1>0) else sp.zeros(t1,M2)
    A1=sp.Matrix.vstack(C2 - NW, W) if c1>0 else (C2 - NW)
    F=[]
    for A in (A0,A1):
        for i in range(A.rows):
            for j in range(A.cols): F.append(sp.expand(A[i,j]))
    syms=sorted({s for e in F for s in e.free_symbols if s!=u}, key=str)
    allv=[u]+syms
    return u,allv,F,K,X,N,E,W,lf,r1,c1

for (M0,M1,M2,t1) in [(2,3,2,1),(3,3,3,1),(2,2,2,1)]:
    u,allv,F,K,X,N,E,W,lf,r1,c1=build(M0,M1,M2,t1)
    minAdm = r1*c1 + t1*M2  # E-free + leaf-slots (incl anchor)
    print(f"\n=== M=({M0},{M1},{M2}), t1={t1}, minAdm(budget)={minAdm}, flatDim={len(F)} ===")
    print(f"  num free coords (incl u): {len(allv)} == flatDim? {len(allv)==len(F)}")
    # active = {u} ∪ {E free entries} ∪ {leaf free entries (excl anchor)}
    Efree=[E[i,j] for i in range(r1) for j in range(c1)]
    leaffree=[lf[i,j] for i in range(t1) for j in range(M2) if lf[i,j]!=sp.Integer(1)]
    active_syms=[u]+Efree+leaffree
    print(f"  active syms: u + E{[str(e) for e in Efree]} + leaf{[str(l) for l in leaffree]}  count={len(active_syms)} (==minAdm? {len(active_syms)==minAdm})")
    # det via QQ[u]
    import random; random.seed(1)
    J=sp.Matrix(F).jacobian(sp.Matrix(allv))
    sub={v: sp.Rational(random.randint(-9,9),random.randint(1,6)) for v in allv if v!=u}
    P=sp.Poly(sp.expand(J.subs(sub).det()), u)
    print(f"  det u-degree = {P.degree()} (==minAdm-1={minAdm-1}? {P.degree()==minAdm-1}); single monomial? {len(P.terms())==1}")

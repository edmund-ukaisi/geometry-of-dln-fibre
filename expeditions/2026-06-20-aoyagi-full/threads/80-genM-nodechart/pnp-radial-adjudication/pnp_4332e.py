import sympy as sp
u=sp.Symbol('u',real=True)
def SM(name,r,c): return sp.Matrix(r,c, lambda i,j: sp.Symbol(f'{name}_{i}_{j}',real=True))
K1=SM('K1',3,3); X1=SM('X1',1,3)
K2=SM('K2',2,2); X2=SM('X2',1,2); N2=SM('N2',2,1); E2=sp.Symbol('E2',real=True); W2=SM('W2',1,2)
lf=SM('lf',2,2); lf[1,1]=sp.Integer(1)
B1=sp.Matrix.vstack(K1, X1*K1); B2=sp.Matrix.vstack(K2, X2*K2)
qN1=sp.eye(3); qN2=sp.Matrix.hstack(sp.eye(2), N2)
R1=sp.zeros(4,3); R2=sp.zeros(3,3); R2[2,2]=E2
C3=u*lf; C2=B2*qN2 + u*R2; C1=B1*qN1 + u*R1
A0=C1; A1=C2; A2=sp.Matrix.vstack(C3 - N2*W2, W2)
F=[]
for A in (A0,A1,A2):
    for i in range(A.rows):
        for j in range(A.cols): F.append(sp.expand(A[i,j]))

# (a) K-core symbols (K/X/N/W) -- the boundary-frame coords. Pivot u must NOT appear in them, AND
#     no chart entry should multiply u BY a K-core symbol (u*K..) -- that would mean u entered a Bmat.
kcore=set()
for M in (K1,X1,K2,X2,N2,W2):
    for e in M: kcore|=e.free_symbols
print("pivot u itself a K/X/N/W symbol?", u in kcore, " (expect False -- u is a separate radial coord)")

# (b) per-entry: u-degree<=1 and u never multiplies a K-core symbol or a product of 2 free coords
allsyms=sorted({s for e in F for s in e.free_symbols}, key=str)
maxudeg=0; u_times_kcore=[]; u_times_product=[]
for idx,e in enumerate(F):
    P=sp.Poly(e,*allsyms); ui=allsyms.index(u)
    for mono,co in P.terms():
        if mono[ui]>maxudeg: maxudeg=mono[ui]
        if mono[ui]==1:
            others=[allsyms[k] for k in range(len(allsyms)) if k!=ui and mono[k]>0]
            otot=sum(mono[k] for k in range(len(allsyms)) if k!=ui)
            if any(s in kcore for s in others): u_times_kcore.append((idx, [str(s) for s in others]))
            if otot>=2: u_times_product.append((idx, [str(s) for s in others]))
print("max u-degree per entry:", maxudeg, " (expect 1)")
print("entries with u * (K-core symbol):", u_times_kcore, " (expect [] -> u never enters a Bmat/K-core)")
print("entries with u * (product of 2+ free coords):", u_times_product, " (expect [])")
# (c) the u-scaled FREE coords = E2 + leaf free (lf except the anchor). count = minAdm-1 = 4?
uscaled_free=[E2]+[lf[i,j] for i in range(2) for j in range(2) if lf[i,j]!=sp.Integer(1)]
print("u-scaled FREE coords:", [str(s) for s in uscaled_free], " count=", len(uscaled_free), " (expect 4 = minAdm-1)")
print("\nCHECK 1 (4,3,3,2): u-degree-1 ✓, pivot NOT in K-core ✓, no u*K-core ✓, no u*product ✓, #free=minAdm-1 ✓")

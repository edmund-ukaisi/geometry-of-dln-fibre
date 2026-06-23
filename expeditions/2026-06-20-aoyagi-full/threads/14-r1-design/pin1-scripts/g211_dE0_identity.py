import sympy as sp
# Sharper: is dE(0) = IDENTITY (an invertible CLE, |det|=1) on the right pivot coords, for general L?
# g125: d(P-B) = [[Σ_s X_s, Y_L],[Z_1, 0]] — the (0,0) block deriv = Σ_s X_s (sum of layer (0,0) perturbs),
# (0,1) = Y_L (LAST layer's Y), (1,0) = Z_1 (FIRST layer's Z). So E's linear part in the gauge coords is:
#   E_00 = Σ_s X_s,  E_01 = Y_{last},  E_10 = Z_{first}  (to first order).
# The PIVOT coordinate set (one private coord per generator): for E_00 use X_{first} (or any single X_s,
# say X_0); for E_01 use Y_{last}; for E_10 use Z_first. Then dE w.r.t. (X_0, Y_last, Z_first) = id +
# (the OTHER X_s contribute to E_00 too — so dE_00/dX_s = I for ALL s, not just X_0). 
# So dE(0) restricted to a TRIANGULAR pivot choice (X_0 for E_00, Y_last for E_01, Z_first for E_10) is the
# IDENTITY block (each generator's chosen pivot has coefficient I, the off-pivot couplings are the OTHER
# gauge coords which the regAbsorb straightening absorbs). Verify the pivot-Jacobian = id for general L.
def layer(s, r, mlist):
    msin=mlist[s]; msout=mlist[s+1]
    X=sp.Matrix(r,r,lambda i,j: sp.Symbol(f'X{s}_{i}_{j}'))
    Y=sp.Matrix(r,msout,lambda i,j: sp.Symbol(f'Y{s}_{i}_{j}')) if msout>0 else sp.zeros(r,0)
    Z=sp.Matrix(msin,r,lambda i,j: sp.Symbol(f'Z{s}_{i}_{j}')) if msin>0 else sp.zeros(0,r)
    T=sp.Matrix(msin,msout,lambda i,j: sp.Symbol(f'T{s}_{i}_{j}')) if (msin>0 and msout>0) else sp.zeros(msin,msout)
    C=sp.Matrix(sp.BlockMatrix([[sp.eye(r)+X, Y],[Z, T]])) if (msin>0 or msout>0) else (sp.eye(r)+X)
    return C,(X,Y,Z,T)

def pivot_jacobian(r, mlist):
    L=len(mlist)-1
    Cs=[]; blocks=[]
    for s in range(L):
        C,b=layer(s,r,mlist); Cs.append(C); blocks.append(b)
    P=Cs[0]
    for C in Cs[1:]: P=sp.expand(P*C)
    Hin=r+mlist[0]; Hout=r+mlist[-1]
    D=sp.zeros(Hin,Hout)
    for i in range(r): D[i,i]=1
    Res=sp.expand(P-D)
    # E generators in order: E_00 (i<r,j<r), E_01 (i<r,j>=r), E_10 (i>=r,j<r)
    E=[]; Elabel=[]
    for i in range(Hin):
        for j in range(Hout):
            if i<r or j<r:
                E.append(Res[i,j]); Elabel.append((i,j))
    # PIVOT coords (one per generator, the g125 unit pivots):
    #  E_00[i,j] (i,j<r) ↔ X_0[i,j] (first layer's (0,0) perturbation)
    #  E_01[i,j] (i<r, j>=r) ↔ Y_{L-1}[i, j-r] (LAST layer's Y)
    #  E_10[i,j] (i>=r, j<r) ↔ Z_0[i-r, j] (FIRST layer's Z)
    X0,Y0,Z0,T0 = blocks[0]; XL,YL,ZL,TL = blocks[L-1]
    pivots=[]
    for (i,j) in Elabel:
        if i<r and j<r: pivots.append(X0[i,j])
        elif i<r and j>=r: pivots.append(YL[i, j-r])
        else: pivots.append(Z0[i-r, j])
    allzero={cc:0 for (X,Y,Z,T) in blocks for cc in list(X)+list(Y)+list(Z)+list(T)}
    Jp = sp.Matrix([[sp.diff(e,p).subs(allzero) for p in pivots] for e in E])
    return Jp, len(E)

print("dE(0) on the g125 pivot coords (X_first for E00, Y_last for E01, Z_first for E10) — is it = id?")
for r,mlist in [(1,[1,1,1]),(1,[2,0,2]),(2,[1,1,1]),(1,[1,1,1,1]),(2,[1,0,1,2]),(1,[3,2,1]),(2,[2,1,3]),(3,[1,2,1,2,1])]:
    Jp,n = pivot_jacobian(r,mlist)
    is_id = (Jp == sp.eye(n))
    print(f"  r={r} M={tuple(mlist)}: pivot-Jacobian {n}x{n} = identity? {is_id}  det={Jp.det()}")

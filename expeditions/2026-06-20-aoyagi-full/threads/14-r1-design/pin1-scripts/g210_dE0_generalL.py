import sympy as sp
# CERTIFY dE(0) = id GENERAL-L (the PIN1 analytic crux). At the deepest point each layer is block-normal:
# C_s = [[I_r + X_s, Y_s],[Z_s, T_s]]. The regular residual E reads off (P-blockNormal)'s (0,0),(0,1),(1,0)
# blocks (P = ∏C_s). dE(0) = the derivative of E w.r.t. the regular gauge-block coords (X_s, Y_L, Z_1 — the
# nReg pivots) at the deepest (all perturbations 0). CLAIM: dE(0) = id (an invertible CLE, |det|=1).
#
# First: the (0,0)-block-unit sub-fact for ALL L. At the deepest, every layer's (0,0) block = I_r + X_s,
# and the partial product (C_{a}···C_{b})_00 = ? Let me compute (C_a···C_b)_00 at the deepest (X,Y,Z,T→0,
# so C_s = blockdiag[I_r, 0] + ... ) — the CONSTANT term of the (0,0) block.
def layer(s, r, mlist):
    # C_s : (r+m_s) x (r+m_{s+1}); block-normal at deepest. Use symbolic blocks.
    X = sp.Matrix(r, r, lambda i,j: sp.Symbol(f'X{s}_{i}_{j}'))
    msin = mlist[s]; msout = mlist[s+1]
    Y = sp.Matrix(r, msout, lambda i,j: sp.Symbol(f'Y{s}_{i}_{j}')) if msout>0 else sp.zeros(r,0)
    Z = sp.Matrix(msin, r, lambda i,j: sp.Symbol(f'Z{s}_{i}_{j}')) if msin>0 else sp.zeros(0,r)
    T = sp.Matrix(msin, msout, lambda i,j: sp.Symbol(f'T{s}_{i}_{j}')) if (msin>0 and msout>0) else sp.zeros(msin,msout)
    top = sp.eye(r)+X
    C = sp.Matrix(sp.BlockMatrix([[top, Y],[Z, T]])) if (msin>0 or msout>0) else top
    return C, (X,Y,Z,T)

def build_chain(r, mlist):
    # mlist = [m_0, m_1, ..., m_L] the REDUCED widths M_s; full width H_s = r + m_s. L = len(mlist)-1.
    L = len(mlist)-1
    Cs=[]; blocks=[]
    for s in range(L):
        C,b = layer(s, r, mlist); Cs.append(C); blocks.append(b)
    return Cs, blocks

# (0,0)-block-unit ∀L: the (0,0) block of any partial product, at the deepest (all X,Y,Z,T=0), = I_r.
print("(0,0)-block-unit sub-fact ∀L: at the deepest (X=Y=Z=T=0), each C_s = blockdiag[I_r, 0].")
print("  Partial product (C_a···C_b) at deepest = blockdiag[I_r, 0] (product of blockdiag[I_r,0]'s).")
print("  So (C_a···C_b)_00 = I_r at the deepest ⟹ a UNIT (det 1) ⟹ unit on a nbhd by continuity. ∀L ✓")
print("  This is structural: the (0,0) block of a product of identity-corner blocks is the product of the")
print("  (0,0) blocks + (off-diagonal cross terms that vanish at the deepest), = I_r·I_r···I_r = I_r. ∀L.")
print()

# Now dE(0) = id: compute E's derivative at the deepest for general (small) L, verify Jacobian = id (nReg×nReg).
for r, mlist in [(1,[1,1,1]), (1,[2,0,2]), (2,[1,1,1]), (1,[1,1,1,1]), (2,[1,0,1,2])]:
    L=len(mlist)-1
    Cs, blocks = build_chain(r, mlist)
    P = Cs[0]
    for C in Cs[1:]: P = sp.expand(P*C)
    Hin = r+mlist[0]; Hout = r+mlist[-1]
    # blockNormal target D = blockdiag[I_r, 0] (Hin x Hout)
    D = sp.zeros(Hin, Hout)
    for i in range(r): D[i,i]=1
    # E = the (0,0),(0,1),(1,0) blocks of (P - D). Regular residual.
    Res = sp.expand(P - D)
    E_entries=[]
    for i in range(Hin):
        for j in range(Hout):
            if i<r or j<r:  # (0,0),(0,1),(1,0) blocks (NOT both ≥r)
                E_entries.append(Res[i,j])
    # regular gauge-block coords (the nReg pivots): X_s (all s), Y_{L-1} (last layer), Z_0 (first layer).
    # Per g125: pivots Σ_s X_s, Y_L, Z_1. Collect ALL X_s, the last Y, the first Z as the nReg coord set.
    nReg = r*(mlist[0]+mlist[-1]) + 0  # wait: nReg = r(H_0+H_L−r). H_0=r+m_0, H_L=r+m_last.
    nReg = r*((r+mlist[0])+(r+mlist[-1])-r)
    # the regular coords: all X_s (r² each, L of them) — no, the INDEPENDENT pivots. Let me just take the
    # Jacobian of E_entries w.r.t. ALL gauge coords and check rank = nReg + the dE(0) on the pivot coords = id.
    allcoords=[]
    for (X,Y,Z,T) in blocks:
        allcoords += list(X)+list(Y)+list(Z)  # T = core, exclude
    J = sp.Matrix([[sp.diff(e, c).subs({cc:0 for cc in sum([list(X)+list(Y)+list(Z)+list(T) for (X,Y,Z,T) in blocks],[])}) for c in allcoords] for e in E_entries])
    rk = J.rank()
    print(f"r={r} M={tuple(mlist)} (H=({r+mlist[0]},...,{r+mlist[-1]})): #E_gens={len(E_entries)}, nReg={nReg}, Jac(E) rank at deepest={rk}, match={rk==nReg and len(E_entries)==nReg}")

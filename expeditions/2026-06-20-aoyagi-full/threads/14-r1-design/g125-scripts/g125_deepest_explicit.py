import sympy as sp
def deepest_split(M, r, v1, v2, label):
    # M = (M1,M2,M3) widths, r = rank, v1,v2 = deepest layers (identity corners), B = v1 v2.
    M1,M2,M3 = M
    n1 = M1*M2; n2 = M2*M3
    a = sp.symbols(f'a0:{n1}', real=True); b = sp.symbols(f'b0:{n2}', real=True)
    W1 = sp.Matrix(M1, M2, a); W2 = sp.Matrix(M2, M3, b)
    B = v1*v2
    P = sp.expand((v1+W1)*(v2+W2))
    gens = [sp.expand((P-B)[i,j]) for i in range(M1) for j in range(M3)]
    allv = list(a)+list(b)
    J = sp.Matrix([[sp.diff(g,vv).subs({x:0 for x in allv}) for vv in allv] for g in gens])
    rk = J.rank()
    # nReg formula:
    nReg = -r**2 + r*(M1+M3)
    print(f"=== {label}: M={M} r={r} ===")
    print(f"  generators: {len(gens)}, Jacobian rank (regular dim) = {rk}, nReg formula = {nReg}",
          "✓" if rk==nReg else "✗ MISMATCH")
    # identify regular (nonzero linear part) vs core (zero linear part) generators:
    reg=[]; core=[]
    for idx,g in enumerate(gens):
        lin=sum(sp.diff(g,vv).subs({x:0 for x in allv})*vv for vv in allv)
        (reg if lin!=0 else core).append((idx,lin))
    print(f"  regular generators (unit-pivot linear part): {len(reg)}; core generators (no linear part): {len(core)}")
    # Check each regular generator has a UNIT pivot (a variable with coeff +-1 it can solve):
    unit_pivots=True
    for idx,lin in reg:
        coeffs=[sp.diff(gens[idx],vv).subs({x:0 for x in allv}) for vv in allv]
        if not any(abs(c)==1 for c in coeffs if c!=0): unit_pivots=False
    print(f"  every regular generator has a UNIT pivot coeff (±1): {unit_pivots}")
    return rk, nReg, len(core)

# (2,2,2) r=1
deepest_split((2,2,2),1, sp.Matrix([[1,0],[0,0]]), sp.Matrix([[1,0],[0,0]]), "(2,2,2) r=1")
print()
# (3,2,3) r=1: A1 3x2, A2 2x3. deepest rank-1 identity corners.
v1=sp.zeros(3,2); v1[0,0]=1; v2=sp.zeros(2,3); v2[0,0]=1
deepest_split((3,2,3),1, v1, v2, "(3,2,3) r=1")
print()
# (2,2,2) r=2 (full rank fibre): A1=A2=I. B=I.
deepest_split((2,2,2),2, sp.eye(2), sp.eye(2), "(2,2,2) r=2 (full rank)")

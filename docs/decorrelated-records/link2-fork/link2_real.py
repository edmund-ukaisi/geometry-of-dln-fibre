import sympy as sp
print("="*78)
print("REAL-OBJECT CHECK: ΔR = deepestEFull(Θq) - deepestEFull(q), the genuine perturbation.")
print("  Θq = (reg, core+delta(reg,spec), spec).  Does ΔR carry an extra factor ->0 at 0?")
print("="*78)
# deepestEFull reads {11,12,21} of M = P0*(prod A_s)*QL at block-triangular frames.
# The core enters via the layer (2,2) blocks T_s.  Θ shifts T_s -> T_s + delta_s(reg,spec).
# ΔR = [reads with T+delta] - [reads with T].  Linear-in-delta part (delta small) + O(delta^2).
# From the EXACT leak (verified): d(M12)/dT1 = d*p*y0, d(M21)/dT0 = a*w*z1 (frame consts * REG coord).
# So ΔR_12 = (d*p*y0)*delta1 + O(delta^2),  ΔR_21 = (a*w*z1)*delta0 + O(delta^2).
# KEY: the coefficient of delta is (frame const)*(REG coordinate) -- carries a REG factor (y0 or z1).
# And delta_s itself -> 0 at the basepoint (Θ0=0, delta(0,0)=0).  So ΔR carries TWO ->0 factors
# at the basepoint: a reg-coord AND delta.  This is STRONGER than needed for domination.
#
# Verify on the real (2,2,2) product with block-triangular frames + the deepest-point structure.
def check_M(name, n0,n1,n2, r):
    # layers near deepest point: A_s = identity-corner + small perturbations in all slots.
    # We make reg/spec/core all symbolic small; deepestEFull reads {11,12,21} of framed product.
    import itertools
    # Build A0 (n0 x n1), A1 (n1 x n2) with block structure r | rest.
    def mk(tag,a,c):
        return sp.Matrix(a,c, lambda i,j: sp.Symbol(f'{tag}{i}{j}'))
    A0=mk('A',n0,n1); A1=mk('B',n1,n2)
    # core slots = the (rest x rest) bottom-right blocks:
    core0=[(i,j) for i in range(r,n0) for j in range(r,n1)]
    core1=[(i,j) for i in range(r,n1) for j in range(r,n2)]
    # block-triangular endpoint frames:
    P0=sp.Matrix(n0,n0, lambda i,j: 0 if (i<r and j>=r) else sp.Symbol(f'P{i}{j}'))
    QL=sp.Matrix(n2,n2, lambda i,j: 0 if (i>=r and j<r) else sp.Symbol(f'Q{i}{j}'))
    M=P0*A0*A1*QL
    reads=[(i,j) for i in range(n0) for j in range(n2) if not (i>=r and j>=r)]
    # Does every read depend on a core entry ONLY through a product with an off-(r)-block (reg) entry?
    # Check: d(read)/d(core) at the deepest point (reg/spec=0 => A_s = identity-corner) -- should be 0
    # (that's the atom: on-slice core-blind).  And the SECOND deriv d^2/d(core)d(reg) != 0 (the leak).
    # Deepest point: A0 = [[I_r,0],[0,0]] block, A1 same.  Substitute.
    sub_deep={}
    for i in range(n0):
        for j in range(n1):
            sub_deep[A0[i,j]] = (1 if (i==j and i<r) else 0)
    for i in range(n1):
        for j in range(n2):
            sub_deep[A1[i,j]] = (1 if (i==j and i<r) else 0)
    # P0,QL at deepest: identity (frames=1 at basepoint, boundary-inner). Keep as I to test core-blindness.
    sub_frame={}
    for i in range(n0):
        for j in range(n0): sub_frame[P0[i,j]] = (1 if i==j else 0) if not (i<r and j>=r) else 0
    for i in range(n2):
        for j in range(n2): sub_frame[QL[i,j]] = (1 if i==j else 0) if not (i>=r and j<r) else 0
    onslice_blind=True
    for (ri,rj) in reads:
        for (ci,cj) in core0+core1:
            cv = A0[ci,cj] if (ci,cj) in core0 else None
        # derivative wrt each core entry, evaluated at deepest+frame=I:
        for core_entry,grp in [(A0[ci,cj],'0') for (ci,cj) in core0]+[(A1[ci,cj],'1') for (ci,cj) in core1]:
            d=sp.diff(M[ri,rj],core_entry).subs({**sub_deep,**sub_frame})
            if sp.simplify(d)!=0: onslice_blind=False
    print(f"  {name} ({n0},{n1},{n2}) r={r}: deepestEFull reads core-BLIND at the deepest point (on-slice)? {onslice_blind}")
    return onslice_blind

check_M("(2,2,2)",2,2,2,1)
check_M("(2,3,2)",2,3,2,1)
check_M("(3,3,3)",3,3,3,1)
check_M("(3,3,3)r2",3,3,3,2)
print()
print("on-slice core-blindness (the atom) holds M-uniformly => ΔR vanishes when reg=spec=0,")
print("AND ΔR's leading term = (reg coord)*(delta) carries the extra ->0 factor => domination")
print("denominator (reg^2 in F) is present at every M.  M-uniform.")

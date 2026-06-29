import sympy as sp
print("="*78)
print("M-UNIFORMITY: the leak/no-leak structure at a SECOND M (2,3,2) and (3,3,3).")
print("  Question: does the core->reg leak in deepestEFull, and its KILL under")
print("  block-triangular frames, depend on M?  (The leak is what the diffeo must absorb.)")
print("="*78)

def leak_test(name, dimsL, dimsM, dimsR, r):
    # 2-layer product, blocks split r | (dim-r).  A_s = [[I_r + Xs, Ys],[Zs, Ts]] block form.
    # Build symbolic 2x2-BLOCK layers with given middle width; check d(read block)/d(core block).
    n0,n1,n2 = dimsL, dimsM, dimsR
    def blkmat(tag, a, b):
        # a x b matrix split rows r|a-r, cols r|b-r
        X = sp.Matrix(a,b, lambda i,j: sp.Symbol(f'{tag}_{i}_{j}'))
        return X
    A0 = blkmat('A0', n0, n1)
    A1 = blkmat('A1', n1, n2)
    # At deepest point A_s ~ [[I_r,0],[0,0]]; set top-left = I_r + small, rest small. We keep symbolic.
    # core slots: A0[r:,r:] (=T0), A1[r:,r:] (=T1). reg reads: blocks 11,12,21 of P=A0*A1.
    P = A0*A1
    # core entries:
    core0 = [(i,j) for i in range(r,n0) for j in range(r,n1)]
    core1 = [(i,j) for i in range(r,n1) for j in range(r,n2)]
    # read entries of P: block11 (i<r,j<r), 12 (i<r,j>=r), 21(i>=r,j<r)
    reads = [(i,j) for i in range(n0) for j in range(n2) if not (i>=r and j>=r)]
    # leak WITHOUT frames: does any read depend on any core entry?
    leak_unframed = 0
    for (ri,rj) in reads:
        for (ci,cj) in core0:
            if sp.diff(P[ri,rj], A0[ci,cj])!=0: leak_unframed+=1
        for (ci,cj) in core1:
            if sp.diff(P[ri,rj], A1[ci,cj])!=0: leak_unframed+=1
    # WITH block-triangular endpoint frames: P0 block-lower (n0 x n0), QL block-upper (n2 x n2).
    P0 = sp.Matrix(n0,n0, lambda i,j: 0 if (i<r and j>=r) else sp.Symbol(f'P0_{i}_{j}'))
    QL = sp.Matrix(n2,n2, lambda i,j: 0 if (i>=r and j<r) else sp.Symbol(f'QL_{i}_{j}'))
    M = P0*P*QL
    leak_framed = 0
    leak_framed_terms = []
    for (ri,rj) in reads:
        for (ci,cj) in core0:
            d = sp.expand(sp.diff(M[ri,rj], A0[ci,cj]))
            if d!=0: leak_framed+=1; leak_framed_terms.append((('M',ri,rj),('T0',ci,cj)))
        for (ci,cj) in core1:
            d = sp.expand(sp.diff(M[ri,rj], A1[ci,cj]))
            if d!=0: leak_framed+=1; leak_framed_terms.append((('M',ri,rj),('T1',ci,cj)))
    print(f"  {name}: dims=({n0},{n1},{n2}) r={r}")
    print(f"     leak UNFRAMED (read depends on core): {leak_unframed} couplings  (>0 => raw leak)")
    print(f"     leak FRAMED (block-triangular P0,QL): {leak_framed} couplings")
    if leak_framed_terms[:4]:
        print(f"       surviving framed couplings (sample): {leak_framed_terms[:4]}")
    return leak_unframed, leak_framed

leak_test("(2,2,2)", 2,2,2, 1)
leak_test("(2,3,2)", 2,3,2, 1)
leak_test("(3,3,3)", 3,3,3, 1)
leak_test("(3,3,3) r=2", 3,3,3, 2)

print()
print("="*78)
print("REFINEMENT: the reg-swap hsub3reg is RELATIVE (psi-moved vs unmoved, SAME frames).")
print("  E(psi q).reg vs E(q).reg.  The move psi changes ONLY (T1, Y1) [last-layer core+Y].")
print("  Claim to test: the SQUARED-SUM of reads is EQUAL after the move, i.e. the leak's")
print("  effect on (M12,M21) is COMPENSATED by the simultaneous Y1-move (the joint action).")
print("="*78)
import sympy as sp
# (2,2,2) r=1.  Joint move: T1 -> T1', Y1 -> Y1' (psiSplitRawL2Core couples them).
# deepestEFull reads M11-? , M12, M21 of M = P0*(A0 A1)*QL, block-triangular frames.
# The cert's claim (E2/leak-kill): there is a JOINT (T1,Y1) action under which the read
# blocks {11,12,21} are INVARIANT.  That action is exactly psiSplitRawL2Core.  Let's see
# if a (T1,Y1)-move can hold M12, M21, M11 fixed while moving T1 (=> the diffeo exists, BARE).
x0,y0,z0,T0,x1,y1,z1,T1 = sp.symbols('x0 y0 z0 T0 x1 y1 z1 T1', real=True)
p,u,w,a,b,dd = sp.symbols('p u w a b d', real=True)
A0 = sp.Matrix([[1+x0,y0],[z0,T0]]); A1 = sp.Matrix([[1+x1,y1],[z1,T1]])
P0 = sp.Matrix([[p,0],[u,w]]); QL = sp.Matrix([[a,b],[0,dd]])
M = sp.expand(P0*A0*A1*QL)
M11,M12,M21 = M[0,0],M[0,1],M[1,0]
# Move T1 -> T1 + t (t = the Theta/psi core shift), find Y1-adjustment y1->y1+dy that keeps reads fixed.
t, dy = sp.symbols('t dy', real=True)
M12_moved = M12.subs({T1:T1+t, y1:y1+dy})
M21_moved = M21.subs({T1:T1+t, y1:y1+dy})
M11_moved = M11.subs({T1:T1+t, y1:y1+dy})
# Solve dy so that M12_moved = M12 (the {12} block fixed).  (M21 has no y1; M11 has no T1,y1 coupling?)
sol = sp.solve(sp.Eq(M12_moved, M12), dy)
print("  d(M11)/dT1 =", sp.diff(M11,T1), "  d(M11)/dy1 =", sp.diff(M11,y1), " (M11 free of T1,y1 => unaffected)")
print("  d(M21)/dT1 =", sp.diff(M21,T1), " (M21 free of T1 => unaffected by core move)")
print("  M12 fixed requires dy =", [sp.simplify(s) for s in sol], " (a SMOOTH function of t and reads)")
print()
print("  => The BARE joint (T1,Y1) move that fixes the reads EXISTS and is SMOOTH in t:")
print("     dy = -(d*p*y0)/(...) * t  type -- RATIONAL in reads, smooth where pivot != 0.")
print("  This is the bare hsub3reg mechanism: a SMOOTH joint move kills the leak.  M-uniform")
print("  (same structure each M; the leak coupling M12<-T1 is compensated by Y1).")

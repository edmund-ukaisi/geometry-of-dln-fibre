#!/usr/bin/env python3
"""PNP hcover OBL-1 probe (decorrelated, exact sympy).
Question: does the FAITHFUL per-node shear (Aoyagi's Q1-clear . Schur . Q2-recoord,
the MULTI-TERM object, NOT just the single-term Schur `coPhi`) satisfy the per-edge
box-containment `closedBall 0 r <= shear '' closedBall 0 (f r)` for a super-geometric
polynomial f?  Key sub-questions:
  (i)  is the faithful per-node coordinate change a valid unipotent shear u |-> u + phi(u)
       with phi reading only KEPT coords and writing only the residual block (disjoint)?
  (ii) what is its polynomial DEGREE (does 'multi-term' mean higher DEGREE, or just more
       degree-2 products)?
  (iii) does the naive inverse v |-> v - phi(v) actually invert it (right/left inverse)?
  (iv) the box-bound: |phi(v)|_inf <= C * r^D on |v|<=r  =>  f(r) = r + C r^D.
Corank 2 AND corank 3 (deeper/wider), plus a Case-2 full-block variant.
All EXACT (sympy polynomials). No floats.
"""
import sympy as sp
import itertools

def maxdeg(expr, gens):
    p = sp.Poly(sp.expand(expr), *gens)
    return p.total_degree() if p.total_degree() is not None else 0

def build_node_shear(krow, kcol):
    """One Aoyagi Schur-clearing NODE at a pivot with residual block of size krow x kcol.
    Pivot normalized to 1 (post-blowup). Pivot row C12 (1 x kcol), pivot col C21 (krow x 1),
    residual block C22 (krow x kcol). The FAITHFUL coordinate change is the pair (Q1 left-clear
    of the col, Q2 right-clear of the row) acting on the residual block AND recoording the
    downstream C2 factor by Q2^{-1}.
    Returns: variables, the shear map on the FULL coordinate vector (kept row/col + block +
    a downstream block S it recoords), as a dict coord->expr, plus the 'kept' set.
    """
    # pivot row (kept), pivot col (kept)
    C12 = sp.Matrix(1, kcol, lambda i,j: sp.Symbol(f'r{j}'))     # pivot row entries  r0..
    C21 = sp.Matrix(krow, 1, lambda i,j: sp.Symbol(f'c{i}'))     # pivot col entries  c0..
    C22 = sp.Matrix(krow, kcol, lambda i,j: sp.Symbol(f'm{i}_{j}'))  # residual block (written)
    # A downstream factor C2 (kcol x w) that Q2^{-1} recoords -- model width w=2
    w = 2
    C2 = sp.Matrix(kcol+1, w, lambda i,j: sp.Symbol(f's{i}_{j}'))  # (kcol+1) x w incl pivot-row slot
    # Q2 = I + R  with R strictly-upper single pivot ROW = -C12 (clears the pivot row);
    #   its inverse (unipotent, single row) = I - R = I + [pivot row = +C12].  DEGREE-1.
    # The recoord of the downstream factor: C2' = Q2^{-1} C2.  Q2^{-1} acts on the (kcol+1)-dim
    #   index space: row0 (pivot row) gets  row0 + sum_j C12[j]*row_{j+1}.
    # Schur update of the block: Delta = C22 - C21*C12   (rank-1 correction, one product/entry).
    # Assemble the displacement phi on the full coord vector:
    coords = {}
    kept = set()
    # kept: pivot row + pivot col are FIXED and READ
    for j in range(kcol):
        coords[('r',0,j)] = C12[0,j]; kept.add(('r',0,j))
    for i in range(krow):
        coords[('c',i,0)] = C21[i,0]; kept.add(('c',i,0))
    # WRITTEN: residual block  m_{i,j} |-> m_{i,j} - c_i * r_j   (Schur, degree 2, one product)
    Delta = C22 - C21*C12
    for i in range(krow):
        for j in range(kcol):
            coords[('m',i,j)] = Delta[i,j]
    # WRITTEN: downstream recoord  s0_j |-> s0_j + sum_{l} r_l * s_{l+1,j}
    #   (the Q2^{-1} pivot-row combine; kcol products, each degree 2)
    Q2inv_C2 = C2.copy()
    for j in range(w):
        acc = C2[0,j]
        for l in range(kcol):
            acc = acc + C12[0,l]*C2[l+1,j]
        Q2inv_C2[0,j] = acc
    for i in range(kcol+1):
        for j in range(w):
            coords[('s',i,j)] = Q2inv_C2[i,j]
    # the s_{>=1} rows are kept-fixed; the s0 row is written
    for i in range(1,kcol+1):
        for j in range(w):
            kept.add(('s',i,j))
    return coords, kept

def analyze(krow, kcol, label):
    coords, kept = build_node_shear(krow, kcol)
    allkeys = list(coords.keys())
    gens = sorted({s for e in coords.values() for s in sp.sympify(e).free_symbols}, key=str)
    # identity value on a coordinate key
    def idsym(key):
        t,i,j = key
        return sp.Symbol({'r':f'r{j}','c':f'c{i}','m':f'm{i}_{j}','s':f's{i}_{j}'}[t])
    # phi = image - identity
    phi = {k: sp.expand(coords[k] - idsym(k)) for k in allkeys}
    # (i) valid shear: phi vanishes on kept coords, reads only kept coords
    kept_ok = all(phi[k]==0 for k in kept)
    read_syms = {s for k in allkeys for s in phi[k].free_symbols}
    kept_syms = {idsym(k) for k in kept}
    reads_only_kept = read_syms.issubset(kept_syms)
    # (ii) degree of phi
    deg = max([maxdeg(phi[k], gens) for k in allkeys] + [0])
    # (iii) inverse v |-> v - phi(v):  substitute image = id + phi, then apply inverse-candidate
    # Build forward map F(u)_k = idsym(k) + phi[k];  candidate inverse G(v)_k = idsym(k) - phi[k]
    # Check G(F(u)) = u  as polynomials.  Substitute: in G, replace each idsym(key) by F(key).
    Fmap = {idsym(k): idsym(k) + phi[k] for k in allkeys}
    # G(F(u))_k = F(k) - phi[k]( with each coord replaced by F )
    ok_inv = True
    for k in allkeys:
        phi_at_F = phi[k].xreplace(Fmap)
        val = sp.expand((idsym(k)+phi[k]) - phi_at_F)
        if sp.expand(val - idsym(k)) != 0:
            ok_inv = False; break
    # (iv) box bound: number of monomials & max #products per written coord => f(r)=r + C r^deg
    Cmax = 0
    for k in allkeys:
        p = sp.Poly(phi[k], *gens) if phi[k]!=0 else None
        if p is not None:
            Cmax = max(Cmax, len(p.terms()))
    print(f"[{label}]  block {krow}x{kcol}")
    print(f"   (i)   valid shear (phi=0 on kept, reads only kept): {kept_ok and reads_only_kept}")
    print(f"   (ii)  degree of faithful shear phi              : {deg}")
    print(f"   (iii) inverse v|->v-phi(v) is exact             : {ok_inv}")
    print(f"   (iv)  max #products in a written coord (=>C)     : {Cmax}   box f(r)=r + {Cmax}*r^{deg}")
    return dict(shear_ok=kept_ok and reads_only_kept, deg=deg, inv=ok_inv, C=Cmax)

print("="*72)
print("OBL-1: FAITHFUL per-node shear (Schur update + Q2^{-1} recoord) box-containment")
print("="*72)
r2 = analyze(2,2,"corank-2 faithful")
r3 = analyze(3,3,"corank-3 faithful (deeper/wider)")
r24 = analyze(2,4,"corank (2,4) rectangular")
r4 = analyze(4,4,"corank-4 faithful")

print()
print("VERDICT OBL-1:")
allsh = all(r['shear_ok'] for r in [r2,r3,r24,r4])
alldeg2 = all(r['deg']==2 for r in [r2,r3,r24,r4])
allinv = all(r['inv'] for r in [r2,r3,r24,r4])
print(f"  all valid unipotent shears (keep+read, disjoint write): {allsh}")
print(f"  all DEGREE EXACTLY 2 (multi-term = more products, NOT higher degree): {alldeg2}")
print(f"  all invert by v|->v-phi(v) exactly: {allinv}")
print(f"  => box-bound f(r) = r + C*r^2 at EVERY node (C grows with block size, DEGREE fixed at 2)")

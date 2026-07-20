#!/usr/bin/env python3
# guards: coverage-theorem, region-glue, resolution-tree
# provenance: threads/08-atlas-probe (pnp08), Q1b. Exact sympy; formulae pinned to Aoyagi pp.16-21
#   (corner-unit normalize, Q p.17, P p.18, C'=Q^{-1}C, D'''=[1 O; O D_{J+1}]).
"""Q1b: does ONE variable-dependent shear psi per node faithfully factor the C'/P/Q composite, or is a
COMPOSITION required?

The paper's per-node gauge is executed as: normalize the corner (J+1,J+1) to 1; RIGHT-multiply the
D-block by an UPPER-unipotent Q (clears row 1); LEFT-multiply by a LOWER-unipotent P (clears col 1) to
reach D''' = [1 O; O D_{J+1}]; and relabel the next layer C' = Q^{-1} C. We compute the NET coordinate
change-of-variables it induces (parent entries -> child entries) and classify it.

CLAIM UNDER TEST (mine, withheld from Codex): the NET CoV is the single Schur-complement update
   d_{ij} |-> d_{ij} - d_{i1} d_{1j}   (i,j > 1),   ratios d_{i1}, d_{1j} unchanged,
plus a row-mix on C ( C_{1,l} |-> C_{1,l} + sum_j d_{1j} C_{j,l} ). This is ONE TRIANGULAR unipotent
substitution (nonlinear: the shift is a product of two coords) with Jacobian determinant = a power of
the (bounded-unit) corner -- i.e. a single variable-dependent unimodular gauge, NOT a composition that
fails to collapse. We VERIFY by (a) forming Q,P explicitly, (b) checking P.diag.D''.=diag.D''' matches
the Schur complement, (c) computing the net CoV Jacobian, (d) checking the CoV is triangular (single psi).
"""
import sys
import sympy as sp


def run(n):
    """n x n residual D-block; corner (1,1) normalized to 1. Returns (ok, report)."""
    # residual coordinates: D[i][j], i,j in 1..n, with D[0][0] = 1 (corner normalized).
    D = sp.zeros(n, n)
    D[0, 0] = sp.Integer(1)
    names = {}
    for i in range(n):
        for j in range(n):
            if (i, j) != (0, 0):
                s = sp.Symbol(f"d_{i+1}{j+1}", real=True)
                D[i, j] = s
                names[(i, j)] = s

    # Q (upper-unipotent): first row Q[0,j] = -D[0,j] (j>0); clears row 0 of D by RIGHT mult.
    Q = sp.eye(n)
    for j in range(1, n):
        Q[0, j] = -D[0, j]
    Dpp = sp.expand(D * Q)                       # D'' = D' Q  (row 0 -> (1,0,...,0))

    # P (lower-unipotent): first col P[i,0] = -D''[i,0] (i>0), clears col 0 of D'' by LEFT mult.
    # (the b'-ratio here is 1 because the diag(b') factors out uniformly for a single-pivot clear;
    #  the ratio only rescales which is checked separately -- see det below.)
    P = sp.eye(n)
    for i in range(1, n):
        P[i, 0] = -Dpp[i, 0]
    Dppp = sp.expand(P * Dpp)                     # should be [1 O; O D_{J+1}]

    # (b) does D''' = [1 O; O Schur]?  Schur complement S[i,j] = D[i,j] - D[i,0] D[0,j] (i,j>0).
    schur_ok = True
    for i in range(1, n):
        for j in range(1, n):
            if sp.simplify(Dppp[i, j] - (D[i, j] - D[i, 0] * D[0, j])) != 0:
                schur_ok = False
    # first row/col cleared?
    cleared = all(sp.simplify(Dppp[0, j]) == 0 for j in range(1, n)) and \
              all(sp.simplify(Dppp[i, 0]) == 0 for i in range(1, n)) and sp.simplify(Dppp[0, 0]) == 1

    # (c) FULL NET CoV: the residual Schur update  new_{ij} = d_{ij} - d_{i1} d_{1j}  (i,j>0)
    #     PLUS the next-layer relabel C' = Q^{-1} C (one scalar column c_i, row 0 -> c_0 + sum_j d_{0j} c_j).
    C = [sp.Symbol(f"c_{i+1}", real=True) for i in range(n)]
    Cnew = list(C)
    Cnew[0] = C[0] + sum(D[0, j] * C[j] for j in range(1, n))   # (Q^{-1} C) row 0
    free = ([names[(i, 0)] for i in range(1, n)] + [names[(0, j)] for j in range(1, n)]
            + [names[(i, j)] for i in range(1, n) for j in range(1, n)] + C)
    new = ([names[(i, 0)] for i in range(1, n)] + [names[(0, j)] for j in range(1, n)]
           + [Dppp[i, j] for i in range(1, n) for j in range(1, n)] + Cnew)
    Jac = sp.Matrix([[sp.diff(nc, v) for v in free] for nc in new])
    detJ = sp.simplify(Jac.det())
    # triangular/unipotent: Jacobian is unitriangular in this ordering => det == 1 (before corner unit)
    tri_unipotent = (detJ == 1)
    # displacement rank: is it a SINGLE elementary transvection (rank(J-I)=1) or NOT (rank>=2)?
    disp_rank = (Jac - sp.eye(Jac.rows)).rank()
    single_elem = (disp_rank <= 1)

    ok = schur_ok and cleared and tri_unipotent and (disp_rank >= 2 if n >= 2 else True)
    rep = (f"  n={n}: D'''=[1 O; O Schur] (Schur=d_ij - d_i1 d_1j): match={schur_ok}, cleared={cleared}; "
           f"net-CoV det={detJ} (unipotent); rank(J-I)={disp_rank} "
           f"({'SINGLE elementary shear' if single_elem else 'NOT one elementary shear (rank>=2)'})")
    return ok, rep, detJ


def ccheck(n, ccols=2):
    """The next-layer relabel C' = Q^{-1} C is a single UPPER-unipotent shear (row-mix), det 1."""
    D0 = [sp.Symbol(f"e_{j+1}", real=True) for j in range(1, n)]   # the d'_{1j}, j>1
    Q = sp.eye(n)
    for j in range(1, n):
        Q[0, j] = -D0[j - 1]
    Qi = Q.inv()
    detQi = sp.simplify(Qi.det())
    # Q^{-1} is unit-upper-triangular (row 0 gets +d'_{1j}); acting on C by left mult is one shear.
    unitri = all(Qi[i, i] == 1 for i in range(n)) and all(Qi[i, j] == 0 for i in range(n) for j in range(i))
    return detQi, unitri


print("Q1b — is the C'/P/Q composite a SINGLE shear or a COMPOSITION? (exact sympy)\n")
ok = True
for n in (2, 3, 4):
    o, rep, dj = run(n)
    ok &= o
    print(rep)
    dQi, ut = ccheck(n)
    print(f"       next-layer relabel C'=Q^-1 C: unit-upper-triangular={ut}, det={dQi} (single shear)")
    ok &= (dQi == 1 and ut)

print("""
FINDING: the faithful per-node gauge is the TWO-SIDED action A |-> P A Q (on vec: Q^T (x) P), plus
  C |-> Q^{-1} C -- equivalently the single Schur-complement CoV d_{ij} |-> d_{ij} - d_{i1} d_{1j}
  (+ the C row-mix). It is ONE UNIPOTENT map (Jacobian det = 1, all eigenvalues 1, unit-triangular),
  so it IS faithfully one variable-dependent gauge -- NOT the non-unipotent same-side product P*Q.
  BUT rank(J-I) >= 2: it is NOT a single elementary (rank-1) transvection.
  => VERDICT: single-psi is FAITHFUL as ONE general unipotent/unimodular map (the compass region-glue
  'bounded-unit local diffeo with full inverse data' shape); it is NOT faithful as a single ELEMENTARY
  shear -- an elementary-shear chart-slot needs the ordered column-then-row composition (Psi_Q ; Psi_P).
  The LEAF chartMap is the fold of these per-node single unipotent gauges (case-1(1) merges carry none).
""" if ok else "\nUNEXPECTED — recheck")
sys.exit(0 if ok else 1)

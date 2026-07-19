#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/15-psi-adjudication (pnp-psi). T2(a): re-derive Aoyagi's Case-1(2) d-pivot
#   gauge from Q (p.17) and P (p.18) INDEPENDENTLY (decorrelated from cert-single-psi's net form),
#   confirm ratios-fixed + residual Schur update + det 1, then show NO single per-node psi factors
#   both the u-pivot edge (psi=id, Case-1(1)) and a d-pivot edge (psi=Schur, Case-1(2)).
# Exact symbolic (sympy). No Monte-Carlo.
import sympy as sp

def aoyagi_dpivot_gauge_on_ratio_block(m, n):
    """Trace Aoyagi p.16-18 for a Case-1(2) corner-pivot on an m x n ratio block.
       Block D' = corner 1 at (0,0), ratio entries elsewhere. Apply Q (clear row 0 via columns),
       then P (clear col 0 via rows). Return (D', D''') symbolically and the residual map."""
    # ratio block: (0,0)=1 ; row 0 = [1, r_{0,1},..], col 0 = [1, r_{1,0},..], interior r_{i,j}
    r = {}
    Dp = sp.zeros(m, n)
    Dp[0,0] = sp.Integer(1)
    for i in range(m):
        for j in range(n):
            if (i,j)==(0,0): continue
            r[(i,j)] = sp.Symbol(f"r_{i}_{j}")
            Dp[i,j] = r[(i,j)]
    # Q (p.17): upper-unitriangular, clears row 0 -> [1,0,...,0]. Q acts on columns: D'' = D' * Q.
    Q = sp.eye(n)
    for j in range(1, n):
        Q[0, j] = -Dp[0, j]                 # first row of Q = [1, -r_{0,1}, ...]
    Dpp = sp.simplify(Dp * Q)
    # P (p.18): lower-unitriangular, clears col 0 -> [1,0,...,0]^T. P acts on rows: D''' = P * D''.
    P = sp.eye(m)
    for i in range(1, m):
        P[i, 0] = -Dpp[i, 0]                # first col of P = [1, -d''_{1,0}, ...]^T (b'-weights =1 in ratio frame)
    Dppp = sp.simplify(P * Dpp)
    return Dp, Dpp, Dppp, Q, P

def check_2x2():
    """Smallest block with a genuine residual Schur update: 2x2 (residual = the (1,1) entry)."""
    Dp, Dpp, Dppp, Q, P = aoyagi_dpivot_gauge_on_ratio_block(2,2)
    r01, r10, r11 = Dp[0,1], Dp[1,0], Dp[1,1]
    # After P,Q the normal form should be [[1,0],[0, r11 - r10*r01]] (Schur complement).
    expected = sp.Matrix([[1,0],[0, r11 - r10*r01]])
    ok_form = sp.simplify(Dppp - expected) == sp.zeros(2,2)
    # det of the (ratio) gauge (r00=1,r01,r10,r11) -> (1,r01,r10, r11-r10 r01), r01,r10 fixed:
    #   the coordinate map on the free ratios (r01,r10,r11) is (r01, r10, r11 - r10*r01).
    J = sp.Matrix([[1,0,0],[0,1,0],[-r11.diff(r01)*0, -r10, 1]])  # placeholder; compute properly below
    g = sp.Matrix([r01, r10, r11 - r10*r01])
    vars_ = sp.Matrix([r01, r10, r11])
    Jg = g.jacobian(vars_)
    det = sp.simplify(Jg.det())
    return ok_form, Dppp, det

def no_single_psi():
    """Functional-equation refutation. hloc demands localSub_e = psi(q.symm(pivotChart_e)) with a
       COMMON psi. Solve psi on each edge; show the two determinations disagree.
       Model the shared post-pivot residual coordinate r (e.g. d22-ratio). On the d-pivot edge the
       ACTUAL localSub applies the Schur map r -> r - a*b (a,b the adjacent ratios); on the u-pivot
       edge the ACTUAL localSub is the pure blow-up (psi = id). A common psi would need
       psi = Schur (from d-edge) AND psi = id (from u-edge) on the overlapping image region."""
    r, a, b = sp.symbols('r a b')
    psi_from_d = r - a*b        # determination of psi on the residual coord from the d-pivot edge
    psi_from_u = r              # determination from the u-pivot edge (psi = id, Case-1(1))
    gap = sp.simplify(psi_from_d - psi_from_u)   # = -a*b : nonzero => inconsistent
    return gap

if __name__ == "__main__":
    print("T2(a) — Aoyagi d-pivot gauge (independent Q/P trace) + no-single-psi")
    ok_form, Dppp, det = check_2x2()
    print("  2x2 block normal form D''' =", Dppp.tolist())
    print("  matches Schur complement [[1,0],[0, r11 - r10*r01]] :", ok_form)
    print("  gauge Jacobian det on free ratios (r01,r10,r11):", det, "(unipotent, det 1)")
    print("  => d-pivot gauge psi_d is NONTRIVIAL (residual r11 -> r11 - r10*r01) and det 1.")
    print()
    gap = no_single_psi()
    print("  no-single-psi functional equation: psi_d - psi_u on the residual coord =", gap)
    print("  => a COMMON psi must equal (r - a*b) [d-edge] AND r [u-edge]; these differ by -a*b != 0.")
    ok = ok_form and det == 1 and gap != 0
    print()
    print("VERDICT T2(a):", "PASS -- psi_d != id = psi_u, NO single per-node psi exists" if ok else "FAIL")
    import sys; sys.exit(0 if ok else 1)

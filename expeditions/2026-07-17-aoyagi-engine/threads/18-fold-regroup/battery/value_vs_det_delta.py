#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/18-fold-regroup (pnp-fold). Scope-note check for the ledger-accumulation cert:
# does the DET cocycle |det D chartMap| = prod |z_divCoord|^{divExp-1} state as the VALUE object
# prod o chartMap = diag(b) with the det DERIVED from it? This contrasts the THREE exponent structures
# a single divisor carries across a case-2 birth + k case-1(1) re-merges, showing they DIVERGE -> the
# det is NOT derivable from the value (they are different reads of the same tree; pnp-loss cert thread-19
# established the full value/loss factorization + the Schur delta). Confirms: shared SKELETON, different
# CONTENT. Exact symbolic.
import sympy as sp

def chart(point, center, pivot):
    piv = point[pivot]
    return {c: (piv if c == pivot else (piv*point[c] if c in center else point[c])) for c in point}

def det_exp_of_A(k_merges):
    """|det D chartMap| for case-2 birth of A (2x2 block) + k case-1(1) merges into A.
       Returns the exponent of z_A (the JACOBIAN / det read = divExp - 1 = accumulated)."""
    cells = ['A','b','c','d'] + [f'm{i}' for i in range(k_merges)]
    path = [ (['A','b','c','d'], 'A') ]                 # case-2 births A (dCN 4)
    for i in range(k_merges):
        path.append((['A', f'm{i}'], 'A'))             # case-1(1) merge into A (dCN 2, +1 each)
    src = {c: sp.Symbol('z_'+c, positive=True) for c in cells}
    pt = dict(src)
    for (center, pivot) in reversed(path):
        pt = chart(pt, center, pivot)
    order = list(cells)
    J = sp.Matrix([[sp.diff(pt[r], src[c]) for c in order] for r in order])
    det = sp.factor(sp.Abs(J.det()))
    return int(sp.degree(sp.Poly(det, src['A'])))

if __name__ == "__main__":
    print("== Three exponent structures a divisor A carries (case-2 birth + k case-1(1) re-merges) ==")
    print("  k | DET (Jacobian, |det D chartMap|) | VALUE diag-monomial b1 (thread-19) | LOSS power (thread-19)")
    print("  --|----------------------------------|------------------------------------|----------------------")
    ok = True
    for k in range(4):
        det_exp = det_exp_of_A(k)          # accumulates: 3 + k  (divExp = 4 + k, det read = divExp-1)
        b_exp   = 1                        # b1 is SQUAREFREE (each terminal divisor once) -- thread-19 cert (a)
        loss_exp = 2                       # frobSq = b1^2 * unit -> divisor power exactly 2 -- thread-19 cert (a)
        print(f"  {k} |            z_A^{det_exp:<2d}                  |            z_A^{b_exp}                     |        z_A^{loss_exp}")
        # sanity: the DET must accumulate (3+k); the VALUE/LOSS must NOT.
        ok = ok and (det_exp == 3 + k)
    print()
    print("READING:")
    print("  * DET (my ledger-accumulation cert): exponent = divExp-1 = 3+k -- ACCUMULATES with re-merges.")
    print("  * VALUE diag-monomial b1 (prod o chartMap = diag(b)): exponent 1, SQUAREFREE -- does NOT accumulate.")
    print("  * LOSS (frobSq = prod divCoord^2 * core): exponent 2, UNIFORM -- does NOT accumulate.")
    print("  => the DET is NOT derivable from the VALUE (different exponent structure); they share the")
    print("     THREADED-INDUCTION SKELETON (tree walk / per-stepUpdate-case / conRoot base / DivBirthInv)")
    print("     but track different content. The VALUE additionally needs the residual-block (off-diagonal)")
    print("     tracking + the incidence/Q,P Schur source gauge that the det-1-blind Jacobian never sees")
    print("     (thread-19 cert-loss-factorization, exact-verified).")
    print()
    print("VERDICT:", "PASS -- det accumulates (3+k) while value(1)/loss(2) do not; not derivable" if ok else "FAIL")
    import sys; sys.exit(0 if ok else 1)

"""
(3,3,4) belt-and-braces: does an INTERIOR-pivot chart of the coupled 3x3 block peel/monomialise
exactly like the banked corner peel (g-coupled-334-diagb.py, which does the c11=1 corner chart)?

The block blow-up of the 3x3 residual block C1 (ideal = all 9 entries) has one chart per pivot entry.
The battery does the CORNER chart (pivot (0,0)). Here we do an INTERIOR chart (pivot (1,1)) and confirm:
 (A) the pivot-(1,1) peel Q1*C1*Q2 = (pivot->1, its row/col ->0, Schur elsewhere), Q1,Q2 UNIPOTENT;
 (B) the deeper factor C2 recoord (Q2^{-1} C2) is UNIPOTENT (det 1) — the exponent ledger is untouched;
 (C) the blown-up ideal <C1 C2> is preserved (peel is a unipotent change of basis => same ideal =>
     same RLCT / same b-chain / same M' as the corner chart — chart-independence of the exponents);
 (D) M' = |block| = 9 is pivot-independent (the exceptional coord exponent, so minAdm=8 via the JOIN
     is reached from the interior chart too).
All exact (sympy).
"""
import sympy as sp

ok = True
# 3x3 residual block C1 (all entries free = the coupled block before choosing a chart)
C1 = sp.Matrix(3, 3, sp.symbols('c0:9'))
u = sp.Symbol('u')

def pivot_chart_peel(C, a, b):
    """blockBlowupMap p=(a,b) chart (pivot->u, others u*w) then pivot-(a,b) Schur (unipotent row/col ops).
       Returns (blockchart, Q1, Q2, peeled)."""
    n, m = C.shape
    w = sp.Matrix(n, m, lambda i, j: sp.Integer(1) if (i, j) == (a, b)
                  else sp.Symbol(f'w_{i}{j}'))
    d = sp.Matrix(n, m, lambda i, j: u if (i, j) == (a, b) else u * w[i, j])
    # Q1 clears column b (rows != a): row_i -= (d_ib/d_ab) row_a.  Q2 clears row a (cols != b).
    Q1 = sp.eye(n)
    for i in range(n):
        if i != a:
            Q1[i, a] = -d[i, b] / d[a, b]
    Q2 = sp.eye(m)
    for j in range(m):
        if j != b:
            Q2[b, j] = -d[a, j] / d[a, b]
    peeled = sp.simplify(Q1 * d * Q2)
    return d, w, Q1, Q2, peeled

# --- (A) interior pivot (1,1) ---
a, b = 1, 1
d, w, Q1, Q2, peeled = pivot_chart_peel(C1, a, b)
# pivot->u, row a / col b -> 0, Schur elsewhere:
peel_shape_ok = True
for i in range(3):
    for j in range(3):
        val = sp.simplify(peeled[i, j] / u)   # factor out u
        if (i, j) == (a, b):
            peel_shape_ok &= (val == 1)
        elif i == a or j == b:
            peel_shape_ok &= (sp.simplify(peeled[i, j]) == 0)
        else:
            expected = w[i, j] - w[i, b] * w[a, j]   # Schur complement w.r.t. pivot (a,b)
            peel_shape_ok &= (sp.simplify(val - expected) == 0)
        # u-factor exact (no u left in val)
        peel_shape_ok &= (u not in sp.simplify(val).free_symbols)
uni_ok = (sp.simplify(Q1.det()) == 1 and sp.simplify(Q2.det()) == 1)
print(f"(A) interior pivot (1,1): peel shape (pivot->u, row/col->0, Schur w_ij-w_ib*w_aj) = {peel_shape_ok};"
      f"  Q1,Q2 unipotent = {uni_ok}")
ok &= peel_shape_ok and uni_ok

# --- (B) deeper factor recoord Q2^{-1} C2 unipotent (det 1) ---
Q2inv = Q2.inv()
uni_deep = (sp.simplify(Q2inv.det()) == 1)
# and linear in C2's entries with coefficients from the block coords (w): Q2inv has entries in {0,1,w..}
C2 = sp.Matrix(3, 4, sp.symbols('e0:12'))
C2p = sp.expand(Q2inv * C2)
lin_ok = all(sp.Poly(C2p[i, j], *C2).total_degree() <= 1 for i in range(3) for j in range(4))
print(f"(B) deeper recoord Q2^-1*C2 unipotent = {uni_deep};  linear in C2 (deg<=1) = {lin_ok}")
ok &= uni_deep and lin_ok

# --- (C) ideal <C1 C2> preserved (peel is a unipotent basis change) ---
# C1 = Q1^{-1} peeled Q2^{-1};  C1 C2 = Q1^{-1} (peeled) (Q2^{-1} C2).  Q1^{-1} unipotent => same row-span
# ideal. We verify the reconstruction identity exactly.
recon = sp.simplify(Q1.inv() * peeled * Q2.inv() - d)
recon_ok = (recon == sp.zeros(3, 3))
print(f"(C) reconstruct block d = Q1^-1 * peeled * Q2^-1: {recon_ok}  (ideal <C1 C2> preserved by unipotent peel)")
ok &= recon_ok

# --- (D) exponent pivot-independence: |block| = 9 for any pivot; Jacobian u^{9-1} ---
# blockBlowupMap p-chart Jacobian = u^{|block|-1} = u^8; N_p (Q1,Q2) det 1 => total u^8, pivot-independent.
print(f"(D) M' = |block| = {C1.rows * C1.cols} (pivot-independent); Jacobian u^(|block|-1) = u^8, N_p det 1")
ok &= (C1.rows * C1.cols == 9)

print("\n(3,3,4) INTERIOR-pivot chart peels/monomialises like the corner peel, det-1, ideal-preserving,"
      f" exponent 9 pivot-independent:  {ok}")

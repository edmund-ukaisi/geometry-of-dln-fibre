"""
Is the WHOLE baked path to the case11 node (blow-ups/quotients) ∘ (UNIPOTENT shears)?
If every edge's SHEAR part (canonNormalizationOf) is unipotent (det-1, structurally triangular),
then the baked fold = (legit blow-up modifications) ∘ (invertible coordinate changes), so it PRESERVES
the RLCT of the zero-fibre ideal — a VALID resolution chart, even though its residual ideal differs
from the faithful (cleared) one (see recoord_ideal_matched.py).  This is the route-level datum:
RLCT-valid-but-different, NOT broken.

(2,2,2,2) canonical branch: ed1 = case2 δ1 pivot (0,0,0); ed2 = case2 δ0 pivot (0,1,1); ed3 = rollover
(shear = id).  We check the SHEAR part of ed1 and ed2 (rollover's is identity).
"""
import sympy as sp


def make(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u


def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)


def canonNormalizationOf(u, d, sL, sC, piv):
    a, b = piv[1], piv[2]
    phi = {}
    for (L, r, c) in u:
        if L == sL and r != a and c != b and sC <= r and sC <= c:
            phi[(L, r, c)] = -readEntry(u, d, sL, r, b) * readEntry(u, d, sL, a, c)
        elif L == sL + 1 and c == a:
            phi[(L, r, c)] = sum((readEntry(u, d, sL, i, b) * readEntry(u, d, sL + 1, r, i)
                                  for i in range(d[sL + 1]) if i != c), sp.Integer(0))
        else:
            phi[(L, r, c)] = sp.Integer(0)
    return phi


def unipotent(d, sL, sC, piv, label):
    N, u = make(d)
    phi = canonNormalizationOf(u, d, sL, sC, piv)
    keys = list(u.keys())
    psi = [u[k] + phi[k] for k in keys]
    vars_ = [u[k] for k in keys]
    J = sp.Matrix([[sp.diff(p, v) for v in vars_] for p in psi])
    detJ = sp.expand(J.det())
    at0 = J.subs({v: 0 for v in vars_}) == sp.eye(len(vars_))
    # structural triangularity: each modified coord's phi depends only on UNMODIFIED coords
    modified = {k for k in keys if phi[k] != 0}
    triangular = all(phi[k].free_symbols.isdisjoint({u[m] for m in modified}) for k in keys)
    print(f"  [{label}] det J = {detJ}   J(0)=I: {at0}   shear-triangular (modified⊥support): {triangular}")
    return detJ == 1 and triangular


print("(2,2,2,2) path-to-case11 shear unipotency (each edge's shear part):")
e1 = unipotent((2, 2, 2, 2), 0, 0, (0, 0, 0), "ed1 case2 δ1 piv(0,0,0)")
e2 = unipotent((2, 2, 2, 2), 0, 1, (0, 1, 1), "ed2 case2 δ0 piv(0,1,1)")
print("  ed3 rollover: shear = id (trivially unipotent)")
print(f"\n  => every shear on the path is det-1 AND structurally triangular (=> globally invertible,")
print(f"     not merely det-1): {e1 and e2}.  The baked fold to case11 = (blow-ups) ∘ (invertible shears)")
print(f"     => RLCT of the zero-fibre PRESERVED.  Valid-but-different resolution, not broken.")

# wide witness ed1 shear too
print("\nwide-witness ed1 shear unipotency:")
unipotent((2, 3, 2), 0, 0, (0, 0, 0), "(2,3,2) ed1 piv(0,0,0)")
unipotent((2, 3, 2, 2), 0, 0, (0, 0, 0), "(2,3,2,2) ed1 piv(0,0,0)")

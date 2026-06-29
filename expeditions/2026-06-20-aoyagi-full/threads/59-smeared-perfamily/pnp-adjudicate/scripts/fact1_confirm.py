import sympy as sp

# Confirm the TALL free case FAILS at an exact rational point (numerator nonzero, det nonzero).
def rational_point_test(M0, M1, r, seed_offset=0):
    s = M1 - r
    import random
    random.seed(12345+seed_offset)
    A = sp.Matrix(M0, M1, lambda i,j: sp.Rational(random.randint(1,9), random.randint(1,5)))
    P1 = A[:, :r]; P2 = A[:, r:]
    G = P1.T*P1
    dG = G.det()
    if dG == 0:
        return f"M0={M0},M1={M1},r={r}: Gram det 0 at this point (re-seed)"
    Lam0 = G.inv()*P1.T*P2
    resid = sp.simplify(P1*Lam0 - P2)
    return f"M0={M0},M1={M1},r={r}: detG={dG} (nonzero) | P1*Lam0-P2 zero? {resid.is_zero_matrix} | resid={resid.tolist() if not resid.is_zero_matrix else '0'}"

# Tall free P1 (r=2<M0=3) at a concrete rational point -- expect FAIL (nonzero residual, det nonzero)
print("TALL free, exact point:", rational_point_test(3,3,2))
print("TALL free, exact point (2):", rational_point_test(4,5,2, seed_offset=7))

# r>M0 regime: confirm Gram rank <= M0 < r so det == 0 ALWAYS (off-pole empty)
def gram_rank(M0,M1,r):
    A = sp.Matrix(M0, M1, lambda i,j: sp.Symbol(f'a_{i}_{j}'))
    P1 = A[:, :r]
    G = P1.T*P1   # r x r, but rank(P1) <= min(M0,r) = M0 if r>M0
    return f"r={r}>M0={M0}: G is {r}x{r}, rank(P1)<=M0={M0}<r, so det(G) symbolic = {sp.simplify(G.det())}"
print(gram_rank(2,4,3))
print(gram_rank(3,5,4))

"""
r=0 fibre (mult = 0) Jacobian rank + minor analysis.

For r=0 the fibre is the zero-product locus  mult(A) = A_N...A_1 = 0.
A point of the TOP stratum of the zero-product variety has a canonical form: a
"binary string" (Kostant) telling, at each internal node, whether the rank drops.
We pick a top component and generate exact-rational generic points on it, then
compute the exact rank of the fibre Jacobian and which (codim)-minors survive.

Top stratum of zero-product for width-w internal nodes: dimension vector
(w,...,w) length N+1, product 0. The codim-minimal components correspond to a
single full-rank-drop somewhere; generically each A_i is full rank except the
"break" is realized by the composite hitting a kernel. We instead just sample
random tuples on V(mult) by parametrizing image/kernel chains.
"""
import sympy as sp
import random
from fibjac import build_symbolic, mult_product, E_r

def generic_zero_product_point(d, seed):
    """Construct an exact tuple with A_N...A_1 = 0 by routing through a chain of
    subspaces: choose at each step a rank so the composite kernel grows; simplest
    generic top point: make ONE factor have a 1-dim kernel aligned so product=0.
    We do it constructively: pick a 'cut' position c in 1..N. Build A_1..A_c with
    generic entries, let K = column space chain; force A_{c..} to annihilate.

    Simplest robust approach for width-2, r=0: choose unit vectors so that
    im(A_c..A_1) lands in ker(A_{c+1}). We realize a rank-1 through-channel that
    gets killed at the cut. Construct via random rank-deficient factor at cut.
    """
    rng = random.Random(seed)
    N = len(d) - 1
    def rq(): return sp.Rational(rng.randint(-3,3), rng.choice([1,2]))
    # choose cut node c in [0, N-1]: factor index c (0-based, i.e. A_{c+1}) is the
    # one whose kernel catches the incoming image.
    c = rng.randrange(N)
    factors = []
    # incoming image vector chain: start with generic vectors
    for i in range(N):
        rows, cols = d[i+1], d[i]
        M = sp.Matrix(rows, cols, lambda a,b: rq())
        factors.append(M)
    # Now force product zero: compute prefix images and rank-deficient cut.
    # Easiest exact construction: make the FULL product zero by left/right kernel.
    # Build A so that A_{c+1} (factor index c) kills the column space of prefix.
    # prefix = A_c...A_1 (factors[0..c-1]); its columns span a subspace V of k^{d_c}.
    # we want A_{c+1} (factors[c]) to vanish on V.
    if c == 0:
        # kill at first factor: make factors[0] = 0 on a generic 1-dim? Need full product 0.
        # set factors[0] columns to 0 -> product 0 but that's deepest; instead pick c>=1 if possible
        if N >= 2:
            c = 1
        else:
            factors[0] = sp.zeros(d[1], d[0])
            return factors
    prefix = factors[0]
    for i in range(1, c):
        prefix = factors[i] * prefix
    # prefix : d_c x d_0. choose A_{c+1} = factors[c] (d_{c+1} x d_c) to annihilate
    # the column space of prefix. Build factors[c] with rows orthogonal to col(prefix)?
    # We want factors[c] * prefix = 0. So each row of factors[c] is in left-kernel
    # of prefix. left-kernel of prefix (d_c x d_0): vectors v in k^{d_c} with v^T prefix = 0.
    LK = prefix.T.nullspace()   # nullspace of prefix^T = left null of prefix
    if not LK:
        return None
    rows_c, cols_c = d[c+1], d[c]
    Mc = sp.zeros(rows_c, cols_c)
    for a in range(rows_c):
        # random combination of left-kernel basis vectors
        v = sp.zeros(cols_c, 1)
        for w in LK:
            v += rq() * w
        for b in range(cols_c):
            Mc[a, b] = v[b]
    factors[c] = Mc
    return factors

def jac_rank_and_minors(d, r, factors_num, want_minors=False):
    factors_sym, syms = build_symbolic(d)
    subs = {}
    for i in range(len(factors_sym)):
        rows, cols = factors_sym[i].shape
        for a in range(rows):
            for b in range(cols):
                subs[factors_sym[i][a,b]] = factors_num[i][a,b]
    P = mult_product(factors_sym)
    E = E_r(d[-1], d[0], r)
    F = P - E
    Fentries = [F[a,b] for a in range(d[-1]) for b in range(d[0])]
    J = sp.Matrix([[sp.diff(f, s) for s in syms] for f in Fentries])
    Jnum = J.subs(subs)
    rk = Jnum.rank()
    return rk, Jnum, syms, Fentries

if __name__ == "__main__":
    d = [2,2,2,2,2]; r = 0
    N = len(d)-1
    dimRep = sum(d[i+1]*d[i] for i in range(N))
    print(f"d={d} r={r}: dimRep={dimRep}, cuteqs={d[-1]*d[0]}, expected codim=3")
    ranks = []
    for seed in range(40):
        pt = generic_zero_product_point(d, seed)
        if pt is None: continue
        P = mult_product(pt)
        if sp.simplify(P) != sp.zeros(d[-1], d[0]):
            continue  # not on fibre
        rk, Jnum, syms, F = jac_rank_and_minors(d, r, pt)
        ranks.append(rk)
    from collections import Counter
    print("Jacobian rank distribution over generic zero-product points:", Counter(ranks))

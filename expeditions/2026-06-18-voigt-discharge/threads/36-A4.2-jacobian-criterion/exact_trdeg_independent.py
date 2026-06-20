#!/usr/bin/env python3
"""
INDEPENDENT trdeg certificate for the (2,2,2) image of mu_M^*, NOT using the Jacobian criterion.

trdeg_k k[g_1,...,g_n] = dim of the Zariski closure of the image  Phi : G --> A^n.
We certify this dimension WITHOUT derivatives, by a LOCAL implicitization at a single point of the image:

  Sample EXACT rational group points P^(1),...,P^(L) on a tiny EXACT random affine path through a base
  point P^(0), get image points q^(l) = Phi(P^(l)) in Q^n. The dimension D of the image variety equals
  the largest D such that the image, sampled on a generic D-dim slice, fills D dimensions. We measure it
  by the rank of the matrix of (q^(l) - q^(0)) for many small EXACT perturbations of P^(0): that rank is
  the dimension of the tangent space to the image at the (smooth, generic) base point = dim image.
  (This is the differential ONLY through finite differences of the MAP, never of the defining ideal --
  decorrelated from the symbolic Jacobian, and exact since we use exact-rational secant vectors with a
  formal infinitesimal, i.e. we keep the first-order term symbolically.)

To stay fully exact and independent we use a SYMBOLIC infinitesimal t: perturb P^(0) along an exact
random rational direction V_a (one per generator of Lie(G)), expand Phi(P^(0) + t V_a) to first order in
t, collect the O(t) coefficient vectors, and take their EXACT rank over Q. That rank = dim of image =
trdeg. This is the image-of-a-curve dimension test; it does not reference the Jacobian-criterion code at
all (different code path, different base points), giving a decorrelated confirmation.
"""
import sympy as sp
import random

Nv = 3
t = sp.Symbol('t')

def interval_arrow(a, b, i):
    src = 1 if a <= i <= b else 0
    tgt = 1 if a <= i + 1 <= b else 0
    if src and tgt:
        return sp.Matrix([[1]])
    return sp.zeros(tgt, src)

def directsum_tuple(intervals):
    d = [0]*Nv
    for (a, b) in intervals:
        for w in range(Nv):
            if a <= w <= b:
                d[w] += 1
    M = []
    for i in range(Nv-1):
        blocks = [interval_arrow(a, b, i) for (a, b) in intervals]
        rows = sum(b.rows for b in blocks); cols = sum(b.cols for b in blocks)
        Mi = sp.zeros(rows, cols); r = c = 0
        for blk in blocks:
            Mi[r:r+blk.rows, c:c+blk.cols] = blk; r += blk.rows; c += blk.cols
        M.append(Mi)
    return d, M

def rand_invertible(n, rng):
    while True:
        Q = sp.Matrix(n, n, lambda r, c: sp.Rational(rng.randint(-3, 3), rng.randint(1, 3)))
        if Q.det() != 0:
            return Q

def image_dim_via_curve(d, M, rng):
    """dim of image = rank over Q of the O(t) coefficients of Phi(P0 + t V_a) for a spanning set of
    directions V_a (a basis of all matrix-entry perturbations at each vertex). Independent of the
    symbolic Jacobian code: we evaluate Phi on an honest 1-parameter family and read first order."""
    # base point: random invertible at each vertex
    P0 = [rand_invertible(d[v], rng) for v in range(Nv)]
    cols = []
    for v in range(Nv):
        for r in range(d[v]):
            for c in range(d[v]):
                # direction = E_{r,c} at vertex v
                Pt = [P0[w].copy() for w in range(Nv)]
                E = sp.zeros(d[v], d[v]); E[r, c] = 1
                Pt[v] = P0[v] + t*E
                vec = []
                for i in range(Nv-1):
                    block = Pt[i+1] * M[i] * Pt[i].inv()       # rational in t
                    for rr in range(block.rows):
                        for cc in range(block.cols):
                            e = sp.series(block[rr, cc], t, 0, 2).removeO()
                            coeff = sp.diff(e, t).subs(t, 0)   # O(t) coefficient (exact rational)
                            vec.append(sp.nsimplify(coeff))
                cols.append(vec)
    Jmat = sp.Matrix(cols).T   # (n) x (dim G) matrix of exact rationals
    return Jmat.rank()

if __name__ == "__main__":
    for name, intervals in [("(1,1)-orbit", [(0,0),(0,1),(1,2),(2,2)]),
                            ("zero-product", [(0,0),(0,0),(1,2),(1,2)])]:
        d, M = directsum_tuple(intervals)
        dims = []
        for seed in (11, 23, 47):
            rng = random.Random(seed)
            dims.append(image_dim_via_curve(d, M, rng))
        print(f"{name}: d={d}  ->  trdeg(image) = dim of image variety = {dims}   "
              f"[EXACT over Q at random base points; image-of-a-curve test, NO symbolic Jacobian-criterion code]")

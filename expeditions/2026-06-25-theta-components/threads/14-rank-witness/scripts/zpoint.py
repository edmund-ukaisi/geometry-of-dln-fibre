"""
Generic point sampler for a chosen TOP component of the shifted zero-product
variety  Z(dsh) = { B = (B_1,...,B_N) : B_N...B_1 = 0 }  on dim vector
dsh = (e_0,...,e_N).

Principled construction (Kostant / rank-pattern):
A representation B of the A_{N+1} quiver with B_N...B_1 = 0 is determined up to
the GL-orbit by the ranks of all the composites
    rho(i,j) := rank( B_j B_{j-1} ... B_i )    for 1 <= i <= j <= N
(plus rho(i,i-1) = e_{i-1}).  The zero-product condition is rho(1,N) = 0.

The TOP (codim-minimal) components are the GL-orbit closures of the orbits whose
composite-rank pattern is "as large as possible subject to rho(1,N)=0".  We
generate a generic point of a chosen pattern by building B as block maps along a
chain of generic subspaces realizing exactly those ranks.

Simplest robust realization used here: choose a "cut profile" = a non-increasing
rank chain  r_0=e_0 >= r_1 >= ... >= r_N  with r_N forced so the full composite
is 0, where r_i = rank(B_i...B_1) = dim of the image of the prefix.  We require
the product to be 0, i.e. the final image after B_N is 0: r_N = 0.  Each B_i maps
a generic e_{i-1}-space onto a generic r_i-subspace of k^{e_i}, full rank r_i,
with kernel chosen generically.  The image chain r_i is the data; the dense orbit
of a top component is one extremal chain.

We build B_i explicitly: B_i = (random e_i x r_{i-1} full-col-rank) composed with
a projection picking the prefix image, times (random r_{i-1} x e_{i-1} of rank
r_i acting on the prefix image)...  Cleaner: maintain an explicit basis matrix
Img (e_{i-1} x r_{i-1}) of the running image; choose B_i to act on it with rank
r_i and send everything else generically, while ensuring B_N kills the last image.

Implementation: we parametrize by the image-dimension chain and build each B_i as
    B_i = Vimg_i * M_i * Pi_{i-1}
won't be generic enough. Instead we directly build full matrices then *correct*
the last factor to kill the running image (mirroring r0_rank but generalized to
arbitrary widths and an arbitrary single internal cut, and to multi-cut via
sequential image truncation).
"""
import sympy as sp
import random


def _randmat(rng, rows, cols, lo=-4, hi=4):
    return sp.Matrix(rows, cols, lambda a, b: sp.Rational(rng.randint(lo, hi), rng.choice([1, 2, 3])))


def _full_rank_mat(rng, rows, cols, rank, lo=-4, hi=4, tries=60):
    """random rows x cols matrix of exactly the given rank (rank <= min(rows,cols))."""
    assert rank <= min(rows, cols)
    if rank == 0:
        return sp.zeros(rows, cols)
    for _ in range(tries):
        U = _randmat(rng, rows, rank, lo, hi)
        V = _randmat(rng, rank, cols, lo, hi)
        M = U * V
        if M.rank() == rank:
            return M
    raise RuntimeError("could not build rank matrix")


def zero_product_point_chain(dsh, rank_chain, seed=0):
    """Build B=(B_1,...,B_N), B_i : e_i x e_{i-1}, with prescribed running-image
    dimension chain rank_chain = (s_1,...,s_N) where s_i = rank(B_i...B_1).
    Requires s_i <= min(e_i, s_{i-1}) with s_0 = e_0, and s_N = 0 (zero product).
    Returns the list of exact-rational B_i, or None if infeasible.

    Construction: keep an exact basis matrix Img (e_{i-1} x s_{i-1}) spanning the
    running image (Img_0 = I_{e_0}). For step i:
      pick a generic full-rank map of the image to an s_i-subspace of k^{e_i},
      and extend B_i generically on a complement of the image (so B_i is a generic
      e_i x e_{i-1} matrix conditioned to map Img onto a chosen s_i-space).
    The cleanest exact realization: choose B_i = C_i where on Img it has rank s_i
    and overall B_i is generic. We build B_i = Y_i * Z_i with the running image
    threaded through.
    """
    N = len(dsh) - 1
    e = dsh
    rng = random.Random(1000 + seed)
    s = [e[0]] + list(rank_chain)  # s[0..N]; s[0]=e_0, s[i]=rank(B_i..B_1)
    if len(s) != N + 1:
        return None
    if s[-1] != 0:
        return None
    for i in range(1, N + 1):
        if not (0 <= s[i] <= min(e[i], s[i - 1])):
            return None
    # Img : current running image as columns in k^{e_{i-1}}; start Img = I_{e_0}
    Img = sp.eye(e[0])  # e_0 x s_0
    Bs = []
    for i in range(1, N + 1):
        rows, cols = e[i], e[i - 1]
        si, sm1 = s[i], s[i - 1]
        # We want B_i (rows x cols) such that rank(B_i restricted to col(Img)) = s_i
        # and B_i is otherwise generic (full rank on a complement, image generic).
        # Build B_i so that B_i*Img has rank exactly s_i.
        # Construct: pick a generic rows x cols matrix Graw, then PROJECT its action
        # on Img to rank s_i by composing the image part through a rank-s_i gate.
        #
        # Decompose cols-space = col(Img) + complement. B_i acts:
        #   on col(Img): a generic map to a generic s_i-subspace of k^{e_i} (rank s_i)
        #   on complement: generic (full) -- but to keep image dims controlled we let it be generic.
        # For the running image we only track B_i*Img.
        #
        # Realize: choose an s_i x s_{i-1} generic rank-s_i matrix G acting in Img-coords,
        # and a generic e_i x s_i full-col-rank embedding W. Then on Img, B_i*Img = W*G*(Img-coords).
        # Off Img, add a generic map on a complement basis.
        # Assemble B_i in the standard basis.
        # complement basis of col(Img) in k^{cols}:
        if Img.cols > 0:
            # extend Img columns to a full basis of k^{cols}
            basis_cols = list(Img.T.rowspace())  # rows = current basis vectors (as 1xcols)
        # Simpler: build B_i as a generic matrix, then *force* B_i*Img to have rank s_i
        # by replacing B_i*Img with W*G and back-solving. Use: choose a generic full
        # B_i, compute current image J = B_i * Img (e_i x s_{i-1}), then we want a rank
        # exactly s_i image. Replace via a rank-reducing right-correction on Img-coords:
        #   B_i' = B_i + W * (E) * Img^+  ... messy. Instead, build directly:
        #
        # Direct exact build:
        #   Let P be a basis matrix (cols x cols) = [Img | Comp] (invertible).
        #   Define action in P-coords: first s_{i-1} coords are Img-coords.
        #   B_i * P = [ W*G | Gen ]  where W*G is e_i x s_{i-1} of rank s_i,
        #   Gen is e_i x (cols - s_{i-1}) generic.
        #   Then B_i = [W*G | Gen] * P^{-1}.
        # Build P:
        Comp = _complement_basis(rng, Img, cols)
        P = Img.row_join(Comp) if Comp.cols > 0 else Img
        if P.shape[1] != cols or P.rank() != cols:
            # rebuild P robustly
            P = _make_basis_extension(rng, Img, cols)
        # W*G block: e_i x s_{i-1} of rank s_i
        if si == 0:
            WG = sp.zeros(rows, sm1)
        else:
            W = _full_rank_mat(rng, rows, si, rank=si)       # e_i x s_i, rank s_i
            G = _full_rank_mat(rng, si, sm1, rank=si)         # s_i x s_{i-1}, rank s_i
            WG = W * G
        Gen = _randmat(rng, rows, cols - sm1) if cols - sm1 > 0 else sp.zeros(rows, 0)
        rhs = WG.row_join(Gen) if Gen.cols > 0 else WG
        Bi = rhs * P.inv()
        Bs.append(Bi)
        # update running image = col(B_i * Img) ; basis = column space of Bi*Img
        newimg = Bi * Img
        Img = _colspace_basis(newimg)
        if Img.cols != si:
            # numerical/degeneracy issue
            return None
    return Bs


def _complement_basis(rng, Img, n):
    """Return a basis (as columns) of a complement of col(Img) in k^n."""
    s = Img.cols
    if s >= n:
        return sp.zeros(n, 0)
    # greedily add random vectors independent of current span
    cur = Img
    cols = []
    while cur.cols < n:
        v = _randmat(rng, n, 1)
        test = cur.row_join(v)
        if test.rank() == cur.cols + 1:
            cur = test
            cols.append(v)
    if not cols:
        return sp.zeros(n, 0)
    M = cols[0]
    for c in cols[1:]:
        M = M.row_join(c)
    return M


def _make_basis_extension(rng, Img, n):
    Comp = _complement_basis(rng, Img, n)
    return Img.row_join(Comp) if Comp.cols > 0 else Img


def _colspace_basis(M):
    """exact basis (as columns) of the column space of M."""
    cs = M.columnspace()
    if not cs:
        return sp.zeros(M.rows, 0)
    B = cs[0]
    for c in cs[1:]:
        B = B.row_join(c)
    return B


if __name__ == "__main__":
    # sanity: (2,2,2,2,2) r=0 -> dsh = (2,2,2,2,2). A top component: one full
    # rank-1 cut. running-image chain that drops by 1 somewhere and ends 0?
    # zero product needs s_N = 0. e=(2,2,2,2,2). A *top* (minimal-codim) chain:
    # the running image stays 2 as long as possible then must reach 0 at the end.
    # The QIP minimum (C_sh=3, theta=6) chains are the |delta|=2 patterns.
    dsh = [2,2,2,2,2]
    from itertools import product
    # enumerate non-increasing chains s_1..s_5 with s_i<=min(e_i,s_{i-1}), s_5=0
    e = dsh; N = len(e)-1
    found = []
    for chain in product(range(0,3), repeat=N):
        s = [e[0]] + list(chain)
        ok = all(0 <= s[i] <= min(e[i], s[i-1]) for i in range(1,N+1)) and s[-1]==0
        if ok:
            found.append(tuple(chain))
    print("feasible image-dim chains (s_1..s_N), s_N=0:", len(found))
    for ch in found[:20]:
        pt = zero_product_point_chain(dsh, ch, seed=1)
        if pt is None:
            print("  chain", ch, "-> infeasible build")
            continue
        prod = pt[-1]
        for k in range(len(pt)-2, -1, -1):
            prod = prod * pt[k]
        print("  chain", ch, "-> product==0:", prod == sp.zeros(e[-1], e[0]),
              " ranks B_i:", [b.rank() for b in pt])

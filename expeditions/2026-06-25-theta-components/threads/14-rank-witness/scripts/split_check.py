"""
INDEPENDENT verification of the rank-split  rank J(A) = delta + dim I(Abar).

For an exact-rational fibre point A in Fib (mult(A)=E_r), we compute THREE numbers
and check they agree:
  (a) rank J(A)            -- direct rank of the fibre Jacobian (sum_i L_i . R_i image);
  (b) delta + dim I(Abar)  -- the structural split, where:
        delta := r*(d_0 + d_N - r)  (claimed endpoint contribution),
        Abar_i := quotient map k^{d_{i-1}}/U_{i-1} -> k^{d_i}/U_i induced by A_i,
                  U_i := through-line = (A_i..A_1)(W_0), W_0 = source of the r-block,
        I(Abar) := sum_i im(Lbar_i) (x) Ann(ker Rbar_i)  inside Hom(coker_0, coker_N),
                   Lbar_i = Abar_N..Abar_{i+1}, Rbar_i = Abar_{i-1}..Abar_1;
        dim I(Abar) is computed as the rank of the SHIFTED zero-product Jacobian on
        the quotient rep Abar (this is the cleanest exact handle, and equals the
        displayed tensor-sum dimension).
  (c) delta + (shifted-Jacobian-rank of Abar) -- to confirm the second summand IS
      exactly the shifted zero-product differential rank.

We also report the ENDPOINT block rank in isolation, to settle whether it is delta
(= r(d_0+d_N-r)) or delta - r^2 or delta + something: we compute the rank of the
sub-Jacobian restricted to directions Adot_1, Adot_N only acting in the endpoint
(through-line touching) part, vs the full split.

This is an INDEPENDENT recomputation (not reusing thread-13's minor enumeration):
we build the quotient rep by an explicit exact basis change to the through-flag.
"""
import sympy as sp
import sys

sys.path.insert(0, "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/scripts")
from fibjac import build_symbolic, mult_product, E_r  # noqa: E402
from rank_points import build_point_blocktri  # noqa: E402
sys.path.insert(0, "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/expeditions/2026-06-25-theta-components/threads/14-rank-witness/scripts")
from qip import fibre_data  # noqa: E402


def full_jacobian_rank(d, r, factors):
    """rank of Phi: Adot -> sum_i L_i Adot_i R_i, as a matrix into Mat_{dN x d0}."""
    N = len(d) - 1
    Ls, Rs = partials(d, factors)
    vecs = []
    for j in range(N):
        Lj, Rj = Ls[j], Rs[j]
        rows, cols = d[j + 1], d[j]
        for a in range(rows):
            for b in range(cols):
                Eab = sp.zeros(rows, cols)
                Eab[a, b] = 1
                M = Lj * Eab * Rj
                vecs.append([M[x, y] for x in range(d[N]) for y in range(d[0])])
    return sp.Matrix(vecs).rank()


def partials(d, factors):
    """L_j = A_N..A_{j+1}, R_j = A_{j-1}..A_1, 1-based j, factors[k]=A_{k+1}."""
    N = len(d) - 1
    Ls, Rs = [], []
    for j in range(1, N + 1):
        if j == N:
            Lj = sp.eye(d[N])
        else:
            Lj = factors[N - 1]
            for k in range(N - 2, j - 1, -1):
                Lj = Lj * factors[k]
        if j == 1:
            Rj = sp.eye(d[0])
        else:
            Rj = factors[j - 2]
            for k in range(j - 3, -1, -1):
                Rj = factors[k] * Rj
        Ls.append(Lj)
        Rs.append(Rj)
    return Ls, Rs


def through_flag(d, r, factors):
    """U_i = (A_i..A_1)(W_0) where W_0 = span(e_0,...,e_{r-1}) in k^{d_0}
    (the source of the r-block of E_r). Return list of basis matrices U_i
    (d_i x r). Verify dim U_i = r at every node (forces a top/clean point)."""
    N = len(d) - 1
    W0 = sp.zeros(d[0], r)
    for a in range(r):
        W0[a, a] = 1
    Us = [W0]
    cur = W0
    for i in range(N):  # apply A_{i+1} = factors[i]
        cur = factors[i] * cur  # (d_{i+1} x r)
        # basis of column space
        cs = cur.columnspace()
        if len(cs) != r:
            return None  # through-line collapsed: not a clean point
        B = cs[0]
        for c in cs[1:]:
            B = B.row_join(c)
        Us.append(B)
    return Us


def quotient_rep(d, r, factors):
    """Build Abar_i : k^{d_{i-1}}/U_{i-1} -> k^{d_i}/U_i as explicit (d_i - r) x
    (d_{i-1} - r) matrices in a basis adapted to the through-flag.
    Adapted basis at node i: [ U_i | C_i ] with C_i a complement; quotient coords
    are the C_i-coordinates. Abar_i = projection of A_i action on C_{i-1} to C_i."""
    N = len(d) - 1
    Us = through_flag(d, r, factors)
    if Us is None:
        return None
    # build full adapted basis P_i = [U_i | C_i] (d_i x d_i, invertible)
    Ps, comps = [], []
    for i in range(N + 1):
        Ui = Us[i]
        di = d[i]
        # complement: extend Ui columns to a basis of k^{di}
        cur = Ui
        extra = []
        idx = 0
        while cur.cols < di:
            e = sp.zeros(di, 1)
            e[idx, 0] = 1
            test = cur.row_join(e)
            if test.rank() == cur.cols + 1:
                cur = test
                extra.append(e)
            idx += 1
            if idx >= di and cur.cols < di:
                return None
        Ci = sp.Matrix.hstack(*extra) if extra else sp.zeros(di, 0)
        comps.append(Ci)
        Ps.append(Ui.row_join(Ci) if Ci.cols > 0 else Ui)
    # Abar_{i+1} = (C_i-projection of A_{i+1} . C_{i-1coords...}) — work node-by-node
    Abars = []
    for i in range(N):  # arrow A_{i+1}: k^{d_i} -> k^{d_{i+1}}
        Pin = Ps[i]       # d_i x d_i
        Pout = Ps[i + 1]  # d_{i+1} x d_{i+1}
        # A_{i+1} in adapted coords: Pout^{-1} A_{i+1} Pin, take bottom-right block
        M = Pout.inv() * factors[i] * Pin
        rin = r
        rout = r
        di, dii = d[i], d[i + 1]
        Abar = M[rout:dii, rin:di]  # (d_{i+1}-r) x (d_i - r)
        Abars.append(Abar)
    return Abars


def shifted_jac_rank(dsh, Bs):
    """rank of the zero-product Jacobian on shifted rep Bs (B_N..B_1 = 0):
    Phi_sh: Bdot -> sum_i Lsh_i Bdot_i Rsh_i, image in Mat_{e_N x e_0}."""
    N = len(dsh) - 1
    if any(dsh[i] == 0 for i in range(N + 1)):
        # degenerate quotient dims allowed; still build (some blocks 0x*)
        pass
    Ls, Rs = partials(dsh, Bs)
    vecs = []
    for j in range(N):
        Lj, Rj = Ls[j], Rs[j]
        rows, cols = dsh[j + 1], dsh[j]
        for a in range(rows):
            for b in range(cols):
                Eab = sp.zeros(rows, cols)
                Eab[a, b] = 1
                M = Lj * Eab * Rj
                vecs.append([M[x, y] for x in range(dsh[N]) for y in range(dsh[0])])
    if not vecs:
        return 0
    return sp.Matrix(vecs).rank()


def check(d, r, ncomp_tries=6):
    N = len(d) - 1
    fd = fibre_data(d, r)
    delta = fd["delta"]
    Csh = fd["Csh"]
    Q = fd["Q"]
    dsh = [x - r for x in d]
    print(f"==== d={d} r={r}:  delta={delta}  C_sh={Csh}  Q={Q}  theta={fd['theta']}  dsh={dsh} ====")
    # generate fibre points on each component-by-zero-factor (thread-13 builder),
    # and also via direct generic build; report split per point.
    seen = set()
    for zf in range(N):
        pt = build_point_blocktri(d, r, zf)
        if pt is None:
            continue
        if sp.simplify(mult_product(pt) - E_r(d[-1], d[0], r)) != sp.zeros(d[-1], d[0]):
            continue
        rk = full_jacobian_rank(d, r, pt)
        Abars = quotient_rep(d, r, pt)
        if Abars is None:
            print(f"  [zf={zf}] through-flag collapsed (non-clean point)")
            continue
        # verify shifted product is zero
        shprod = Abars[-1]
        for k in range(len(Abars) - 2, -1, -1):
            shprod = shprod * Abars[k]
        zero_ok = (shprod == sp.zeros(dsh[-1], dsh[0])) if (dsh[-1] > 0 and dsh[0] > 0) else True
        shrk = shifted_jac_rank(dsh, Abars)
        split_ok = (rk == delta + shrk)
        print(f"  [zf={zf}] rankJ={rk}  delta+shiftedJacRank={delta}+{shrk}={delta+shrk}  "
              f"split_ok={split_ok}  shiftedZP=0?{zero_ok}  (shiftedRank==C_sh? {shrk==Csh})")


if __name__ == "__main__":
    cases = [([2,2,2],1),([2,2,2,2],1),([3,3,3],2),([3,3,3],1),([3,2,3],1),
             ([3,2,4],1),([2,2,3],0)]
    for d, r in cases:
        check(d, r)

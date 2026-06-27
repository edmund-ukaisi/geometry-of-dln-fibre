"""
Evaluate the fibre Jacobian rank at exact-rational generic fibre points.

We need genuine fibre points (mult(A) = E_r exactly). We get them from the
block-triangular chart of thread-04:
    A_i = [[I_r, H_i], [0, B_i]]   (in a basis where the through-line is the
    top-left r block), with the shifted factors B_i : (d_i - r) x (d_{i-1} - r)
    satisfying the ZERO-PRODUCT  B_N..B_1 = 0, and H_i solving an affine linear
    system so that the off-diagonal blocks of mult vanish and the top-left block
    is exactly I_r.

Rather than solve H analytically in general, we BUILD a fibre point directly:
  - choose B_i on a chosen top component of the zero-product locus of the
    shifted dimension vector (d_0-r,...,d_N-r);
  - solve the LINEAR system (mult(A) - E_r = 0) for the H-entries (it is affine
    -linear in the H's once the B's are fixed), pick a particular + random
    homogeneous solution -> a generic fibre point on that component.

Then compute exact rank of the numeric Jacobian, and record which size-(codim)
minors are nonzero.
"""
import sympy as sp
from itertools import combinations
import random
from fibjac import mult_product, E_r

random.seed(12345)

def randQ(lo=-4, hi=4, denoms=(1,2,3)):
    while True:
        n = random.randint(lo, hi)
        dd = random.choice(denoms)
        if dd != 0:
            return sp.Rational(n, dd)

def build_point_blocktri(d, r, zero_factor_index, extra_seed=0):
    """Construct an exact-rational fibre point on the component where shifted
    factor B_{zero_factor_index} is forced (we set that B-block to 0 to kill the
    shifted product). Returns list of numeric factor matrices A_i (d[i+1]xd[i]).
    """
    N = len(d) - 1
    rng = random.Random(987 + extra_seed)
    def rq():
        return sp.Rational(rng.randint(-4,4), rng.choice([1,2,3]))
    # symbolic H, B blocks
    factors_sym = []
    Hsyms = []
    for i in range(N):
        rows, cols = d[i+1], d[i]
        blk = sp.zeros(rows, cols)
        # top-left r x r = I_r
        for a in range(min(r, rows)):
            for b in range(min(r, cols)):
                blk[a, b] = 1 if a == b else 0
        # top-right block H_i : r x (cols - r)  -> unknowns
        for a in range(r):
            for b in range(r, cols):
                s = sp.Symbol(f"H{i}_{a}_{b}")
                blk[a, b] = s
                Hsyms.append(s)
        # bottom-left block : (rows-r) x r  -> set 0 (gauge: through-line clean)
        # bottom-right B_i : (rows-r) x (cols-r)
        for a in range(r, rows):
            for b in range(r, cols):
                if i == zero_factor_index:
                    blk[a, b] = 0
                else:
                    blk[a, b] = rq()
        factors_sym.append(blk)
    P = mult_product(factors_sym)
    E = E_r(d[N], d[0], r)
    F = P - E
    eqs = [sp.expand(F[a,b]) for a in range(d[N]) for b in range(d[0])]
    sol = sp.solve(eqs, Hsyms, dict=True)
    if not sol:
        return None
    s0 = sol[0]
    # substitute, free H-vars get random rational values
    subsmap = {}
    for h in Hsyms:
        if h in s0:
            val = s0[h]
        else:
            val = None
    # Re-evaluate: solve may leave some H free. Build assignment.
    assign = {}
    for h in Hsyms:
        assign[h] = sp.Rational(rng.randint(-3,3), rng.choice([1,2]))
    # now plug random assignment into solution for dependent vars
    final = {}
    for h in Hsyms:
        if h in s0:
            final[h] = sp.simplify(s0[h].subs(assign))
        else:
            final[h] = assign[h]
    factors_num = [blk.subs(final) for blk in factors_sym]
    return factors_num

def jac_at_point(d, r, factors_num):
    from fibjac import build_symbolic
    factors_sym, syms = build_symbolic(d)
    # map symbolic entries to numeric values
    subs = {}
    for i in range(len(factors_sym)):
        rows, cols = factors_sym[i].shape
        for a in range(rows):
            for b in range(cols):
                subs[factors_sym[i][a,b]] = factors_num[i][a,b]
    P = mult_product(factors_sym)
    E = E_r(d[len(d)-1], d[0], r)
    F = P - E
    Fentries = [F[a,b] for a in range(d[-1]) for b in range(d[0])]
    J = sp.Matrix([[sp.diff(f, s) for s in syms] for f in Fentries])
    Jnum = J.subs(subs)
    return Jnum, syms

def report(d, r):
    N = len(d) - 1
    print(f"==== d={d} r={r} : dimRep={sum(d[i+1]*d[i] for i in range(N))}, cut eqs={d[-1]*d[0]} ====")
    # check the fibre point really lands on E_r
    for zf in range(N):
        pt = build_point_blocktri(d, r, zf)
        if pt is None:
            print(f"  zero-factor {zf}: no fibre point (chart empty)")
            continue
        P = mult_product(pt)
        E = E_r(d[-1], d[0], r)
        if sp.simplify(P - E) != sp.zeros(d[-1], d[0]):
            print(f"  zero-factor {zf}: POINT NOT ON FIBRE!", P)
            continue
        Jnum, syms = jac_at_point(d, r, pt)
        rk = Jnum.rank()
        print(f"  component (B_{zf}=0): Jacobian rank = {rk}  (shape {Jnum.shape})")
    print()

if __name__ == "__main__":
    report([2,2,2], 1)
    report([2,2,2,2], 1)
    report([3,3,3], 2)

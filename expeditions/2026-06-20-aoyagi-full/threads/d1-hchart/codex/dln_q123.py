"""Run Q1/Q2/Q3 tests on the (3,3,3), r=1 witness and several others."""
import sympy as sp
from sympy import Matrix, Rational, zeros
from itertools import combinations
from dln_chart import dg_matrix, has_coord_complement, find_coord_complement, q3_invertible_minor


def col_label(p, H0, H1, H2):
    if p < H0 * H1:
        a, b = divmod(p, H1)
        return f"d1[{a},{b}]"
    p2 = p - H0 * H1
    a, b = divmod(p2, H2)
    return f"d2[{a},{b}]"


def analyse(name, A1v, A2v):
    H0, H1 = A1v.shape
    _, H2 = A2v.shape
    B = A1v * A2v
    r = B.rank()
    nReg = r * (H0 + H2 - r)
    M, ridx, dims = dg_matrix(A1v, A2v)
    N = H0 * H1 + H1 * H2
    rk = M.rank()
    print("=" * 70)
    print(f"{name}: H=({H0},{H1},{H2}) rkA1={A1v.rank()} rkA2={A2v.rank()} "
          f"rkB={r} nReg={nReg} nReg_v=rank Dg(v)={rk} N={N}")

    # ---- Q1/Q2: pick an nReg-subset S of gradient ROWS that is independent,
    #      then test coordinate-complement existence.
    H0H2 = H0 * H2
    # Enumerate all nReg-subsets of the H0H2 output rows; for each independent one,
    # test whether it has a coordinate complement (equiv: full row rank, which it does
    # by independence). The SUBTLE point: independence of the nReg gradient functionals
    # is necessary; coordinate complement always exists for an independent row family.
    # We test the FULL square DPhi invertibility directly to be safe.
    found_independent = []
    for S in combinations(range(H0H2), nReg):
        G = M[list(S), :]
        if G.rank() == nReg:
            found_independent.append(S)
    print(f"  # of nReg-subsets S of output rows with INDEPENDENT gradients: "
          f"{len(found_independent)} (out of C({H0H2},{nReg})={sp.binomial(H0H2,nReg)})")

    if not found_independent:
        print("  !!! NO independent nReg-subset of gradients exists -> route (a) already fails.")
        return

    # For the FIRST such S, build the full DPhi = [ G ; P ] with P = coordinate complement,
    # and check it is invertible. By the lemma this works iff G has full row rank => always.
    S = list(found_independent[0])
    cols, P = find_coord_complement(M, S, N)
    print(f"  Witness S (rows {S}) -> coordinate complement P columns "
          f"{[col_label(p,H0,H1,H2) for p in P]}")
    # Build DPhi: rows = G then coordinate rows e_p for p in P
    DPhi = M[S, :]
    for p in P:
        e = zeros(1, N)
        e[0, p] = 1
        DPhi = DPhi.col_join(e)
    assert DPhi.shape == (N, N), DPhi.shape
    det = DPhi.det()
    print(f"  det DPhi(v) = {det}  -> {'INVERTIBLE' if det != 0 else 'SINGULAR'}")

    # ---- Now the ADVERSARIAL Q1 test: is coordinate-complement existence AUTOMATIC
    # for EVERY independent S, or only for SOME?  (a)=>(b) uniform means: every
    # independent nReg gradient family admits a coordinate complement.
    bad = 0
    for S in found_independent:
        if not has_coord_complement(M, list(S)):
            bad += 1
    print(f"  Independent nReg-subsets WITHOUT a coordinate complement: {bad} / "
          f"{len(found_independent)}")

    # ---- Q3 reframing: does an nReg x nReg invertible submatrix of Dg(v) exist?
    rsel, csel, rank = q3_invertible_minor(M, nReg)
    if rsel is None:
        print(f"  Q3: NO nReg-minor (rank {rank} < nReg {nReg}) -- impossible since "
              f"nReg_v>=nReg")
    else:
        minor = M[rsel, csel]
        d = minor.det()
        print(f"  Q3: nReg-minor rows={rsel} cols={[col_label(c,H0,H1,H2) for c in csel]} "
              f"det={d} -> {'INVERTIBLE' if d!=0 else 'BUG'}")
    print()


if __name__ == "__main__":
    # The Q2 witness
    analyse("Q2 witness (middle stratum)", sp.diag(1, 1, 0), sp.diag(1, 0, 0))

    # Other strata at (3,3,3), r=1
    analyse("rkA1=1,rkA2=1 (both rank 1)", sp.diag(1, 0, 0), sp.diag(1, 0, 0))
    analyse("rkA1=3,rkA2=1", sp.eye(3), sp.diag(1, 0, 0))
    analyse("rkA1=1,rkA2=3 (impossible? product rank<=1)",
            sp.diag(1, 0, 0), sp.eye(3))
    # generic-ish full rank product r=3
    analyse("r=3 full", sp.eye(3), sp.eye(3))
    # r=2
    analyse("r=2", sp.diag(1, 1, 0), sp.diag(1, 1, 0))

    # smaller: (2,2,2) r=1
    analyse("(2,2,2) r=1", Matrix([[1, 0], [0, 1]]), Matrix([[1, 0], [0, 0]]))
    analyse("(2,2,2) r=1 both rk1", Matrix([[1, 0], [0, 0]]), Matrix([[1, 0], [0, 0]]))

    # non-diagonal / generic factorisation, r=1, (3,3,3): A1v rank2, A2v rank1, random-ish
    A1 = Matrix([[1, 2, 0], [0, 1, 0], [3, 0, 0]])  # rank 2 (cols: c1=(1,0,3),c2=(2,1,0),c3=0)
    A2 = Matrix([[1, 0, 0], [1, 0, 0], [0, 0, 0]])   # rank 1
    analyse("(3,3,3) r=? generic A1 rk2, A2 rk1", A1, A2)

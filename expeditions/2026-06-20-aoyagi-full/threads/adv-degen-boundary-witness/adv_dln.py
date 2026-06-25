"""
Decorrelated adversarial probe of the #70 degenerate-boundary lemma.

Independent setup (NOT reusing pp2's scripts):
  - Build a DLN chain C_1 (H0 x H1), C_2 (H1 x H2), ..., C_L (H_{L-1} x H_L).
    NOTE on index convention: product P = C_1 C_2 ... C_L is (H0 x H_L).
    Layer "width" between matrices: the inner dims H_1,...,H_{L-1}. The outer dims H_0, H_L.
    A "bottleneck" at interior position i means H_i = r  (i in 1..L-1), giving M_i = H_i - r = 0.
    (We index widths H_0..H_L; reduced multiplicities M_i = H_i - r for ALL i incl ends.)
  - mult map  F(C_1,...,C_L) = (C_1 ... C_L) - B,  loss = ||F||^2.
  - At a deepest point (P = B exactly, rank B = r), the full Hessian of ||F||^2 equals 2 J^T J,
    J = Jacobian of (vec of product) wrt all entries.  So Hessian-rank = rank(J).
  - We compute rank(J) EXACTLY over QQ via sympy.

  nReg(H,r) = r*(H_0 + H_L - r).  Claim under test: rank(J) = nReg at every degenerate-boundary deepest.

We probe:
  (A) the deepest as a *specific aligned* rank-r factorization of a chosen rank-r B,
  (B) partial degeneracy (interior widths > r, only one = r),
  (C) asymmetric/non-monotone profiles,
  (D) several interior bottlenecks,
  (E) different B (not e0 e0^T) / different factorization base point  -> orbit-invariance test.
"""
import sympy as sp
from sympy import Rational as Q

def nReg(H, r):
    return r * (H[0] + H[-1] - r)

def build_chain_symbols(H, base):
    """Symbolic chain C_1..C_L with each entry = base_value + perturbation var.
    base: list of sympy Matrices giving the deepest-point base values (exact rationals).
    Returns (mats, vars) where mats are symbolic and vars is the flat list of perturbations."""
    L = len(H) - 1
    mats = []
    allvars = []
    for k in range(L):
        rows, cols = H[k], H[k+1]
        Mk = sp.zeros(rows, cols)
        for i in range(rows):
            for j in range(cols):
                x = sp.Symbol(f'c{k}_{i}_{j}', real=True)
                allvars.append(x)
                Mk[i, j] = base[k][i, j] + x
        mats.append(Mk)
    return mats, allvars

def product(mats):
    P = mats[0]
    for M in mats[1:]:
        P = P * M
    return P

def jacobian_rank_at_deepest(H, base):
    """Compute rank of J = d(vec P) / d(vars) at the deepest point (all perturbations 0), exactly over QQ."""
    mats, allvars = build_chain_symbols(H, base)
    P = product(mats)
    Pflat = sp.Matrix([sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)])
    Jac = Pflat.jacobian(allvars)
    Jac0 = Jac.subs({v: 0 for v in allvars})
    return Jac0.rank(), len(allvars), Jac0, mats

def full_hessian_rank(H, B, base):
    """Sanity: directly build loss ||P - B||^2 and compute Hessian rank at deepest (exact)."""
    mats, allvars = build_chain_symbols(H, base)
    P = product(mats)
    F = sp.expand(sum((P[i, j] - B[i, j])**2 for i in range(P.rows) for j in range(P.cols)))
    Hm = sp.hessian(F, allvars).subs({v: 0 for v in allvars})
    return Hm.rank(), F, allvars

def report(label, H, r, base, B=None, check_full=False):
    rk, nv, Jac0, mats = jacobian_rank_at_deepest(H, base)
    nr = nReg(H, r)
    P0 = product(mats).subs({s: 0 for row in mats for s in row.free_symbols})
    # product rank at base
    prk = sp.Matrix(P0).rank()
    line = (f"{label}\n   H={H} r={r} nReg={nr} | ambient={nv} | "
            f"rank(J)={rk} | product-rank at base={prk} | match nReg: {rk==nr}")
    print(line)
    if B is not None:
        # confirm base is actually a deepest point (P0 == B)
        ok = (sp.Matrix(P0) - B) == sp.zeros(B.rows, B.cols)
        print(f"   deepest check: P(base) == B ? {ok}")
    if check_full and B is not None:
        hrk, F, _ = full_hessian_rank(H, B, base)
        print(f"   full-Hessian rank (=2 J^T J at F=0) = {hrk}  [should equal rank(J)={rk}: {hrk==rk}]")
    print(f"   flat = ambient - rank(J) = {nv - rk}")
    return rk, nr

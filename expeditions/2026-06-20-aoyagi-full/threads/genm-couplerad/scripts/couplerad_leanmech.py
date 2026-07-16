"""
couplerad_leanmech.py -- does the SVD-FREE (raw-coordinate) resolution reach the floor, and does it
fit the BANKED square SchurCore or need the general non-square bilinear corank step?

The Lean-friendly atlas replaces the SVD atoms by a raw pivot/Schur resolution of the reduced deep
factor + a fibre-peel of the front weights.  The load-bearing question for the formaliser:

  Q(A): at the DEEPEST cell (k=rho, full collapse) the coupled object is  frobSq(Front . Q_eff) . charge
        with Front  u x M2  and  Q_eff  M2 x n  (reduced), codim = minAdm(u,M2,n) = floor.  Is this
        reachable by the banked (r,r,p) SchurCore (square first factor) or does it need the general
        non-square corank recursion?

  Q(B): the atom-sum  sum_i min(beta_i,u)  (the coupled lost-block codim per cell k) -- does it equal
        minAdm of a short reduced chain (so the deep pivot recursion = minAdm recursion), and is the
        binding intermediate cut SQUARE-reachable?

We answer both by exact N arithmetic (minAdm) + the closed atom-sum, over the witnesses + a scan.
"""
from fractions import Fraction as Fr
from functools import lru_cache
import itertools

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 2:
        return M[0] * M[1]
    m0, m1 = M[0], M[1]; rest = M[2:]
    return min((m0 - t) * (m1 - t) + minAdm((t,) + rest) for t in range(0, min(m0, m1) + 1))

def minAdm_argmin(M):
    m0, m1 = M[0], M[1]; rest = M[2:]
    best = None; ts = []
    for t in range(0, min(m0, m1) + 1):
        v = (m0 - t) * (m1 - t) + minAdm((t,) + rest)
        if best is None or v < best:
            best = v; ts = [t]
        elif v == best:
            ts.append(t)
    return best, ts

def binding_cut(M):
    m0, m1 = M[0], M[1]; rest = M[2:]
    best = None; targ = None
    for t in range(0, min(m0, m1) + 1):
        val = (m0 - t) * (m1 - t) + minAdm((t,) + rest)
        if best is None or val < best:
            best = val; targ = t
    return targ, min(m0 - targ, m1 - targ)

def beta(p, k):
    return [(p - k + 1) + 2 * (k - i) for i in range(1, k + 1)]

def atom_sum(u, k, p):
    return sum(min(bi, u) for bi in beta(p, k))

def Ck(u, rho, k, p):
    return u * (rho - k) + atom_sum(u, k, p)

print("="*100)
print("Q(A)+Q(B): SVD-free raw bilinear reachability of the coupled per-cell floor")
print("="*100)

def report(M):
    tstar, r = binding_cut(M)
    rho = min(M[2:]); n = M[-1]; M2 = M[2]; exc = abs(M2 - n)
    print(f"\nM={M}: minAdm={minAdm(M)} t*={tstar} r={r} rho={rho} M2={M2} n={n} exc={exc}")
    for j in range(1, r + 1):
        u = tstar + j; a = M[0] - u; b = M[1] - u
        if a < 1 or b < 1 or a + b > rho - 1:
            continue
        floor = minAdm((u,) + tuple(M[2:]))
        # DEEPEST cell k=rho: coupled bilinear Front(u x M2) . Q_eff(M2 x n), codim=floor.
        # Model as the sub-chain (u, M2, n) [3-chain]; the deep pivot recursion IS its minAdm recursion.
        sub = (u, M2, n)
        subval, subts = minAdm_argmin(sub)
        # is the minAdm-binding intermediate cut t reachable by a SQUARE SchurCore step?
        # SchurCore(r,r,p): first factor square r x r.  The recursion cut t makes the residual bilinear
        # (u-t)x(M2-t) . (M2-t)x? ... the SQUARE-reachable condition is that at the binding t the
        # residual left factor is square, i.e. the front row-count matches: this is exactly u=M2 OR the
        # transpose n=M2.  Flag when NEITHER holds (genuine non-square corank step).
        square_ok = (u == M2) or (n == M2) or all(t == 0 or t == min(u, M2) for t in subts)
        # atom-sum per cell k -> does it = minAdm of the reduced (u, p, k) bilinear? (p=k+exc)
        atomcheck = []
        for k in range(1, rho + 1):
            p = k + exc
            asum = atom_sum(u, k, p)
            # candidate: minAdm(u, p, k) (the reduced lost-block bilinear chain)
            cand = minAdm((u, p, k))
            atomcheck.append((k, p, asum, cand, asum == cand))
        allmatch = all(m for *_, m in atomcheck)
        print(f"  u={u} a={a} b={b} floor=minAdm{ (u,)+tuple(M[2:]) }={floor}")
        print(f"    deepest-cell sub-chain (u,M2,n)={sub}: minAdm={subval} (=floor? {subval==floor}) "
              f"binding t={subts}  square-SchurCore-reachable={square_ok}")
        print(f"    atom-sum == minAdm(u,p,k) for all k?  {allmatch}   " +
              " ".join(f"k{k}:{asum}{'=' if m else '!='}{cand}" for k,p,asum,cand,m in atomcheck))

for M in [(4,4,4,4),(3,4,5,4),(5,5,5,5),(3,3,4,4),(4,5,6,5),(5,5,4,3),(6,4,5,5),(4,4,4,4,4),(5,5,5,5,5)]:
    report(M)

# scan: over all in-scope cuts, does deepest-cell sub-chain minAdm = floor (always)?
print("\n" + "="*100)
print("SCAN (arity 4, widths 2..7): deepest-cell 3-chain (u,M2,n) minAdm == floor minAdm((u,)+deep)?")
print("="*100)
mism = 0; nonsq = 0; ncut = 0
for M in itertools.product(range(2, 8), repeat=4):
    tstar, r = binding_cut(M)
    rho = min(M[2:]); n = M[-1]; M2 = M[2]
    for j in range(1, r + 1):
        u = tstar + j; a = M[0] - u; b = M[1] - u
        if a < 1 or b < 1 or a + b > rho - 1:
            continue
        ncut += 1
        floor = minAdm((u,) + tuple(M[2:]))
        subval, subts = minAdm_argmin((u, M2, n))
        if subval != floor:
            mism += 1
        if not ((u == M2) or (n == M2) or all(t in (0, min(u, M2)) for t in subts)):
            nonsq += 1
print(f"  cuts={ncut}  deepest-3chain!=floor: {mism}   non-square-binding cuts: {nonsq}")
print("  (deep chains have arity>3; the 3-chain (u,M2,n) is the SINGLE-deep-matrix collapse model;")
print("   for arity>4 deep the deepest cell is a longer sub-chain resolved layer-by-layer by CR-path.)")

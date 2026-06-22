#!/usr/bin/env python3
"""
verify_s3.py — exact-rational verification of the S1-S4 chain → Thm 5.5,
with focus on S3 (the power-series inversion).

We work with q-series truncated to a degree cap DEG, as exact polynomials in q
over QQ (sympy). The base field for the "x-inversion" question is the ring of
q-series; we model the x-power-series equations as finite linear recursions and
check whether S3 is a FINITE TRIANGULAR INVERSION (no infinite q-binomial library
needed) by comparing two computations of Q^0_d:
  (A) the DEFINITION  Q^0_d = sum over Kostant partitions m of d with m_{0N}=0 of
      q^{codim} * Pm(m)     [matches the Lean `Qseries d 0`]
  (B) the Thm 5.5 RHS  P_0 * sum_{s=0}^{min d} (-1)^s q^{C(s,2)} P_s * Pmult(d-s)
and the intermediate b_{d0} recursion from eqn:key.

It also directly checks the FINITE inversion mechanism for S3:
  given  sum_{s} b_s x^s * sum_{s} P_s x^s = sum_s a_s x^s   (over the q-series ring),
  the coefficient identity at x^n is   a_n = sum_{k=0}^n b_{n-k} P_k,
  which is LOWER-TRIANGULAR with unit diagonal (P_0 = 1), so b_n is determined by
  b_n = a_n - sum_{k=1}^n b_{n-k} P_k,
  and the CLOSED inverse is  b_n = sum_{k=0}^n a_{n-k} * (-1)^k q^{C(k,2)} P_k
  iff  sum_{k} (-1)^k q^{C(k,2)} P_k * P_{m-k} = [m=0]   (the q-binomial / pentagon
  orthogonality, eqn:Ps_inverse multiplied out).  We verify THAT orthogonality
  exactly (the one classical q-fact S3 rests on), to all orders up to DEG.
"""
import sympy as sp
from itertools import product
from functools import lru_cache

q = sp.symbols('q')

DEG = 24  # q-degree truncation cap

def trunc(poly):
    return sp.Poly(poly, q).as_expr() if poly == 0 else sp.series(sp.expand(poly), q, 0, DEG+1).removeO()

# ---- P_s = prod_{k=1}^s 1/(1-q^k) as a q-series truncated to DEG ----
@lru_cache(maxsize=None)
def Pseries(s):
    expr = sp.Integer(1)
    for k in range(1, s+1):
        # 1/(1-q^k) = sum_{j>=0} q^{jk}, truncated
        geo = sum(q**(j*k) for j in range(0, DEG//max(k,1) + 1))
        expr = sp.expand(expr * geo)
        expr = sp.Poly(expr, q)
        expr = sp.Poly({m: c for m, c in expr.terms() if m[0] <= DEG}, q).as_expr()
    return sp.Poly(expr, q)

def P(s):
    return Pseries(s)

def Pmult(dvec):
    expr = sp.Poly(sp.Integer(1), q)
    for d in dvec:
        expr = (expr * P(d))
        expr = sp.Poly({m: c for m, c in expr.terms() if m[0] <= DEG}, q)
    return expr

def Cbin2(s):
    return s*(s-1)//2

# ---- (x;q)_inf inverse coefficients: alt_k = (-1)^k q^{C(k,2)} P_k ----
def altP(k):
    return sp.Poly(sp.expand(((-1)**k) * q**Cbin2(k)) * P(k).as_expr(), q)

# =====================================================================
# CHECK 1 — the orthogonality (the ONE classical q-fact S3 rests on):
#   sum_{k=0}^m (-1)^k q^{C(k,2)} P_k P_{m-k} = [m == 0]
# This is  ( (x;q)_inf ) * ( 1/(x;q)_inf ) = 1  read off at x^m.
# =====================================================================
def check_orthogonality(MMAX=12):
    ok = True
    for m in range(0, MMAX+1):
        acc = sp.Poly(sp.Integer(0), q)
        for k in range(0, m+1):
            term = altP(k) * P(m-k)
            term = sp.Poly({mm: c for mm, c in term.terms() if mm[0] <= DEG}, q)
            acc = acc + term
        acc = sp.Poly({mm: c for mm, c in acc.terms() if mm[0] <= DEG}, q)
        target = sp.Poly(sp.Integer(1) if m == 0 else sp.Integer(0), q)
        if acc.as_expr() - target.as_expr() != 0:
            ok = False
            print(f"  ORTHOGONALITY FAIL at m={m}: {sp.expand(acc.as_expr()-target.as_expr())}")
    print(f"CHECK 1 orthogonality (sum_k altP(k) P(m-k) = [m=0]) for m=0..{MMAX}: {'PASS' if ok else 'FAIL'}")
    return ok

# =====================================================================
# CHECK 2 — the Kostant-partition definition Q^0_d  (matches Lean Qseries d 0).
# Enumerate Kostant partitions of d with corner m_{0N}=r, compute
#   codim = codimForm  (Cor 3.5 form, equioriented) and Pm.
# We use the equioriented codimForm exactly as Lean encodes it.
# =====================================================================
def codimForm(N, m):
    # m: dict (i,j)->mult for 0<=i<=j<=N ; ints. codimForm over 1<=i<=u<=j<=v<=N
    # term m[(i-1,j-1)] * m[(u,v)]
    total = 0
    for i in range(1, N+1):
        for u in range(i, N+1):
            for j in range(u, N+1):
                for v in range(j, N+1):
                    total += m.get((i-1, j-1), 0) * m.get((u, v), 0)
    return total

def kostant_partitions(dvec, r):
    """Yield all m: dict (i,j)->mult, 0<=i<=j<=N, with sum_{i<=k<=j} m_{ij} = d_k for all k,
       and m_{0,N} = r."""
    N = len(dvec) - 1
    pairs = [(i, j) for i in range(N+1) for j in range(i, N+1)]
    # bound m_{ij} <= d_i
    ranges = [range(0, dvec[i]+1) for (i, j) in pairs]
    for vals in product(*ranges):
        m = {p: v for p, v in zip(pairs, vals)}
        if m[(0, N)] != r:
            continue
        ok = True
        for k in range(N+1):
            s = sum(m[(i, j)] for (i, j) in pairs if i <= k <= j)
            if s != dvec[k]:
                ok = False
                break
        if ok:
            yield m

def Qseries_def(dvec, r):
    N = len(dvec) - 1
    acc = sp.Poly(sp.Integer(0), q)
    for m in kostant_partitions(dvec, r):
        c = codimForm(N, m)
        # Pm = prod_{i<=j} P(m_{ij})
        pm = sp.Poly(sp.Integer(1), q)
        for (i, j), v in m.items():
            pm = pm * P(v)
            pm = sp.Poly({mm: cc for mm, cc in pm.terms() if mm[0] <= DEG}, q)
        term = sp.Poly(q**c, q) * pm
        term = sp.Poly({mm: cc for mm, cc in term.terms() if mm[0] <= DEG}, q)
        acc = acc + term
    acc = sp.Poly({mm: cc for mm, cc in acc.terms() if mm[0] <= DEG}, q)
    return acc

# =====================================================================
# CHECK 3 — Thm 5.5 RHS:
#   Q^r_d = P_r * sum_{s=0}^{min d - r} (-1)^s q^{C(s,2)} P_s * Pmult(d-r-s)
# where Pmult(d-r-s) = prod_i P(d_i - r - s)  (manifestly multiset-symmetric).
# =====================================================================
def thm55_rhs(dvec, r):
    mind = min(dvec)
    acc = sp.Poly(sp.Integer(0), q)
    for s in range(0, mind - r + 1):
        coeff = sp.Poly(sp.expand(((-1)**s) * q**Cbin2(s)), q) * P(s)
        coeff = sp.Poly({mm: cc for mm, cc in coeff.terms() if mm[0] <= DEG}, q)
        shifted = [d - r - s for d in dvec]
        if any(x < 0 for x in shifted):
            continue
        pm = Pmult(shifted)
        term = coeff * pm
        term = sp.Poly({mm: cc for mm, cc in term.terms() if mm[0] <= DEG}, q)
        acc = acc + term
    acc = (P(r) * acc)
    acc = sp.Poly({mm: cc for mm, cc in acc.terms() if mm[0] <= DEG}, q)
    return acc

def eq_upto(a, b, deg):
    da = sp.Poly({m: c for m, c in a.terms() if m[0] <= deg}, q)
    db = sp.Poly({m: c for m, c in b.terms() if m[0] <= deg}, q)
    return sp.expand(da.as_expr() - db.as_expr()) == 0

if __name__ == '__main__':
    print(f"DEG cap = {DEG}\n")
    c1 = check_orthogonality(12)
    print()

    # test dimension vectors: monotone, non-monotone, with zeros, permutations
    tests = [
        (2,2,2), (2,3,2), (2,2,3), (3,2,2), (2,4,2),
        (1,2,1), (1,2,3), (3,2,1), (2,1,2),
        (3,3,3),
        (1,1,1,1), (2,1,2,1), (1,2,2,3), (3,2,2,1),
    ]
    print("CHECK 2+3 — Qseries_def(d,r) == Thm5.5 RHS(d,r), for all valid r:")
    allok = True
    for dvec in tests:
        mind = min(dvec)
        for r in range(0, mind+1):
            # cap reliability: codim can be large; compare only to safe degree
            lhs = Qseries_def(list(dvec), r)
            rhs = thm55_rhs(list(dvec), r)
            # safe compare degree: min part contributes; use DEG - max single P shift
            ok = eq_upto(lhs, rhs, DEG - 6)
            allok = allok and ok
            tag = 'ok' if ok else 'MISMATCH'
            if not ok:
                print(f"  d={dvec} r={r}: {tag}")
                diff = sp.expand((sp.Poly({m:c for m,c in lhs.terms() if m[0]<=DEG-6},q)).as_expr()
                                 - (sp.Poly({m:c for m,c in rhs.terms() if m[0]<=DEG-6},q)).as_expr())
                print(f"      diff = {diff}")
    print(f"  => {'ALL PASS' if allok else 'SOME FAILED'}")
    print()

    # CHECK 4 — permutation invariance of the LOWEST-degree term (C, theta) read off
    print("CHECK 4 — (C, theta) from Qseries_def lowest term, permutation invariance:")
    def lowest(poly):
        terms = [(m[0], c) for m, c in poly.terms()]
        if not terms:
            return (None, None)
        cmin = min(t[0] for t in terms)
        theta = sum(c for (m, c) in terms if m == cmin)
        return (cmin, theta)
    import itertools as it
    for base in [(2,2,3), (1,2,3), (1,2,2,3)]:
        seen = set()
        vals = set()
        for perm in set(it.permutations(base)):
            qd = Qseries_def(list(perm), 0)
            vals.add(lowest(qd))
        print(f"  d~{base}: (C,theta) over all perms = {vals}  {'PASS (invariant)' if len(vals)==1 else 'FAIL'}")

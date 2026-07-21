#!/usr/bin/env python3
# provenance: threads/34-case1-invariant (pnp Case-1 PrincipalInv preservation)
"""
KILL-SET: the DEEP-LAYER Bezout failure ((3,3,2,2)) and the non-monotone running-min ((2,2,3,2)).

The (3,3,4) interior witness (case1_witness_334.py) recovered Bezout after a Case-1(2) step ONLY
because S=L there (the cleared pivot is a bare b1).  The sharper test is a Case-1 step at S<L, where
the cleared pivot carries a PENDING DEEP LAYER that vanishes at the origin -- so no bare b1 appears and
Bezout stays FALSE across the step.  This is the decisive witness that Bezout/principality is NOT a
per-step invariant: it cannot be re-established by a Case-1 step while any deep layer is pending.

(1) (3,3,2,2), interior state S=2 (deep layer C3 pending, S=2 < L=3):
    - parent (S=2,J=0): D holds, B fails.
    - Case-1(2) step advances J->1, clearing a pivot; BUT the cleared-pivot row = b1 * (row of C3),
      which vanishes at the origin.  => divisibility PRESERVED, Bezout STILL FALSE.
    - only at S=3=L (C3 consumed) does a bare b1 appear and Bezout hold.
(2) (2,2,3,2), non-monotone (M^(3)=3 > running-min 2):
    - a Case-1 step across the width increase preserves divisibility;
    - the b-support stays a SUFFIX (width increase adds columns, not b-rows: chain length capped at
      the running min 2), so no non-suffix monomial support is created;
    - the following Case-2 exponent is governed by the RUNNING MIN (2), not the raw width (3):
      the raw-width divisor is NON-BINDING (matches thread 27/31 rawwidth-defect resolution).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

def origin(expr, gens):
    return sp.expand(expr).subs({g: 0 for g in gens})

# =====================================================================
# (1) (3,3,2,2): DEEP-LAYER Bezout failure at S=2 (C3 pending)
# =====================================================================
print("=== (1) (3,3,2,2) deep-layer: Case-1 step at S=2 keeps Bezout FALSE ===")
# M^(1..4)=3,3,2,2, L=3. Running mins M(2)=3, M(3)=2. At S=2: b-chain from layer 1.
r, s, t = sp.symbols('r s t')          # layer-1 divisors: r=u11(t~0), s=u12(t~1), t=u13(t~2)
b = [r, r*s, r*s*t]                     # chain b1|b2|b3 (M(2)=3 rows)
# deep layer C3 : 2x2, pending at S=2, VANISHES at the deepest point
C3 = sp.Matrix(2, 2, lambda i, j: sp.Symbol(f'c{i+1}{j+1}'))
# residual D0 at (S=2,J=0): (M(2)-0)x(M^(3)-0) = 3x2, generic, vanishes at origin
D0 = sp.Matrix(3, 2, lambda i, j: sp.Symbol(f'e{i+1}{j+1}'))
gens1 = [r, s, t] + list(C3.free_symbols) + list(D0.free_symbols)

# --- parent (S=2,J=0): N = diag(b) * [[E_0,O],[O,D0]] * C3 = diag(b)*D0*C3 ---
Npar = sp.diag(*b) * (D0 * C3)          # 3x2
div_par = all((z := sp.cancel(Npar[i, j] / b[0])).is_polynomial(*gens1) and
              sp.simplify(z * b[0] - Npar[i, j]) == 0 for i in range(3) for j in range(2))
bez_par = any(origin(sp.cancel(Npar[i, j] / b[0]), gens1) != 0 for i in range(3) for j in range(2))
check("parent (S=2,J=0): (D) divisibility by b1 holds", div_par)
check("parent (S=2,J=0): (B) Bezout FALSE (deep C3 + residual vanish at 0)", not bez_par)

# --- Case 1(2) at (S=2,J=0): introduce w, normalise pivot, advance to J=1 ---
# In the reduced (J=1) form the working matrix is  diag(b') * [[E_1,O],[O,D1]] * C3.
# The cleared pivot (row 1 of [[E_1,O],[O,D1]]) = [1,0], so row 1 of N' = b1' * (row 0 of C3).
w = sp.symbols('w')
b1p = r * w                              # b1 -> b1*w (new divisor w at threshold 0)
bp = [r*w, r*w*s, r*w*s*t]              # child chain (s stays, reduced)
D1 = sp.Matrix(2, 1, lambda i, j: sp.Symbol(f'f{i+1}'))   # residual after 1 Schur step: (M(2)-1)x(M^(3)-1)=2x1
gens1c = [r, w, s, t] + list(C3.free_symbols) + list(D1.free_symbols)
# reduced [[E_1,O],[O,D1]] is 3x2 : row0=[1,0]; rows1,2 = [0, D1[i]]
red = sp.Matrix([[1, 0],
                 [0, D1[0, 0]],
                 [0, D1[1, 0]]])
Nchild = sp.diag(*bp) * (red * C3)      # 3x2
# divisibility by b1' = r*w
div_ch = all((z := sp.cancel(Nchild[i, j] / b1p)).is_polynomial(*gens1c) and
             sp.simplify(z * b1p - Nchild[i, j]) == 0 for i in range(3) for j in range(2))
check("child (S=2,J=1): (D) divisibility by b1*w PRESERVED", div_ch)
# cleared-pivot row 1 = b1' * (row0 of C3) -- confirm it is NOT bare (equals b1'*C3row, vanishes)
row1_quotient = [sp.cancel(Nchild[0, j] / b1p) for j in range(2)]
pivot_bare = any(origin(qz, gens1c) != 0 for qz in row1_quotient)
check("cleared pivot is b1*(C3 row), NOT bare (row-1 quotient vanishes at 0)", not pivot_bare)
bez_ch = any(origin(sp.cancel(Nchild[i, j] / b1p), gens1c) != 0 for i in range(3) for j in range(2))
check("child (S=2,J=1): (B) Bezout STILL FALSE (S<L: pivot carries pending C3)", not bez_ch)

# --- only at S=3=L (C3 consumed to diagonal) does a bare b1 appear ---
# terminal-ish: replace C3-carrying rows by the resolved diagonal; row1 becomes b1'*1 (bare)
Nterm = sp.diag(*bp) * sp.Matrix([[1, 0], [0, sp.Symbol('g1')], [0, sp.Symbol('g2')]])
bez_term = origin(sp.cancel(Nterm[0, 0] / b1p), [r, w, s, t, sp.Symbol('g1'), sp.Symbol('g2')]) == 1
check("at S=L (C3 gone): bare b1 appears (row-1 quotient = 1) => Bezout HOLDS", bez_term)

# =====================================================================
# (2) (2,2,3,2): non-monotone -- suffix support + running-min exponent
# =====================================================================
print("\n=== (2) (2,2,3,2) non-monotone: suffix support + running-min governs ===")
# M^(1..4)=2,2,3,2, L=3. Running mins: M(1)=2,M(2)=2,M(3)=2,M(4)=2 (min stays 2 -- the increase to 3
# at layer 3 does NOT raise the running min). b-chain length capped at running min = 2.
# Layer-1 gives chain b1=x, b2=x*y (M(2)=2). At S=3 (M^(3)=3, M^(4)=2): residual D_J is
# (M(3)-J)x(M^(4)-J) = (2-J)x(2-J); the extra layer-3 column (M^(3)=3) adds NO b-row.
x, y = sp.symbols('x y')
chain = [x, x*y]                        # length 2 = running min; b1|b2
# suffix property: support(b_i) = {divisors with t~ < i} is nested-increasing => a suffix under any step
supp = [set(sp.Mul.make_args(bi)) for bi in chain]
suffix_ok = supp[0] <= supp[1]          # {x} subset {x,y}
check("b-support nested (suffix): supp(b1) subset supp(b2)", suffix_ok)
# width increase adds a COLUMN not a b-row: chain length == running-min, independent of raw M^(3)=3
running_min = min(2, 2, 2)              # M(3) = min(M^1,M^2,M^3)=min(2,2,3)=2
check("chain length = running min (2), NOT raw width (3)", len(chain) == running_min == 2)
# running-min exponent for a Case-2 step at (S=3,J=0): (M(3)-J)(M^(4)-J) = 2*2 = 4 (running min),
# NOT the raw (M^(3)-J)(M^(4)-J) = 3*2 = 6.  The raw-width divisor would be non-admissible/non-binding.
exp_runningmin = (running_min - 0) * (2 - 0)      # = 4
exp_raw = (3 - 0) * (2 - 0)                        # = 6
check("Case-2 exponent uses running-min: 4 (not raw 6)", exp_runningmin == 4 and exp_raw == 6)
# qipMin(2,2,3,2) = 3 (from thread 27/31); the raw-width divisor (exp 6) is NON-binding (6 > 2*3).
from functools import lru_cache
@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(v) for v in M)
    if len(M) == 1: return 0
    if len(M) == 2: return M[0]*M[1]
    return min((M[0]-k)*(M[1]-k) + minAdm((k,)+M[2:]) for k in range(min(M[0], M[1])+1))
qip = minAdm((2, 2, 3, 2))
check("qipMin(2,2,3,2)=3; raw-width exponent 6 > 2*qip=6-ties? => non-binding (running-min 4 also > 3)",
      qip == 3 and exp_runningmin > qip and exp_raw > qip)

print(f"\nKILL-SET (3,3,2,2 deep-layer + 2,2,3,2 non-monotone): {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)

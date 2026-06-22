"""Thread 06 — Lean-proof-strategy verification for the N=1 Durfee identity.

  (D)  P_a P_b = sum_{r=0}^{min(a,b)} q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}

where P_n = prod_{k=1}^n (1-q^k)^{-1}  (inverse q-Pochhammer; P_0 = 1).

This script tests CANDIDATE INDUCTION ROUTES for a Lean proof against the M1 Core.QSeries
API (P, geomFactor, P_succ : P(s+1)=P s * geomFactor(s+1), geomFactor_mul_one_sub).
We do NOT need a new classical input beyond P_succ + geomFactor telescoping IF an induction
closes. We test, exactly (integer coefficients, truncated power series):

  ROUTE B1 — induction on min(a,b), peeling the TOP geomFactor of the larger argument.
  ROUTE B2 — the "absorb one box" recurrence (Durfee square grows by a hook).
  ROUTE C  — the finite-product clear-denominators polynomial identity.

All arithmetic is exact integer; truncation degree PREC.  Reuses qseries.P_s etc.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "03-qseries-route", "scratch"))
from qseries import P_s, pmul, padd, trunc, PREC, pscale_shift, one_over_1_minus_qk

# --- helpers ---------------------------------------------------------------
def psub(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)]

def one_minus_qk(k):
    """1 - q^k as a truncated series."""
    out = [0]*PREC
    out[0] = 1
    if k < PREC:
        out[k] -= 1
    return out

ONE = [1] + [0]*(PREC-1)

def geomFactor(k):
    """geomFactor k = 1/(1-q^k) (the M1 primitive). geomFactor 0 = 1."""
    if k == 0:
        return ONE[:]
    return list(one_over_1_minus_qk(k))

# --- the identity, both sides ---------------------------------------------
def durfee_lhs(a, b):
    return trunc(pmul(P_s(a), P_s(b)))

def durfee_rhs(a, b):
    acc = [0]*PREC
    for r in range(0, min(a, b)+1):
        term = pmul(pmul(P_s(a-r), P_s(r)), P_s(b-r))
        acc = padd(acc, pscale_shift(term, 1, (a-r)*(b-r)))
    return trunc(acc)

def check_identity(rng=9):
    fails = 0
    for a in range(rng):
        for b in range(rng):
            if durfee_lhs(a, b) != durfee_rhs(a, b):
                fails += 1
                print("  IDENTITY FAIL", a, b)
    print(f"(D) identity, a,b in 0..{rng-1}: ", "OK" if fails==0 else f"{fails} FAIL")
    return fails

# ===========================================================================
# ROUTE B1.  WLOG a <= b (identity is symmetric in a,b — RHS symmetric under swap+reindex).
#   Induct on a (= min). Base a=0: LHS = P_0 P_b = P_b; RHS single term r=0:
#       q^0 P_0 P_0 P_b = P_b.  OK.
#   Step a -> a+1 (with a+1 <= b). We want a recurrence relating RHS(a+1,b) to RHS(a,*).
#   Candidate: peel the top factor of P_{a+1} = P_a * geomFactor(a+1) on the LHS and find
#   a matching telescold on the RHS.  But the RHS terms mix P_{a+1-r} P_r P_{b-r}; not a clean
#   single peel.  TEST instead the STANDARD Durfee-square recurrence (Route B2).
# ===========================================================================

# ===========================================================================
# ROUTE B2.  The classical 'first column / Durfee box' recurrence for the RHS.
#   Define D(a,b) := RHS(a,b).  Claim a recurrence in which the r=0 term is split off and the
#   r>=1 part is q^{...} * D(a-1,b-1) shifted. Precisely, reindex r = s+1:
#     RHS(a,b) = P_a P_b? no, that's the claim. We test the SELF-recurrence of the RHS sum:
#       RHS(a,b) = P_a P_b   (the claim) — instead test that the RHS satisfies the SAME
#       recurrence as the LHS P_a P_b under a 'q-shift' so induction can close.
#   The clean known recurrence:  shifting r->r+1 multiplies the box exponent.
#   Test:  RHS(a,b) - [r=0 term]  ?=  (q-shifted) RHS(a-1,b-1) relation.
# ===========================================================================
def rhs_r0(a, b):
    """r=0 term of RHS(a,b): q^{ab} P_a P_0 P_b = q^{ab} P_a P_b."""
    return pscale_shift(pmul(P_s(a), P_s(b)), 1, a*b)

def rhs_tail_reindex(a, b):
    """sum_{r>=1} q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}, write r = t+1, t>=0:
       = sum_{t>=0} q^{(a-1-t)(b-1-t)} P_{a-1-t} P_{t+1} P_{b-1-t}, t=0..min(a,b)-1.
       Compare to RHS(a-1,b-1) = sum_{t} q^{(a-1-t)(b-1-t)} P_{a-1-t} P_t P_{b-1-t}.
       The only change is P_{t+1} vs P_t.  P_{t+1} = P_t * geomFactor(t+1).  NOT a global factor.
    """
    acc = [0]*PREC
    for r in range(1, min(a, b)+1):
        t = r-1
        term = pmul(pmul(P_s(a-r), P_s(r)), P_s(b-r))
        acc = padd(acc, pscale_shift(term, 1, (a-r)*(b-r)))
    return trunc(acc)

def check_B2_split(rng=9):
    """RHS(a,b) = rhs_r0 + rhs_tail. Trivially true by definition; report to anchor B2."""
    fails = 0
    for a in range(1, rng):
        for b in range(1, rng):
            lhs = durfee_rhs(a, b)
            rhs = trunc(padd(rhs_r0(a, b), rhs_tail_reindex(a, b)))
            if lhs != rhs:
                fails += 1
    print(f"(B2) RHS = [r=0] + [r>=1 tail] split, a,b in 1..{rng-1}: ", "OK" if fails==0 else f"{fails} FAIL")
    return fails

# ===========================================================================
# ROUTE C.  Clear denominators to a POLYNOMIAL identity.
#   Multiply (D) by  Den := prod_{k=1}^{max(a,b)} (1-q^k)^{?}.  The issue: the three P-products
#   on the RHS have DIFFERENT ranges per term.  A uniform denominator that clears EVERY term:
#   for term r, P_{a-r}P_r P_{b-r} has denominators (1-q^k) for k<=a-r, k<=r, k<=b-r.
#   The LHS P_a P_b has denominators k<=a (squared up to min) ... NOT uniform. Route C needs a
#   common denominator = prod over a multiset; messy. We test whether the SYMMETRIC-FUNCTION
#   /Cauchy-style finite identity below is the clean one instead.
#
#   The cleanest finite algebraic form (the one a Lean induction can use) turns out to be the
#   q-analog where we peel geomFactor(b) (largest index present) — test ROUTE D.
# ===========================================================================

# ===========================================================================
# ROUTE D.  Induct on b (the LARGER, WLOG a<=b), peeling geomFactor(b) via a known telescoping
#   of the WHOLE identity.  We test the hypothesised recurrence:
#       (1 - q^b) * [ P_a P_b ]  =  P_a P_{b-1}                         (LHS peel, exact)
#   and on the RHS, find the matching (1-q^b)-multiplied telescoping.  Test if
#       (1-q^b)*RHS(a,b)  ==  RHS(a,b-1) + (correction)
#   by brute compare, to discover the correction term shape.
# ===========================================================================
def check_LHS_peel(rng=9):
    fails = 0
    for a in range(rng):
        for b in range(1, rng):
            lhs = trunc(pmul(one_minus_qk(b), durfee_lhs(a, b)))
            rhs = durfee_lhs(a, b-1)   # P_a * P_{b-1}
            if lhs != rhs:
                fails += 1
                print("  LHS-peel FAIL", a, b)
    print(f"(D) LHS peel (1-q^b)P_a P_b = P_a P_{{b-1}}, a in 0..{rng-1},b 1..{rng-1}: ",
          "OK" if fails==0 else f"{fails} FAIL")
    return fails

def discover_D_correction(a, b):
    """(1-q^b) RHS(a,b)  vs  RHS(a,b-1). Return the difference series (the 'correction')."""
    lhs = trunc(pmul(one_minus_qk(b), durfee_rhs(a, b)))
    rhs = durfee_rhs(a, b-1)
    return psub(lhs, rhs)

if __name__ == "__main__":
    total = 0
    total += check_identity()
    total += check_B2_split()
    total += check_LHS_peel()
    print("\n=== ROUTE D: discover the correction (1-q^b)RHS(a,b) - RHS(a,b-1), a<=b ===")
    for (a, b) in [(1,2),(2,3),(2,2),(1,3),(3,4),(2,4),(3,3)]:
        d = discover_D_correction(a, b)
        nz = [(i, c) for i, c in enumerate(d) if c != 0]
        print(f"  a={a} b={b}: correction nonzero terms (deg,coeff)[:6] = {nz[:6]}")
    print()
    print("CLEAN" if total == 0 else f"{total} FAILS")

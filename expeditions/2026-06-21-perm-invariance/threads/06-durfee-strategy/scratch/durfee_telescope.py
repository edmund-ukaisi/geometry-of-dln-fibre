"""Thread 06 — pin the EXACT telescoping for the RHS descent (1-q^b)RHS(a,b)=RHS(a,b-1).

From durfee_descent_struct.py:
  (1-q^b) T_r(b) = q^{a-r} T_r(b-1) + B_r,   B_r := q^{b-r}(1-q^r) T_r(b),  T_r(b-1):=0 if r>min(a,b-1).
  Goal: sum_r (1-q^b)T_r(b) = sum_r T_r(b-1).
  Equivalent: sum_r B_r = sum_r (1 - q^{a-r}) T_r(b-1)     (call RHS-resid).
We seek a per-term match  B_r  <->  a shifted copy that telescopes.  Two natural guesses:
  (G1)  B_r telescopes in r:  B_r = C_{r-1} - C_r  for some C (Abel/telescoping sum).
  (G2)  B_r equals a piece of the (1-q^{a-r})T_r(b-1) residual after a reindex r->r-1.

Recall T_r(b) = q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}.
  B_r = q^{b-r}(1-q^r) q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}.
  Use (1-q^r)P_r = P_{r-1} (r>=1).  =>  B_r = q^{b-r} q^{(a-r)(b-r)} P_{a-r} P_{r-1} P_{b-r}.
Compare to T_{r-1}(b-1) = q^{(a-r+1)(b-r)} P_{a-r+1} P_{r-1} P_{b-r}.
  Ratio of q-exponents: (b-r)+(a-r)(b-r) = (b-r)(a-r+1) = (a-(r-1))(b-r) -- SAME as exponent of
  T_{r-1}(b-1)!  But P_{a-r} vs P_{a-r+1}=P_{a-(r-1)}: differ by geomFactor(a-r+1).
So  B_r = (1-q^{a-r+1}) T_{r-1}(b-1)   [since P_{a-r}=(1-q^{a-r+1})P_{a-r+1}].  TEST THIS.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "03-qseries-route", "scratch"))
from qseries import P_s, pmul, padd, trunc, PREC, pscale_shift

def psub(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)]
def one_minus_qk(k):
    out = [0]*PREC; out[0] = 1
    if 0 <= k < PREC: out[k] -= 1
    return out
def qpow(e):
    out = [0]*PREC
    if 0 <= e < PREC: out[e] = 1
    return out
def nz(d): return [(i, c) for i, c in enumerate(d) if c != 0]

def term(a, b, r):
    """T_r(b) = q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}, valid 0<=r<=min(a,b)."""
    return pscale_shift(pmul(pmul(P_s(a-r), P_s(r)), P_s(b-r)), 1, (a-r)*(b-r))

def B_term(a, b, r):
    return pmul(qpow(b-r), pmul(one_minus_qk(r), term(a, b, r)))

# --- the clean per-term claim:  B_r = (1 - q^{a-r+1}) T_{r-1}(b-1),  for 1<=r<=min(a,b) ---
print("=== B_r = (1-q^{a-r+1}) T_{r-1}(b-1)  for 1<=r<=min(a,b) ===")
bf = 0
for a in range(0, 9):
    for b in range(1, 9):
        for r in range(1, min(a, b)+1):
            B = trunc(B_term(a, b, r))
            # T_{r-1}(b-1): need r-1 <= min(a, b-1). r-1<=a-? and r-1<=b-1 since r<=b. a side:
            # T_{r-1}(b-1) uses P_{a-(r-1)}=P_{a-r+1}; valid if a-r+1>=0 i.e. r<=a+1; and r-1>=0. ok.
            if a - r + 1 < 0:
                continue
            tgt = trunc(pmul(one_minus_qk(a-r+1), term(a, b-1, r-1)))
            if B != tgt:
                bf += 1
                if bf <= 6: print(f"   FAIL a={a} b={b} r={r}: {nz(psub(B,tgt))[:4]}")
print("  per-term B_r identity OK" if bf == 0 else f"  {bf} FAIL")

# Now the descent assembled from two clean per-term facts:
#   (PA)  (1-q^{b-r}) T_r(b) = q^{a-r} T_r(b-1)          [r<=min(a,b-1)]   -- "shrink the b-Pochhammer"
#   (PB)  q^{b-r}(1-q^r) T_r(b) = (1-q^{a-r+1}) T_{r-1}(b-1)   [1<=r<=min(a,b)] -- "shift r down"
#   (split) 1-q^b = (1-q^{b-r}) + q^{b-r}(1-q^r)
# So (1-q^b) T_r(b) = q^{a-r} T_r(b-1) + (1-q^{a-r+1}) T_{r-1}(b-1).
# Summing over r=0..R (R=min(a,b)) and using T_R(b-1)=0 when R=b (i.e. b<=a, r=b>min(a,b-1)):
#   sum_r [q^{a-r}T_r(b-1)] + sum_{r>=1}[(1-q^{a-r+1})T_{r-1}(b-1)]
#   reindex 2nd sum s=r-1:  sum_s (1-q^{a-s})T_s(b-1).
#   total coeff of T_s(b-1):  q^{a-s} + (1-q^{a-s}) = 1.   => sum_s T_s(b-1) = RHS(a,b-1).  QED.
print("\n=== assembled descent via the two per-term facts + reindex: total = RHS(a,b-1) ===")
df = 0
for a in range(0, 9):
    for b in range(1, 9):
        R = min(a, b)
        acc = [0]*PREC
        for r in range(0, R+1):
            # (1-q^b)T_r(b) = q^{a-r}T_r(b-1) + (1-q^{a-r+1})T_{r-1}(b-1)
            acc = padd(acc, pmul(one_minus_qk(b), term(a, b, r)))
        # rebuild target from the per-term decomposition (no direct (1-q^b) mult):
        rebuilt = [0]*PREC
        for r in range(0, R+1):
            if r <= min(a, b-1):
                rebuilt = padd(rebuilt, pscale_shift(term(a, b-1, r), 1, a-r))         # q^{a-r}T_r(b-1)
            if r >= 1 and a-r+1 >= 0:
                rebuilt = padd(rebuilt, pmul(one_minus_qk(a-r+1), term(a, b-1, r-1)))  # (1-q^{a-r+1})T_{r-1}(b-1)
        if trunc(acc) != trunc(rebuilt):
            df += 1
            if df <= 4: print(f"   decomp FAIL a={a} b={b}: {nz(psub(trunc(acc),trunc(rebuilt)))[:4]}")
        # and rebuilt should equal RHS(a,b-1):
        RHSm = [0]*PREC
        for s in range(0, min(a, b-1)+1):
            RHSm = padd(RHSm, term(a, b-1, s))
        if trunc(rebuilt) != trunc(RHSm):
            df += 1
            if df <= 8: print(f"   target FAIL a={a} b={b}: {nz(psub(trunc(rebuilt),trunc(RHSm)))[:4]}")
print("  assembled descent OK" if df == 0 else f"  {df} FAIL")

# boundary sanity: the r=R=b term (when b<=a) has T_R(b-1)=T_b(b-1) with b>min(a,b-1)=b-1 -> ZERO.
# Confirm the q^{a-r}T_r(b-1) part vanishes there and only the (1-q^{a-r+1})T_{r-1}(b-1) survives.
print("\n=== boundary: top term r=R contributes only via the shift piece when R=b<=a ===")
print("  (covered by the index guards r<=min(a,b-1) and r>=1 above; OK if assembled descent OK)")

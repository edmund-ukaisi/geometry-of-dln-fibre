"""Thread 06 — WHY does (1-q^b) RHS(a,b) = RHS(a,b-1) hold?  Pin the term-level mechanism.

RHS(a,b) = sum_{r=0}^{min(a,b)} q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}.

Multiply term r by (1-q^b). Use P_{b-r} = P_{b-1-r} * geomFactor(b-r) ... no: peel on b.
Better: (1-q^b) acts and we expect to land on RHS(a,b-1) = sum_{r=0}^{min(a,b-1)} q^{(a-r)(b-1-r)} P_{a-r}P_r P_{b-1-r}.

Hypothesised mechanism (Abel summation / telescoping in r):
Define T_r(b) = q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}  (term r of RHS(a,b)).
We test the per-pair telescoping identity:
   (1-q^b) T_r(b)  ?=  T_r(b-1)  +  [boundary that telescopes against neighbour r].

Use the factorization on the (b-r)-Pochhammer:  P_{b-r} = P_{b-r-1} * geomFactor(b-r),
and geomFactor(b-r)*(1-q^{b-r}) = 1.  So  (1-q^{b-r}) P_{b-r} = P_{b-r-1} = P_{(b-1)-r}.
That gives  (1-q^{b-r}) T_r(b) involving P_{(b-1)-r}.  But we multiply by (1-q^b), not (1-q^{b-r}).
Write 1-q^b = (1-q^{b-r}) + q^{b-r}(1-q^r)  [algebraic split].  TEST this split first.
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
    """T_r(b) = q^{(a-r)(b-r)} P_{a-r} P_r P_{b-r}."""
    return pscale_shift(pmul(pmul(P_s(a-r), P_s(r)), P_s(b-r)), 1, (a-r)*(b-r))

def durfee_rhs(a, b):
    acc = [0]*PREC
    for r in range(0, min(a, b)+1):
        acc = padd(acc, term(a, b, r))
    return trunc(acc)

# --- scalar split:  1 - q^b = (1-q^{b-r}) + q^{b-r}(1 - q^r) ---
print("=== scalar split 1-q^b = (1-q^{b-r}) + q^{b-r}(1-q^r) ===")
sf = 0
for b in range(0, 9):
    for r in range(0, b+1):
        lhs = one_minus_qk(b)
        rhs = padd(one_minus_qk(b-r), pmul(qpow(b-r), one_minus_qk(r)))
        if trunc(lhs) != trunc(rhs):
            sf += 1
print("  split OK" if sf == 0 else f"  {sf} FAIL")

# Now (1-q^b) T_r(b) = (1-q^{b-r}) T_r(b) + q^{b-r}(1-q^r) T_r(b).
#  Part A: (1-q^{b-r}) T_r(b): uses (1-q^{b-r})P_{b-r}=P_{b-1-r}, so A_r = q^{(a-r)(b-r)} P_{a-r}P_r P_{b-1-r}.
#     Note (a-r)(b-r) = (a-r)((b-1-r)+1) = (a-r)(b-1-r) + (a-r).  So A_r = q^{a-r} T_r(b-1).
#  Part B: q^{b-r}(1-q^r) T_r(b): uses (1-q^r)P_r = P_{r-1} (for r>=1; r=0 -> 0).
#     B_r = q^{b-r} q^{(a-r)(b-r)} P_{a-r} P_{r-1} P_{b-r}  (r>=1).
#  CLAIM (telescoping): sum_r A_r + sum_r B_r = sum_r T_r(b-1) = RHS(a,b-1).
#  i.e.  sum_r (A_r - T_r(b-1)) + sum_r B_r = 0, a telescoping in r between A/B-shifted indices.
print("\n=== Part A:  (1-q^{b-r}) T_r(b)  ==  q^{a-r} T_r(b-1)  (per term, r<=min(a,b-1)) ===")
af = 0
for a in range(0, 8):
    for b in range(1, 8):
        for r in range(0, min(a, b-1)+1):
            A = trunc(pmul(one_minus_qk(b-r), term(a, b, r)))
            tgt = pscale_shift(term(a, b-1, r), 1, a-r)
            if A != tgt:
                af += 1
                if af <= 4: print(f"   A FAIL a={a} b={b} r={r}: {nz(psub(A,tgt))[:4]}")
print("  Part A OK" if af == 0 else f"  {af} FAIL")

# Define A_r := q^{a-r} T_r(b-1),  B_r := q^{b-r}(1-q^r) T_r(b) for r>=1.
def A_term(a, b, r):  # for r <= min(a,b-1)
    return pscale_shift(term(a, b-1, r), 1, a-r)
def B_term(a, b, r):  # for 1 <= r <= min(a,b)
    return pmul(qpow(b-r), pmul(one_minus_qk(r), term(a, b, r)))

# verify (1-q^b)T_r(b) = A_part + B_part term by term, where A_part uses (1-q^{b-r})T_r(b) [not q^{a-r}T_r(b-1) when r=min=b? boundary]
print("\n=== reconstruct: (1-q^b)RHS(a,b) = sum_r (1-q^{b-r})T_r(b) + sum_{r>=1} B_term  ===")
rf = 0
for a in range(0, 8):
    for b in range(1, 8):
        full = trunc(pmul(one_minus_qk(b), durfee_rhs(a, b)))
        accA = [0]*PREC
        for r in range(0, min(a, b)+1):
            accA = padd(accA, pmul(one_minus_qk(b-r), term(a, b, r)))  # (1-q^{b-r})T_r(b)
        accB = [0]*PREC
        for r in range(1, min(a, b)+1):
            accB = padd(accB, B_term(a, b, r))
        recon = trunc(padd(accA, accB))
        if full != recon:
            rf += 1
print("  reconstruction OK" if rf == 0 else f"  {rf} FAIL")

# Now the KEY telescoping:  sum_r (1-q^{b-r})T_r(b) + sum_{r>=1} B_term(r)  ==  RHS(a,b-1).
#  We expect a shift: B_term(a,b,r) telescopes with the gap between (1-q^{b-r})T_r(b) and T_r(b-1).
#  Test the consolidated telescoping directly:
print("\n=== KEY: sum_r (1-q^{b-r})T_r(b) + sum_{r>=1} B_term(r) == RHS(a,b-1)? ===")
kf = 0
for a in range(0, 9):
    for b in range(1, 9):
        accA = [0]*PREC
        for r in range(0, min(a, b)+1):
            accA = padd(accA, pmul(one_minus_qk(b-r), term(a, b, r)))
        accB = [0]*PREC
        for r in range(1, min(a, b)+1):
            accB = padd(accB, B_term(a, b, r))
        recon = trunc(padd(accA, accB))
        tgt = durfee_rhs(a, b-1)
        if recon != tgt:
            kf += 1
            if kf <= 4: print(f"   KEY FAIL a={a} b={b}: {nz(psub(recon,tgt))[:6]}")
print("  KEY telescoping OK" if kf == 0 else f"  {kf} FAIL")

#!/usr/bin/env python3
# =============================================================================
# WITNESS W3 — TIGHTNESS AT THE BINDING CELL  (executable kill-condition, exact)
# =============================================================================
# DISCRIMINATOR (prodcorank-cert.md §3; decstep-cert.md §2, §3 lines 83-94):
#   The budget/threshold inequalities the native engine carries are EXACTLY TIGHT
#   at the binding cell: the per-cut threshold meets c* = 1/2 * minAdm(n,n,n,n)
#   with EQUALITY there, and is STRICTLY above it elsewhere. There is NO slack at
#   the binding cut — a peel that loses even delta of budget there breaks c*.
#
# OPERATOR RULE (binding, applies to the engine):
#   any inequality-shaped condition the engine will carry gets an
#   EQUALITY-AT-BINDING-CELL witness, not only a truth scan.
#   This witness supplies that equality certificate (exact Fractions) for every
#   budget inequality the engine carries, PLUS the paired strict-undershoot that
#   shows which accounting is INVALID on the balanced locus.
#
# ENGINE KILL-CONDITIONS GUARDED:
#   (A) master peel budget:   minAdm(M) = min_t [ peelCharge(M,t) + minAdm(redChain t M) ]
#       -- equality at the argmin (binding) cut(s), strict above off them.
#   (B) free-block outer peel: T_m = 1/2 m^2 + 1/2 minAdm((n-m,n,n)) >= c*,
#       equality at the binding corank m*. (This is (A)'s top peel, m = n - t.)
#   (C) balanced product-corank threshold: T_k = 1/2 ( C_k + n(n-k) ) >= c*,
#       equality at the binding stratum k*. (decstep (C_k + n r')/2 identity.)
#   (D) GUARD / invalid split: pairing the TRUE product codim C_m with an
#       independent RECURSIVE reduced chain, T_m = 1/2 C_m + 1/2 minAdm((n-m,n,n)),
#       STRICTLY UNDERSHOOTS c* for n>=4. The engine must not use this pairing.
#
# EXACT INSTRUMENT: exact-integer DP (minAdm) + exact rational arithmetic
#   (fractions.Fraction). No floats anywhere.
#
# FAMILY: headline n=4..7 (per the cert); robustness n=3..8.
#
# EXPECTED RESULT (see w3_tightness_at_binding_cell.out for the verbatim run):
#   (A) equality at every argmin cut, strict above off it.
#   (B) T_m >= c* all m, EQUALITY exactly at m*, STRICT above off m*.
#   (C) T_k >= c* all k, EQUALITY exactly at k*, STRICT above off k*.
#   (D) at least one balanced stratum with T_m < c* (strict undershoot), n>=4.
# =============================================================================

from functools import lru_cache
from fractions import Fraction as F

def hdr(s): print("\n" + "="*70 + "\n" + s + "\n" + "="*70)
def Ck(k): return k*k - (k*k)//4
def redChain(t, M): return (t,) + M[2:]
def peelCharge(M, t): return (M[0]-t)*(M[1]-t)

@lru_cache(None)
def minAdm(M):
    L = len(M)
    if L == 1: return 0
    if L == 2: return M[0]*M[1]
    best = None
    for t in range(0, min(M[0], M[1]) + 1):
        v = peelCharge(M, t) + minAdm(redChain(t, M))
        best = v if best is None else min(best, v)
    return best

HEAD = range(4, 8)   # headline n=4..7
SWEEP = range(3, 9)  # robustness n=3..8

# =============================================================================
# (A) MASTER PEEL BUDGET — equality at the argmin cut(s), strict above off them.
# =============================================================================
hdr("(A) master peel budget: minAdm(M) = min_t [peelCharge + minAdm(redChain)]")
A_ok = True
for n in SWEEP:
    M = (n, n, n, n)
    mval = minAdm(M)
    vals = {t: peelCharge(M, t) + minAdm(redChain(t, M)) for t in range(0, n+1)}
    binding = sorted(t for t, v in vals.items() if v == mval)
    off = sorted(t for t in vals if t not in binding)
    eq_ok = all(vals[t] == mval for t in binding)                 # EQUALITY at binding
    strict_ok = all(vals[t] > mval for t in off)                  # STRICT above off it
    A_ok &= (eq_ok and strict_ok and len(binding) >= 1)
    tag = "  <== HEADLINE" if n in HEAD else ""
    print(f" n={n}: minAdm={mval}  binding cut t*={binding} (corank m*={[n-t for t in binding]})"
          f"  eq@binding={eq_ok}  strict@off={strict_ok}{tag}")
    # show the exact per-cut ledger for one headline case
    if n == 4:
        for t in range(0, n+1):
            mark = " <= BINDING (equality)" if t in binding else ""
            print(f"     t={t}: peelCharge={peelCharge(M,t):>2} + minAdm({redChain(t,M)})="
                  f"{minAdm(redChain(t,M)):>2}  = {vals[t]:>2}{mark}")
print("(A) VERDICT  equality at binding cut, strict above off it, all n:", A_ok)

# =============================================================================
# (B) FREE-BLOCK OUTER PEEL — T_m = 1/2 m^2 + 1/2 minAdm((n-m,n,n)) >= c*,
#     equality exactly at binding corank m*.  [the native engine's budget]
# =============================================================================
hdr("(B) free-block outer peel:  T_m = 1/2 m^2 + 1/2 minAdm((n-m,n,n))  >= c*")
B_ok = True
for n in SWEEP:
    cstar = F(minAdm((n, n, n, n)), 2)
    T = {m: F(m*m, 2) + F(minAdm((n-m, n, n)), 2) for m in range(0, n+1)}
    tmin = min(T.values())
    binding = sorted(m for m, v in T.items() if v == cstar)
    off = sorted(m for m in T if m not in binding)
    ge_ok = all(T[m] >= cstar for m in T)                        # inequality holds
    min_eq = (tmin == cstar)                                     # min meets c* exactly
    eq_ok = all(T[m] == cstar for m in binding)                  # EQUALITY at binding
    strict_ok = all(T[m] > cstar for m in off)                  # STRICT above off it
    B_ok &= (ge_ok and min_eq and eq_ok and strict_ok and len(binding) >= 1)
    tag = "  <== HEADLINE" if n in HEAD else ""
    print(f" n={n}: c*={cstar}  min_m T_m={tmin} (==c*? {min_eq})  binding m*={binding}"
          f"  T_m>=c* all m={ge_ok}  eq@binding={eq_ok}  strict@off={strict_ok}{tag}")
print("(B) VERDICT  T_m>=c* with equality exactly at binding m*, all n:", B_ok)

# =============================================================================
# (C) BALANCED PRODUCT-CORANK THRESHOLD — T_k = 1/2 (C_k + n(n-k)) >= c*,
#     equality exactly at binding stratum k*.  [decstep (C_k + n r')/2 identity]
# =============================================================================
hdr("(C) balanced product-corank threshold:  T_k = 1/2 (C_k + n(n-k))  >= c*")
C_ok = True
for n in SWEEP:
    cstar = F(minAdm((n, n, n, n)), 2)
    T = {k: F(Ck(k) + n*(n-k), 2) for k in range(0, n+1)}
    tmin = min(T.values())
    binding = sorted(k for k, v in T.items() if v == cstar)
    off = sorted(k for k in T if k not in binding)
    ge_ok = all(T[k] >= cstar for k in T)
    min_eq = (tmin == cstar)
    eq_ok = all(T[k] == cstar for k in binding)
    strict_ok = all(T[k] > cstar for k in off)
    C_ok &= (ge_ok and min_eq and eq_ok and strict_ok and len(binding) >= 1)
    tag = "  <== HEADLINE" if n in HEAD else ""
    print(f" n={n}: c*={cstar}  min_k T_k={tmin} (==c*? {min_eq})  binding k*={binding}"
          f"  T_k>=c* all k={ge_ok}  eq@binding={eq_ok}  strict@off={strict_ok}{tag}")
    if n == 5:
        for k in range(0, n+1):
            mark = " <= BINDING (equality)" if k in binding else ""
            print(f"     k={k}: C_k={Ck(k):>2} + n(n-k)={n*(n-k):>2}  -> T_k={T[k]}{mark}")
print("(C) VERDICT  T_k>=c* with equality exactly at binding k*, all n:", C_ok)

# =============================================================================
# (D) GUARD — the INVALID split: C_m paired with a recursive reduced chain
#     STRICTLY UNDERSHOOTS c*.  The engine must NOT use this pairing.
# =============================================================================
hdr("(D) GUARD: T_m = 1/2 C_m + 1/2 minAdm((n-m,n,n)) STRICTLY UNDERSHOOTS c* (n>=4)")
D_ok = True
for n in SWEEP:
    cstar = F(minAdm((n, n, n, n)), 2)
    T = {m: F(Ck(m), 2) + F(minAdm((n-m, n, n)), 2) for m in range(0, n+1)}
    under = sorted((m, T[m], cstar - T[m]) for m in T if T[m] < cstar)  # (m, T_m, deficit)
    has_under = (len(under) > 0)
    if n >= 4:
        D_ok &= has_under   # for n>=4 the invalid split MUST expose an undershoot
    tag = "  <== HEADLINE" if n in HEAD else ""
    ustr = ", ".join(f"m={m}:T={t}(deficit {d})" for (m, t, d) in under) or "none"
    print(f" n={n}: c*={cstar}  undershooting balanced strata: {ustr}{tag}")
print("(D) VERDICT  invalid split exposes a strict undershoot for every n>=4:", D_ok)

# =============================================================================
hdr("W3 OVERALL")
ok = A_ok and B_ok and C_ok and D_ok
print("(A) master peel budget tight at binding cut:", A_ok)
print("(B) free-block outer peel equality at m*:", B_ok)
print("(C) balanced product-corank equality at k*:", C_ok)
print("(D) invalid split strictly undershoots (guard):", D_ok)
print("W3 PASS:", ok)
assert ok, "W3 FAILED — a load-bearing exhibit did not reproduce"
print("\n[W3] the budget inequalities are EXACTLY tight at the binding cell "
      "(equality, no slack); the invalid C_m-plus-reduced-chain split undershoots.")

# =============================================================================
# CHECKED-IN OUTPUT: see w3_tightness_at_binding_cell.out . Key lines:
#   (A) VERDICT  equality at binding cut, strict above off it, all n: True
#   (B) VERDICT  T_m>=c* with equality exactly at binding m*, all n: True
#   (C) VERDICT  T_k>=c* with equality exactly at binding k*, all n: True
#   (D) VERDICT  invalid split exposes a strict undershoot for every n>=4: True
#   W3 PASS: True
# =============================================================================

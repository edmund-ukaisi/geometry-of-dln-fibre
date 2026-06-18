"""Exact verification of the two CThetaExplicit bridges against the committed Gqip.

Run: python3 verify.py
"""
import sympy as sp
from itertools import product

# Gqip d e = sum_{j<=i} e_i (e_j + d_{j+1} - d_j)  (Lean indexing: i,j in 0..N-1, d in 0..N).
def Gqip(d, e):
    N = len(e)
    return sum(e[i]*(e[j] + d[j+1] - d[j]) for i in range(N) for j in range(N) if j <= i)

# 1. Square completion: 2 Gqip - (sum e)^2 = sum (e_i - s_i)^2 - sum s_i^2, s_i = d_0 - d_{i+1}.
print("Square completion (s_i = d 0 - d i.succ):")
for N in range(1, 7):
    e = sp.symbols(f'e0:{N}')
    d = sp.symbols(f'd0:{N+1}')
    s = [d[0] - d[i+1] for i in range(N)]
    lhs = sp.expand(2*Gqip(d, list(e)) - (sum(e))**2)
    rhs = sp.expand(sum((e[i]-s[i])**2 for i in range(N)) - sum(s[i]**2 for i in range(N)))
    print(f"  N={N}: {sp.simplify(lhs-rhs)==0}")

# 2. Integer-square optimum: min{sum t^2 : t in Z^m, sum t = delta} = |delta| for |delta| <= m.
print("Integer-square optimum (min sum t^2 = |delta|):")
def brute(m, delta, R=6):
    return min(sum(x*x for x in t) for t in product(range(-R, R+1), repeat=m) if sum(t) == delta)
ok = True
for m in range(1, 5):
    for delta in range(-m, m+1):
        ok &= (brute(m, delta) == abs(delta))
print(f"  m=1..4, |delta|<=m: {ok}")

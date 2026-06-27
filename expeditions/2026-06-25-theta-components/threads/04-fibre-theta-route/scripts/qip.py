# Brute-force the QIP for Sigma^0 of (2,2,2,2,2):
# G(e) = sum_{1<=j<=i<=N} e_i (e_j + d'_j - d'_{j-1}),  s.t. e_i in N, sum_{i=1}^N e_i = d'_0
# d' = (2,2,2,2,2), N=4, d'_0=2.  Find minimizers, count them.
from itertools import product
dp = [2,2,2,2,2]
N = 4
d0 = dp[0]
def G(e):  # e = (e_1,...,e_N)
    tot = 0
    for i in range(1,N+1):
        for j in range(1,i+1):
            tot += e[i-1]*(e[j-1] + dp[j] - dp[j-1])
    return tot
sols=[]
# e_i can range 0..d0
rng = range(0, d0+1)
for e in product(rng, repeat=N):
    if sum(e)==d0:
        sols.append((G(e), e))
mn = min(g for g,_ in sols)
opt = [e for g,e in sols if g==mn]
print("QIP min G =", mn)
print("num optimal e-vectors =", len(opt))
for e in opt: print("   ", e)

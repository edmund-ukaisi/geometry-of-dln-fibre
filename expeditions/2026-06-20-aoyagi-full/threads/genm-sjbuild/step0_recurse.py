"""
STEP-0: full recursive enumeration of EVERY (cut t, deeper) chart the sjBoundaryPeel/sjJointResolution
recursion visits, flagging where the deeper factor Q_b is RANK-DEFICIENT (the ONLY place the monomial
terminal sjLoss_terminal is load-bearing; elsewhere regime A + soundness gate close at EXACTLY 1/2*minAdm).

Rank-deficiency criterion (derived): at chain cur=(m,n, rest...), peel cut t, corank block p x q,
p=m-t, q=n-t. The block Gamma (p x q) couples through Q_b (the q non-pivot node-1 rows -> deeper product
of widths `rest`), rank(Q_b) = min(q, min(rest)). Gamma |-> Gamma.Q_b is INJECTIVE (clean isotropic Morse
of dim pq -> regime A/B applies) iff Q_b has full ROW rank q, i.e. min(rest) >= q. RANK-DEFICIENT iff
min(rest) < q  (== M1 - t > min(deeper widths), the docstring criterion).
"""
from functools import lru_cache

@lru_cache(None)
def minAdm(M):
    M = tuple(M); L = len(M) - 1
    if L == 0: return 0
    if L == 1: return M[0] * M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def redChain(t, M): return (t,) + tuple(M[2:])

def enumerate_charts(M, seen=None):
    """Recursively visit every chain the recursion reaches; return list of (chain, t, p,q, rest, rankdef)."""
    if seen is None: seen = set()
    out = []
    M = tuple(M)
    if M in seen or len(M) < 3:
        return out
    seen.add(M)
    m, n = M[0], M[1]; rest = M[2:]
    for t in range(1, min(m, n) + 1):          # front peel cuts 1..min (t=0 whole-box excluded)
        p, q = m - t, n - t
        rankdef = (rest != ()) and (min(rest) < q)
        out.append((M, t, p, q, rest, rankdef))
    # recurse into every reduced chain (all cuts 0..min, since deeper recursion visits redChain t)
    for t in range(0, min(m, n) + 1):
        out += enumerate_charts(redChain(t, M), seen)
    return out

for M in [(3,3,4), (2,2,2,2), (3,3,3,4), (3,3,2,2), (4,4,2,2)]:
    charts = enumerate_charts(M)
    rankdef = [c for c in charts if c[5]]
    print(f"\nM={M}  minAdm={minAdm(M)}  total charts visited={len(charts)}  RANK-DEFICIENT charts={len(rankdef)}")
    for (chain, t, p, q, rest, rd) in charts:
        tag = "  <== RANK-DEFICIENT (monomial terminal load-bearing)" if rd else ""
        print(f"    chain={chain} cut t={t}: corank {p}x{q} charge={p*q}, deeper rest={rest} min(rest)={min(rest) if rest else '-'}{tag}")

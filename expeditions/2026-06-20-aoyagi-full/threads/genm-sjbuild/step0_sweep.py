"""
STEP-0 broad sweep: is the monomial terminal EVER load-bearing?

At a chain `cur` the recursion visits, local threshold c' < 1/2*minAdm(cur). Peel cut t, corank p x q
(p=m-t, q=n-t), deeper factor Q_b has rank r = min(q, min(rest)).
  - The freed block Gamma (p x q). frobSq(Gamma.Q_b) depends on p*r nondegenerate directions; the
    remaining p*(q-r) directions are FLAT (kernel of .Q_b) -> integrate to a bounded constant on the box.
  - regime B (Morse dominance) covers the chart for c' < p*r/2 (effective Morse dim = p*r).
  - regime A (exponent shift, clean hand to IH) needs Q_b FULL row rank: r = q  (min(rest) >= q).
The monomial terminal sjLoss_terminal is load-bearing ONLY on a chart that is
    RANK-DEFICIENT (r < q)  AND  regime-B does not already cover it, i.e.  p*r < minAdm(cur)
    (so there exists c' in (p*r/2, 1/2*minAdm(cur)) that neither regime A [rank-def] nor regime B covers).

Sweep all chains M (arities 3..5, widths 1..W) and report any chart hitting the load-bearing condition.
"""
from functools import lru_cache
import itertools

@lru_cache(None)
def minAdm(M):
    M = tuple(M); L = len(M) - 1
    if L == 0: return 0
    if L == 1: return M[0] * M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def redChain(t, M): return (t,) + tuple(M[2:])

def visit(M, seen):
    M = tuple(M)
    if M in seen or len(M) < 3: return []
    seen.add(M)
    out = [M]
    for t in range(0, min(M[0], M[1]) + 1):
        out += visit(redChain(t, M), seen)
    return out

def load_bearing_charts(M):
    """charts where the monomial terminal is genuinely load-bearing."""
    hits = []
    for cur in visit(M, set()):
        m, n, rest = cur[0], cur[1], cur[2:]
        mm = minAdm(cur)
        for t in range(1, min(m, n) + 1):
            p, q = m - t, n - t
            r = min(q, min(rest)) if rest else q
            rank_def = (rest != ()) and (r < q)
            # regime A clean iff full rank; regime B covers iff p*r >= mm (i.e. c'<1/2 mm <= p*r/2).
            regimeB_covers = (p * r >= mm)
            if rank_def and not regimeB_covers:
                hits.append((cur, t, p, q, r, p*r, mm))
    return hits

W = 6
total_lb = 0
examples = []
for arity in [3, 4, 5]:
    for widths in itertools.product(range(1, W+1), repeat=arity):
        hits = load_bearing_charts(widths)
        if hits:
            total_lb += 1
            if len(examples) < 25:
                examples.append((widths, hits))

print(f"Swept all chains of arity 3,4,5 with widths in 1..{W}.")
print(f"Chains with a genuinely load-bearing monomial-terminal chart: {total_lb}")
if examples:
    print("\nExamples (chain -> [(cur, t, p, q, rank r, p*r=effMorse, minAdm(cur))]):")
    for widths, hits in examples:
        print(f"  M={widths}  minAdm={minAdm(widths)}:")
        for h in hits:
            print(f"      cur={h[0]} t={h[1]} corank {h[2]}x{h[3]} rank(Q_b)={h[4]} effMorse=p*r={h[5]} minAdm(cur)={h[6]}")
else:
    print("\n*** NO chain has a load-bearing monomial-terminal chart. ***")
    print("    => regime B (Morse dominance, effective dim p*rank(Q_b)) covers EVERY rank-deficient chart;")
    print("       regime A covers every full-rank chart. The monomial terminal sjLoss_terminal is never")
    print("       reached with a threshold below 1/2*minAdm. The count<->monomial bridge is VACUOUS.")

# sanity: confirm the three named anchors + witnesses have zero load-bearing charts:
print("\nNamed anchors + rank-deficient witnesses:")
for M in [(3,3,4),(2,2,2,2),(3,3,3,4),(3,3,2,2),(4,4,2,2),(5,5,2,2),(6,6,2,2),(5,5,2,3),(6,6,3,2)]:
    print(f"  M={M}: load-bearing monomial charts = {load_bearing_charts(M)}")

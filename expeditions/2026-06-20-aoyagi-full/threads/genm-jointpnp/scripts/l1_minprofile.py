"""
DECORRELATED re-derivation (NOT d1_discriminate.py):
Lane-1 obstruction hunt, part 1 -- the MINIMIZING-PATH MIN-PROFILE.

Question: the single-factor native recursion computes
   minAdm(M) = min_t [ (M0-t)(M1-t) + minAdm(t, M2, ...) ].
Each recursion step "peels" the front M0xM1 at effective source rank t, paying the
rank-<=t codim (M0-t)(M1-t), then recurses on (t, M2, ...). The peel's "corank"
is (a,b) = (M0-t, M1-t), min-corank d = min(a,b).

The DISPATCH (controller): d<=1 peel = native (Lane 1); d>=2 peel = CITE (Aoyagi product-corank).

OBSTRUCTION TEST: is there a chain M whose codim minAdm(M) can be achieved ONLY by a
minimizing path that, at some level, is FORCED to take a peel with d = min(M0-t,M1-t) >= 2?
If so, that chain's native charge itself requires a product-corank step -- and if such a
chain is (mis)classified Lane-1 at its OUTER peel, the native resolution has a min>=2 heart.

We build minAdm from scratch (independent transcription) and, for EVERY chain up to a width
bound, record: (i) minAdm; (ii) the FULL set of minimizing peels at the top level;
(iii) whether minAdm is achievable with a TOP peel of d<=1; (iv) recursively, whether there
is a WHOLLY-d<=1 minimizing PATH (every peel along it has d<=1).
"""
from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minAdm(M):
    n = len(M)
    if n <= 1: return 0
    if n == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(0, min(M[0],M[1])+1))

@lru_cache(maxsize=None)
def has_all_d_le_1_optimal_path(M):
    """True iff minAdm(M) is achieved by SOME minimizing path in which EVERY peel has
       d = min(M0-t, M1-t) <= 1. (Base chains of length<=2 vacuously true.)"""
    n = len(M)
    if n <= 2:
        return True
    best = minAdm(M)
    for t in range(0, min(M[0],M[1])+1):
        d = min(M[0]-t, M[1]-t)
        val = (M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:])
        if val == best and d <= 1 and has_all_d_le_1_optimal_path((t,)+M[2:]):
            return True
    return False

@lru_cache(maxsize=None)
def optimal_top_peels(M):
    n = len(M)
    if n <= 2: return ()
    best = minAdm(M)
    return tuple(t for t in range(0, min(M[0],M[1])+1)
                 if (M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) == best)

def gen_chains(Ls, wmax, wmin=1):
    for L in Ls:
        for M in product(range(wmin, wmax+1), repeat=L):
            yield M

# ---- Census: which chains FORCE a min>=2 peel on every optimal path? ----
Ls = [3,4,5]
WMAX = 6
forced_min2 = []   # chains with NO wholly-d<=1 optimal path
total = 0
for M in gen_chains(Ls, WMAX):
    total += 1
    if not has_all_d_le_1_optimal_path(M):
        forced_min2.append(M)

print(f"chains checked (L in {Ls}, width 1..{WMAX}): {total}")
print(f"chains with NO wholly-d<=1 optimal path (FORCE a min>=2 peel): {len(forced_min2)}")
if forced_min2:
    print("  smallest examples (by total width):")
    for M in sorted(forced_min2, key=lambda m:(sum(m),len(m),m))[:20]:
        tops = optimal_top_peels(M)
        topd = [min(M[0]-t,M[1]-t) for t in tops]
        print(f"    M={M}  minAdm={minAdm(M)}  optimal top peels t={tops} (d={topd})")

# ---- Cross-check: of those, how many have a d<=1 TOP peel (so classified Lane-1 at outer)? ----
print()
lane1_outer_but_forced = []
for M in forced_min2:
    tops = optimal_top_peels(M)
    if any(min(M[0]-t, M[1]-t) <= 1 for t in tops):
        lane1_outer_but_forced.append(M)
print(f"of the forced-min>=2 chains, # with a d<=1 optimal TOP peel (Lane-1-looking outer): {len(lane1_outer_but_forced)}")
for M in sorted(lane1_outer_but_forced, key=lambda m:(sum(m),m))[:20]:
    print(f"    M={M}  minAdm={minAdm(M)}  tops={optimal_top_peels(M)}")

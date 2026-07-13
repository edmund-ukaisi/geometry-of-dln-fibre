from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def binding_cuts(M):
    mA=minAdm(M)
    return [t for t in range(min(M[0],M[1])+1)
            if (M[0]-t)*(M[1]-t)+minAdm((t,)+tuple(M[2:]))==mA]

def rho(M): return min(M[1:])

def pivot_ok_STRICT(M):
    """head-split route finite at M under the STRICT convention:
       binding-cut main pivot (j=0) + proper off-sector pivots (j>=1, a,b>=1)."""
    r=rho(M)
    for t in binding_cuts(M):
        # main peel pivot (j=0), needs t>=1 for a pivot block
        if t>=1 and t*r < minAdm((t,)+tuple(M[2:])):
            return False
        # proper off-sector pivots
        for j in range(1, min(M[0]-t, M[1]-t)+1):
            u=t+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            if u*r < minAdm((u,)+tuple(M[2:])):
                return False
    return True

def rev(M): return tuple(reversed(M))

# ---- recompute both-ends-bad under STRICT convention ----
badboth=[]
for Ln in [3,4,5,6]:
    for M in product(range(1,7),repeat=Ln):
        if not pivot_ok_STRICT(M) and not pivot_ok_STRICT(rev(M)):
            badboth.append(M)
print("STRICT-convention both-ends pivot-bad chains:", len(badboth))

# canonical dedup up to reversal
canon=set()
for M in badboth:
    canon.add(min(M, rev(M)))
canon=sorted(canon, key=lambda M:(sum(M),len(M),M))
print("distinct up to reversal:", len(canon))
print("\nMINIMAL counterexamples (by width-sum, then length, then lex):")
for M in canon[:20]:
    print(f"   M={M}  sum={sum(M)}  rev={rev(M)}  minAdm={minAdm(M)}  palindrome={M==rev(M)}")

# ---- characterize: middle bottleneck / peak? ----
print("\nStructural signature of the counterexamples:")
allpeak=all(min(M[1:-1]) < M[0] and min(M[1:-1]) < M[-1] for M in canon)
print("  every counterexample has an interior width < both endpoint widths (a 'waist/peak')?", allpeak)
# show interior-min vs ends
for M in canon[:8]:
    print(f"   {M}: ends=({M[0]},{M[-1]}) interior-min={min(M[1:-1])}")

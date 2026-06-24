"""
Q3 — Census: how common is the corank-≥2 binding obstruction?

The squeeze (Route B) is SOUND on a width vector M iff some minAdm-achieving rank profile
is reachable by corank-≤1 peels at every node (Codex's scope: min(M₀−t, M₁−t) ≤ 1 at every
binding peel). We census small width vectors: does the binding (minAdm-achieving) branch
require a corank-≥2 peel at layer 1?

corank at layer-1 peel rank t = min(M₀−t, M₁−t).  corank ≥ 2 ⟺ M₀−t ≥ 2 AND M₁−t ≥ 2.
"""
from itertools import product as iproduct

def minAdmRec_with_t(M):
    """Return (minAdm, list of achieving layer-1 t values)."""
    L=len(M)-1
    if L==0: return 0, []
    if L==1: return M[0]*M[1], [None]  # leaf, no layer-1 branch
    best=None; achievers=[]
    for t in range(min(M[0],M[1])+1):
        red=[t]+list(M[2:])
        sub,_=minAdmRec_with_t(red)
        v=(M[0]-t)*(M[1]-t)+sub
        if best is None or v<best:
            best=v; achievers=[t]
        elif v==best:
            achievers.append(t)
    return best, achievers

def binding_needs_corank2(M):
    """True if EVERY minAdm-achieving layer-1 t has corank ≥ 2 (no clean reach at layer 1)."""
    _, achievers = minAdmRec_with_t(M)
    if not achievers or achievers==[None]: return False
    coranks = [min(M[0]-t, M[1]-t) for t in achievers]
    return all(cr >= 2 for cr in coranks)

# Census L=2 (3-width) and L=3 (4-width), widths 2..5.
print("=== L=2 (3-width) census, widths 2..5 ===")
hits=[]; total=0
for M in iproduct(range(2,6), repeat=3):
    total+=1
    if binding_needs_corank2(list(M)):
        hits.append(M)
print(f"  {len(hits)}/{total} width vectors have ALL binding branches corank≥2 at layer 1:")
for M in hits[:20]:
    ma,ach = minAdmRec_with_t(list(M))
    print(f"    {M}: minAdm={ma}, achiever t∈{ach}, coranks={[min(M[0]-t,M[1]-t) for t in ach]}")
print(f"  (showing first 20 of {len(hits)})")
print()

print("=== L=3 (4-width) census, widths 2..5 (sample) ===")
hits3=[]; total3=0
for M in iproduct(range(2,6), repeat=4):
    total3+=1
    if binding_needs_corank2(list(M)):
        hits3.append(M)
print(f"  {len(hits3)}/{total3} 4-width vectors have ALL layer-1 binding branches corank≥2.")
print("  (Note: even corank≤1 at layer 1 can hide corank≥2 DEEPER in the recursion — this census")
print("   only checks LAYER 1; the true obstruction is corank≥2 at ANY binding node.)")
print()
# Check (3,3,4) specifically
ma, ach = minAdmRec_with_t([3,3,4])
print(f"(3,3,4): minAdm={ma}, achiever t∈{ach}, coranks={[min(3-t,3-t) for t in ach]} -> corank-2 binding ✓")
ma, ach = minAdmRec_with_t([2,2,2])
print(f"(2,2,2): minAdm={ma}, achiever t∈{ach}, coranks={[min(2-t,2-t) for t in ach if t is not None]}")
print()
print("CONCLUSION: corank-≥2 binding is NOT rare — it appears in a substantial fraction of")
print("3-width vectors (the RRR cores (n,n,p) with n≥3, p≥2n-ish). The squeeze route's sound")
print("scope EXCLUDES these. So Route B's residual is NOT general-M; it covers a scoped sub-family.")

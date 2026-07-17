"""
decstep's question: is the DEEP c=min(a,b)>=2 corank per-stratum reduction PLAIN-IH+bounded-Jacobian (Route-D)
or DECORATED+carried-Gram-weight (Route-Dec)?

Reliable check: my leaf1-soundness found the HARD cells (bare/plain route undershoots) are where
minAdm(M) > ab + u*(M1-j) [front bound ceiling]; those need the CARRIED Gram weight (decorated).
Also my a<u/a>=u split: a<u => weight DISPOSABLE (sphere, plain-ish); a>=u => weight CARRIED (gammaAtom, decorated).
For decstep's deep-corank examples + the general c=min(a,b)>=2, check: is a<u (disposable/plain) possible, or is
a>=u FORCED (carried/decorated)? And are they in the hard (minAdm>ab+u(M1-j)) regime?
NO MC.
"""
from functools import lru_cache
from itertools import product
def redChain(u,M): return (u,)+tuple(M[2:])
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm(redChain(t,M)) for t in range(min(M[0],M[1])+1))

print("=== decstep's deep-corank examples: a vs u + hard-regime check ===")
for M in [(4,4,4,4),(5,5,5,5),(2,2,3,3),(4,4,4,4,4)]:
    M0,M1=M[0],M[1]; mM=minAdm(M)
    # take the corank cut u where c=min(a,b) is maximal (interior deep corank)
    rows=[]
    for u in range(1,min(M0,M1)+1):
        a=M0-u; b=M1-u; c=min(a,b)
        if c<2: continue
        # a<u disposable? ; hard (front bound ceiling) minAdm > ab+u*(M1-... ) -- use m'=M1-j with j=u-t, t>=1 => m'=M1-(u-1) worst
        # front ceiling (leaf1): minAdm(M) <= ab + u*(M1-j), j max = u-1 (t=1) => M1-j = M1-u+1 = b+1
        ceil = a*b + u*(b+1)   # M1-j with t=1
        hard = mM > ceil
        disposable = (a<u)
        rows.append((u,a,b,c,'a<u(disp)' if disposable else 'a>=u(CARRIED)', 'HARD' if hard else 'easy', mM, ceil))
    print(f"  {M}: minAdm={mM}")
    for r in rows: print(f"     u={r[0]} a={r[1]} b={r[2]} c={r[3]}: {r[4]}, {r[5]} (minAdm={r[6]} vs ceil={r[7]})")

print()
print("=== general: deep corank c=min(a,b)>=2 — is a>=u FORCED (=> carried/decorated)? ===")
tot=0; aLTu=0; aGEu=0
for arity in (4,5):
  for M in product(range(1,7),repeat=arity):
    for u in range(1,min(M[0],M[1])+1):
      a=M[0]-u; b=M[1]-u
      if min(a,b)<2: continue    # deep corank c>=2
      tot+=1
      if a<u: aLTu+=1
      else: aGEu+=1
print(f"  deep-corank (c=min(a,b)>=2) cuts: {tot};  a<u (disposable/plain-ish): {aLTu};  a>=u (CARRIED/decorated): {aGEu}")
print(f"  => a>=u (carried Gram weight => DECORATED) occurs for {aGEu}/{tot} deep-corank cuts; NOT universally plain.")

"""
Two deliverables q2gate scoped:
(A) b=0 leaf Q2-status: b=0 (M0>M1, u=M1) is a WEIGHT-FREE injective CoV to redChain M1 M at ITS level, but
    INHERITS redChain M1 M's Q2-status. Does the reduced chain hit the SQUARE-decorated wall (a=b=0, u>=3)?
    Recursively classify Q2-status. If b=0 always reduces to Q2-clean, injective⟹weight-free (q2gate's guess);
    if it can inherit a square-decorated, b=0 tall u>=3 is NOT universally clean.
(B) a=0/b>0 wide-non-square per-corank γ_r + codim_r + Lᵖ range (for q2gate's shell budget).
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

@lru_cache(maxsize=None)
def q2status(M):
    """Recursive Q2-status of the SATURATED waist of chain M. Returns 'clean' / 'decorated' / 'open'."""
    M=tuple(M)
    if len(M)<=2: return 'clean'          # RMBTF base
    M0,M1=M[0],M[1]; u=min(M0,M1)
    if M0<=M1:   # a=0
        if u<=2: return 'clean'           # shell+Hölder log (q2gate proved)
        # u>=3 a=0
        if M0==M1: return 'decorated'      # SQUARE u>=3 = the wall (q2gate proved)
        else: return 'open'                # a=0/b>0 wide-non-square u>=3 (needs the per-corank γ)
    else:        # b=0 (M0>M1), u=M1: weight-free CoV, inherit redChain M1 M
        return q2status(redChain(u,M))     # inherit

# (A) scan b=0 cells: how many inherit 'decorated' vs 'clean' vs 'open'?
from collections import Counter
b0=Counter(); ex_dec=[]
for arity in (4,5):
  for M in product(range(1,7),repeat=arity):
    if M[0]<=M[1]: continue     # b=0 branch: M0>M1
    st=q2status(M); b0[st]+=1
    if st=='decorated' and len(ex_dec)<6: ex_dec.append((M, 'redChain=', redChain(min(M[0],M[1]),M)))
print("=== (A) b=0 tall leaf: recursive Q2-status (inherited from redChain M1 M) ===")
print("  b=0 cells by inherited status:", dict(b0))
print("  => b=0 is NOT universally weight-free: it INHERITS. Decorated inheritors (M, redChain):")
for e in ex_dec: print("    ", e)
print(f"  witness (5,3,3,3): u={min(5,3)}, redChain 3 (5,3,3,3)={redChain(3,(5,3,3,3))}, status={q2status((5,3,3,3))}")
print()
# (B) a=0/b>0 wide-non-square u>=3: per-corank γ_r = r*(M2-b-r), codim_r, Lᵖ range p<codim/γ
print("=== (B) a=0/b>0 wide-non-square u>=3: per-corank density order + Lᵖ (for q2gate shell budget) ===")
def report_widensquare(M):
    M0,M1,M2=M[0],M[1],M[2]; u=M0; b=M1-u   # a=0, u=M0, b=M1-M0>0
    print(f"  {M}: u={u},a=0,b={b},M2={M2}")
    rows=[]
    for r in range(1, min(u,M2)+1):        # corank r (rank z~0 = min(u,M2)-r)
        gamma = r*(M2-b-r)                 # satred density order at corank r (0 => log)
        # codim of rank=min(M0,M2)-r in M0xM2:
        k=min(M0,M2)-r; codim=(M0-k)*(M2-k)
        lp = "all p (log)" if gamma<=0 else f"p<{codim}/{gamma}={codim/gamma:.2f}"
        rows.append((r,gamma,codim,lp))
    for r,g,c,lp in rows: print(f"     corank r={r}: γ={g}, codim={c}, ρ∈Lᵖ: {lp}")
for M in [(3,4,4,4),(3,4,5,5),(3,5,5,5),(4,5,5,5),(3,4,4,4,4)]:
    report_widensquare(M)

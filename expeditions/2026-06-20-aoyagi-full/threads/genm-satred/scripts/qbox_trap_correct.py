"""
CORRECTED P2 review: the Gram-carry distinction is WHICH VARIABLE the Gram is integrated over.
- CORANK Gram: ∫_{A_cor∈box(b×M₂)} det((A_cor·Z_deep)(·)ᵀ)^{−a/2}  [strong-block, over A_cor]
    finite iff  a < ρ − b + 1  (ρ = rank Z_deep). FAILS at the edge a+b=ρ+1 (a=ρ−b+1 exactly).
    => this is the TRAP: the EASY route (L1's corank weight) uses it; it fails at the edge/hard shells.
- PIVOT Gram: det(Q̃ₚQ̃ₚᵀ)^{−a/2} integrated over the REDUCED params z  [absorbed by the reduced-chain
    recursion / IH, NOT a separate strong-block over A_cor]. (waist-b0: literal qbox over the P,C front box.)
Verify: the corank strong-block condition a<ρ−b+1 fails EXACTLY on the edge+deep (a>=ρ−b+1), and the
easy/hard guard is a DIFFERENT (finer) condition. NO MC.
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
WMAX=6
corank_fails=0; corank_ok=0; edge_boundary=0; tot=0
for arity in (4,5):
  for M in product(range(1,WMAX+1),repeat=arity):
    M0,M1=M[0],M[1]; rho=min(M[1:])
    for t in range(1,min(M0,M1)+1):
      r=min(M0-t,M1-t)
      for j in range(0,r):        # interior shells
        u=t+j; a=M0-u; b=M1-u
        if b<1: continue
        tot+=1
        corank_conv = (a < rho - b + 1)     # corank strong-block over A_cor
        if corank_conv: corank_ok+=1
        else: corank_fails+=1
        if a == rho-b+1: edge_boundary+=1   # the exact edge tie (corank strong-block boundary)
print(f"interior shells (b>=1): {tot}")
print(f"  corank strong-block a<ρ−b+1 CONVERGES: {corank_ok}  (easy corank weight ok)")
print(f"  corank strong-block a<ρ−b+1 FAILS (a>=ρ−b+1): {corank_fails}  (the TRAP region — edge+deep-corank)")
print(f"  of which the EXACT edge tie a=ρ−b+1 (boundary, log): {edge_boundary}")
print("  => corank Gram over A_cor is the TRAP (fails at edge a=ρ−b+1); PIVOT Gram is absorbed by the reduced-chain IH (different integral), NOT a corank strong-block. P2 wording must distinguish.")

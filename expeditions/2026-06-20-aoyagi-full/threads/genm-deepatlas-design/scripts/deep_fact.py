"""
Verify the factorization-chart mechanism + Jacobian for the deep resolution.
Mechanism (peel last layer): on {rank L_last = r}, factor L_last = A·B (A: full col rank r, B: full row rank r).
Then rank(head·L_last) = rank(head·A). Reduce chain last width -> r.
"""
import numpy as np
from fractions import Fraction
np.random.seed(0)

def rank_np(A, tol=1e-9):
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False)
    return int((s>tol*max(1.0,s[0])).sum()) if s.size else 0

# --- Q2: rank(head·L_last) = rank(head·A) when L_last = A·B, B full row rank ---
print("=== Q2: rank(head·L_last)=rank(head·A) for L_last=A·B (B full row rank) ===")
bad=0
for trial in range(2000):
    v = [np.random.randint(1,6) for _ in range(4)]  # v0 v1 v2 v3, p=3
    L=[np.random.randn(v[i],v[i+1]) for i in range(3)]
    head = L[0]@L[1]   # v0 x v2
    Llast = L[2]       # v2 x v3
    r = rank_np(Llast)
    U,S,Vt = np.linalg.svd(Llast, full_matrices=False)
    A = U[:,:r]*S[:r]  # v2 x r  (col space)
    B = Vt[:r,:]       # r x v3, full row rank
    assert np.allclose(A@B, Llast)
    if rank_np(head@Llast) != rank_np(head@A): bad+=1
print("mismatches:", bad)

# --- Q3: Jacobian of the pivoted factorization of a v1xv2 matrix at generic rank r=min(v1,v2) ---
# On chart {top-left rxr minor Δ invertible}, generic full-rank layer L=[[Δ,B12],[B21,B22]].
# Chart-5 says: coordinatize by (Δ,B12,B21,E), E=B22-B21 Δ^{-1} B12, Jacobian≡1, and {rank L<=r}={E=0}.
# For a layer at its GENERIC rank r=min(v1,v2): if v1<=v2, r=v1, the "E block" is empty (no rows below Δ pivot in the v1 dir)
#   -> chart is just the linear open chart, Jacobian 1, no transverse condition.
# Confirm: for r=min(v1,v2), the transverse Schur block E has size (v1-r)x(v2-r); one factor is 0 -> empty.
print("\n=== Q3: at generic rank r=min(v1,v2), transverse Schur block is EMPTY ===")
for v1 in range(1,6):
  for v2 in range(1,6):
    r=min(v1,v2)
    print(f"  layer {v1}x{v2}: r={r}, E-block size ({v1-r})x({v2-r}) -> dim {(v1-r)*(v2-r)}")

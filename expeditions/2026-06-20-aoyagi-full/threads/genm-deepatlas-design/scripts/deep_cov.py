"""
Verify the reduction CoV: on chart {Δ = top-left r×r minor of L_last invertible},
- A := pivot columns [Δ; C] of L_last (v_{p-1} × r).
- Completion G := [[Δ,0],[C,I]] (v_{p-1}×v_{p-1}), det G = det Δ.
- CoV on L_{prev} (v_{p-2}×v_{p-1}): L_prev ↦ L_prev·G, Jacobian |det Δ|^{v_{p-2}},
  image splits (L_prev·A , L_prev^2) where L_prev^2 = last (v_{p-1}-r) cols.
- On {E=0} (E=D-CΔ⁻¹B=0): rank(head·L_last) = rank(head·A) = rank(head'·(L_prev·A)) with head'=L_0..L_{p-3}.
"""
import numpy as np
np.random.seed(1)
def rank_np(A,tol=1e-9):
    if A.size==0: return 0
    s=np.linalg.svd(A,compute_uv=False); return int((s>tol*max(1.0,s[0])).sum()) if s.size else 0

print("=== CoV Jacobian: L_prev ↦ L_prev·G, |Jac| = |det Δ|^{v_prev_rows} ===")
bad=0
for _ in range(500):
    vpm2=np.random.randint(1,5); vpm1=np.random.randint(1,5); r=np.random.randint(1,vpm1+1)
    # build G=[[Δ,0],[C,I]], Δ r×r invertible
    Δ=np.random.randn(r,r)
    while abs(np.linalg.det(Δ))<1e-3: Δ=np.random.randn(r,r)
    C=np.random.randn(vpm1-r,r)
    G=np.block([[Δ,np.zeros((r,vpm1-r))],[C,np.eye(vpm1-r)]])
    # Jacobian of L ↦ L·G on v_prev×v_{p-1} space = det(G)^{v_prev} (build linear map matrix)
    n=vpm2*vpm1
    Jm=np.zeros((n,n))
    E=np.zeros((vpm2,vpm1))
    for i in range(vpm2):
        for j in range(vpm1):
            E[:]=0; E[i,j]=1; out=(E@G).flatten(); Jm[:,i*vpm1+j]=out
    jac=abs(np.linalg.det(Jm)); pred=abs(np.linalg.det(Δ))**vpm2
    if not np.isclose(jac,pred,rtol=1e-6): bad+=1
print("  Jacobian mismatches:", bad, " (expected 0)")

print("\n=== reduction: on {E=0}, rank Z unchanged under reduction to (head', L_prev·A) ===")
bad2=0
for _ in range(800):
    v=[np.random.randint(1,5) for _ in range(4)]  # v0 v1 v2 v3 (p=3)
    L=[np.random.randn(v[i],v[i+1]) for i in range(3)]
    Llast=L[2]; vpm1,vp=v[2],v[3]; r=rank_np(Llast)
    if r==0 or r>min(vpm1,vp): continue
    # find invertible r×r minor (use SVD-based col/row pivot); simpler: use first r cols as A when full-col-rank
    U,S,Vt=np.linalg.svd(Llast,full_matrices=False)
    A=U[:,:r]*S[:r]           # v2×r, col space (this is the "pivot columns" analog)
    Z=L[0]@L[1]@L[2]
    head=L[0]@L[1]            # v0×v2
    Zred=head@A               # v0×r
    if rank_np(Z)!=rank_np(Zred): bad2+=1
print("  rank(Z) != rank(head·A) mismatches:", bad2, " (expected 0)")

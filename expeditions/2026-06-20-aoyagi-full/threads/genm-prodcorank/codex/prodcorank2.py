from fractions import Fraction as F
import numpy as np, itertools

def Ck(k): return k*k - (k*k)//4

# TRUE codim of {rank(PZ) <= n-k}: minimize over components.
# Component (a,c,e): rank(P)=n-a, rank(Z)=n-c, dim(im Z ∩ ker P)=e, giving rank(PZ)=(n-c)-e <= n-k => e>=k-c.
#   codim = a^2 (rank P) + c^2 (rank Z) + e*(c - a + e) (Schubert: dim(U∩V)>=e, U=ker P dim a, V=im Z dim n-c)
#   constraints: 0<=a,c<=n; e=max(0,k-c) minimal to reach; e<=a, e<=n-c; also need e>= k-c AND (n-c)-e>=0 target rank>=0
def true_codim(n,k):
    best=None
    for a in range(0,n+1):
        for c in range(0,n+1):
            e = k - c
            if e < 0: e = 0
            # need rank(PZ)=(n-c)-e <= n-k  => e >= k-c (ok). Feasibility of Schubert:
            if e> a: continue
            if e> n-c: continue
            if (n-c)-e < 0: continue
            # also rank(P)=n-a>=0, rank(Z)=n-c>=0 ok
            codim = a*a + c*c + e*(c - a + e)
            if codim<0: continue
            if best is None or codim<best: best=codim; barg=(a,c,e)
    return best,barg

print("=== TRUE product-corank codim (balanced Schubert component) ===")
allok=True
for n in range(2,9):
    for k in range(1,n+1):
        tc,arg=true_codim(n,k)
        ok = (tc==Ck(k))
        allok &= ok
        print(f"  n={n} k={k}: true codim={tc} at (a,c,e)={arg}, C_k={Ck(k)}, match={ok}")
print("ALL MATCH C_k:", allok)

# Numerical cross-check via generic Jacobian rank at a smooth point of the balanced component (n=4,k=2).
# Build P,Z on the component a=c=1,e=1: rank(P)=3, rank(Z)=3, im Z ∩ ker P has dim 1, so rank(PZ)=3-1=2=n-k. good.
print("\n=== numerical Jacobian-rank codim check, n=4,k=2 (expect codim 3) ===")
np.random.seed(0)
n=4; k=2
# construct a point: ker P = span(e1). im Z = span(e1,e2,e3) (so e1 in ker P ∩ im Z). rank P=3, rank Z=3.
# P: 4x4 rank 3 with ker = e1  -> columns: col1=0, others random
# Z: 4x4 rank 3 with image = span(e1,e2,e3): rows 1..3 random, row4 = combo? image=col space. Make col space = <e1,e2,e3>: last coordinate of every column =0.
def build_point():
    P=np.random.randn(4,4); P[:,0]=0.0   # ker contains e1
    Z=np.random.randn(4,4); Z[3,:]=0.0   # im Z ⊆ <e1,e2,e3>
    return P,Z
P0,Z0=build_point()
PZ=P0@Z0
print("rank(P0),rank(Z0),rank(PZ):",np.linalg.matrix_rank(P0),np.linalg.matrix_rank(Z0),np.linalg.matrix_rank(PZ))
# codim via: dimension of the variety near this point = 32 - rank of Jacobian of the (k x k)-minors defining rank<=2? 
# Instead estimate dim of the variety as dim of tangent to the stratum {rank(PZ)=2}. 
# The stratum {rank(M)=2} in Mat4 has codim (4-2)^2=4; pull back tangent condition: T = {(dP,dZ): d(PZ) ∈ T_PZ(rank<=2)}.
# T_M(rank<=r) = {X: U2^T X V2 =0} where U2,V2 span cokernel/kernel (dim (n-r) each). codim of that linear condition on d(PZ)=dP·Z+P·dZ.
U,S,Vt=np.linalg.svd(PZ)
r=2
Ucok=U[:,r:]   # 4x2 left null
Vker=Vt[r:,:].T # 4x2 right null
# linear map (dP,dZ) -> Ucok^T (dP Z + P dZ) Vker  in R^{2x2}=4 dims. codim of variety = rank of this linear map.
import numpy as np
def vecmap():
    rows=[]
    for i in range(4):
      for j in range(4):
        dP=np.zeros((4,4)); dP[i,j]=1
        val=Ucok.T@(dP@Z0)@Vker
        rows.append(val.flatten())
    for i in range(4):
      for j in range(4):
        dZ=np.zeros((4,4)); dZ[i,j]=1
        val=Ucok.T@(P0@dZ)@Vker
        rows.append(val.flatten())
    return np.array(rows)
Jm=vecmap()  # 32 x 4
codim_local = np.linalg.matrix_rank(Jm, tol=1e-9)
print("local codim (rank of normal map) at balanced point:", codim_local, "(expect 3 => C_2=3)")

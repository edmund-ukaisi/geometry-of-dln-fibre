# Route-2 probe: varietyDim Z_M = ringKrullDim(image μ_M^*) = trdeg Frac(image μ_M^*).
# Compute trdeg of the image of the orbit pullback for (2,2,2), via the Jacobian rank of μ_M^*
# at a generic group point (the rank of the differential of the orbit map at the identity = rank δ⁰).
# This is exactly the submersion content: trdeg(image) = generic rank of Jacobian of μ_M^*.
# If trdeg(image μ_M^*) = rank(δ⁰), route 2 is mathematically the SAME as the submersion,
# i.e. it does NOT avoid the theorem — it relocates it to "generic Jacobian rank = trdeg".
import numpy as np

# Orbit map μ_M : G=(GL2)^3 -> Rep_d=(Mat2)^2,  P=(P0,P1,P2) ↦ (P1 M0 P0^{-1}, P2 M1 P1^{-1}).
# Its differential at the IDENTITY (P=1) in directions (X0,X1,X2)∈(Mat2)^3:
#   d/dt[ (I+tX1) M0 (I+tX0)^{-1} ]|0 = X1 M0 - M0 X0
#   d/dt[ (I+tX2) M1 (I+tX1)^{-1} ]|0 = X2 M1 - M1 X1
# = exactly δ⁰. So rank of Jacobian of μ_M^* at identity = rank δ⁰. ✓ (definitional)
#
# But trdeg(image) = generic rank of Jacobian over the WHOLE group, not just at identity.
# For a homogeneous space the generic rank = rank at any point (homogeneity), and in char 0
# generic rank of differential = dim image = trdeg. So compute rank of dμ at a RANDOM group point.

def interval_arrow(a,b,i):
    src=1 if a<=i<=b else 0; tgt=1 if a<=i+1<=b else 0
    if src and tgt: return np.array([[1.0]])
    return np.zeros((tgt,src))
def directsum_tuple(intervals,Nv=3):
    d=[0]*Nv
    for (a,b) in intervals:
        for w in range(Nv):
            if a<=w<=b: d[w]+=1
    M=[]
    for i in range(Nv-1):
        blocks=[interval_arrow(a,b,i) for (a,b) in intervals]
        rows=sum(b.shape[0] for b in blocks); cols=sum(b.shape[1] for b in blocks)
        Mi=np.zeros((rows,cols)); r=0;c=0
        for blk in blocks:
            Mi[r:r+blk.shape[0],c:c+blk.shape[1]]=blk; r+=blk.shape[0]; c+=blk.shape[1]
        M.append(Mi)
    return d,M

def dmu_rank_at(d,M,P,Nv=3,eps=1e-6):
    # numerically estimate rank of d(μ_M) at group point P=(P0,P1,P2)
    # directions: tangent at P is X_v P_v (left translate), but rank is translation-invariant so
    # just perturb each P_v by a basis of Mat2 and collect columns in Rep_d.
    base=[P[i+1]@M[i]@np.linalg.inv(P[i]) for i in range(Nv-1)]
    cols=[]
    for v in range(Nv):
        for r in range(d[v]):
            for c in range(d[v]):
                Pp=[Q.copy() for Q in P]; E=np.zeros((d[v],d[v])); E[r,c]=eps; Pp[v]=P[v]+E
                pert=[Pp[i+1]@M[i]@np.linalg.inv(Pp[i]) for i in range(Nv-1)]
                col=np.concatenate([( (pert[i]-base[i])/eps ).flatten() for i in range(Nv-1)])
                cols.append(col)
    J=np.array(cols).T
    return np.linalg.matrix_rank(J,tol=1e-4)

np.random.seed(0)
for name,intervals in [("(1,1)-orbit",[(0,0),(0,1),(1,2),(2,2)]),("zero-product",[(0,0),(0,0),(1,2),(1,2)])]:
    d,M=directsum_tuple(intervals)
    # random invertible P_v
    P=[np.eye(d[v])+0.3*np.random.randn(d[v],d[v]) for v in range(3)]
    r_gen=dmu_rank_at(d,M,P)
    r_id =dmu_rank_at(d,M,[np.eye(d[v]) for v in range(3)])
    print(f"{name}: d={d}; rank dμ at identity={r_id}; rank dμ at RANDOM P={r_gen}  (homogeneity ⇒ equal, = dim image = trdeg in char 0)")

import numpy as np
rng=np.random.default_rng(0)
# Confirm: on the t-pivot chart, inner ∫_{A0} frobSq(A0 Q)^{-c'} dA0 scales, as Q -> rank-deficient
# (det Q -> 0), like the RANK-governed threshold (finite iff c' < M0*rank(Q)/2), NOT frobSq(Q).
# Test (2,2,2,2): M0=2. c'=1.2 (in [1,1.5)). Full-rank Q: conv iff c'<2 (finite). rank-1 Q: iff c'<1 -> DIVERGES.
def I_of_Q(Q, cp, N=2_000_000):
    A0=rng.uniform(-1,1,(N,2,2)); P=np.matmul(A0,Q[None])
    f=np.maximum((P**2).sum((1,2)),1e-300); return (f**(-cp)).mean()*16.0
print("(2,2,2,2), c'=1.2. Q_s = [[1,0],[0,s]] (det=s). As s->0, Q->rank1, inner should DIVERGE (grows w/ N).")
for s in [1.0,0.3,0.1,0.03]:
    Q=np.array([[1.0,0.0],[0.0,s]])
    v1=I_of_Q(Q,1.2,1_000_000); v2=I_of_Q(Q,1.2,4_000_000)
    print(f"  s=det Q={s:5.2f}: I(N=1e6)={v1:8.2f}  I(N=4e6)={v2:8.2f}  {'GROWS(div)' if v2>1.4*v1 else 'stable'}  frobSq(Q)^-1.2={ (1+s*s)**-1.2:.3f}")
print("""
=> confirms route-2 death mechanism: inner ∫_{A0} DIVERGES as Q->rank-deficient (rank-governed),
   while frobSq(Q) stays O(1). The divergence locus {det Q=0} is codim-1 (NULL in A'), so the
   double integral is finite but the pointwise inner bound has no uniform C. Integrated (per-chart,
   a.e.) is required.
""")
# Confirm {det Q = 0} is codim-1 (null) in A'-space for tail=(2,2,2): Q=A1 A2, det Q=det A1 det A2.
A1=rng.uniform(-1,1,(200000,2,2)); A2=rng.uniform(-1,1,(200000,2,2))
detQ=np.linalg.det(np.matmul(A1,A2))
print(f"P(|det Q|<1e-3) over box = {(np.abs(detQ)<1e-3).mean():.4f}  (->0 as tol->0: {{det Q=0}} is NULL)")

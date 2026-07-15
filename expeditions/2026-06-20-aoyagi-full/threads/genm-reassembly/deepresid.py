import numpy as np
rng=np.random.default_rng(3)
# Test integrability of the residual det+(Z Z^T)^{-b/2} over deep params (Z = A2, single deep layer, M2 x n).
# Criterion (Wishart / determinantal lct): ∫_{A2 in box} det(A2^T A2)^{-s} dA2 < ∞  iff  s < (M2col_free)/2 ...
# For A2 : p x q (p rows, q cols), G+ = det(A2^T A2) (q x q, needs p>=q). ∫ det(A2^T A2)^{-s} < ∞ iff s < (p-q+1)/2.
# Here Z=A2 is M2 x n; det+(Z Z^T)=det(A2^T A2) (n x n) needs M2>=n; threshold s* = (M2 - n + 1)/2.
# residual exponent s = b/2.  So residual integrable iff b/2 < (M2-n+1)/2 iff b < M2-n+1 iff b + n <= M2.
def test(M2,n,b,N=3_000_000):
    A2=rng.standard_normal((N,M2,n))
    G=np.transpose(A2,(0,2,1))@A2
    dg=np.linalg.det(G)                 # det(A2^T A2)
    s=b/2.0
    # integral over box ~ E over gaussian of dg^{-s} * (gaussian weight)... use finite-cutoff estimator:
    # near-zero-det scaling: estimate P(dg<eps) ~ eps^{lam}; integrable iff s<lam.
    eps=np.array([0.5,0.1,0.02,0.004])
    P=np.array([np.mean(dg<e) for e in eps])
    lg=np.log(eps); lp=np.log(P+1e-30)
    sl=(lp[1:]-lp[:-1])/(lg[1:]-lg[:-1])
    thr=(M2-n+1)/2.0
    print(f"M2={M2} n={n} b={b}: s=b/2={s}, predicted threshold (M2-n+1)/2={thr}, small-det scaling slopes={np.round(sl,3)} -> integrable={s<thr}")
print("Residual det+(Z Z^T)^{-b/2} integrability over deep params (Z=A2, M2 x n):")
# case M=(3,3,4,3): M2=4,n=3,b=1
test(4,3,1)
# case M=(3,4,5,4): M2=5,n=4,b=2
test(5,4,2)
# case M=(3,4,5,4) but b=1 hypothetically
test(5,4,1)
# case M=(4,5,6,4): M2=6,n=4,b=2  (more room)
test(6,4,2)
print()
print("Rule: residual integrable over deep iff  b + n <= M2  (n=M_last, M2=second width).")

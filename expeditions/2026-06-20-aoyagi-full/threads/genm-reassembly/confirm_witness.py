import numpy as np
rng=np.random.default_rng(7)
# Confirm the deep-Gram residual det+(Z Z^T)^{-b/2} DIVERGES over the deep layer A2 for the witnesses.
# Estimator: V(eps)=E_gauss[ det+(ZZ^T)^{-b/2} * 1(det+ > eps) ] should CONVERGE as eps->0 iff integrable.
# Equivalently truncated integral T(eps)=E[ det+^{-b/2} 1(det+>eps) ]; if it grows without bound as eps->0, divergent.
def detplus(A2):
    p,q=A2.shape[-2],A2.shape[-1]
    if p>=q: return np.linalg.det(np.transpose(A2,(0,2,1))@A2)   # det(A2^T A2)
    else:    return np.linalg.det(A2@np.transpose(A2,(0,2,1)))   # det(A2 A2^T)
def truncated(M2,M3,b,N=4_000_000):
    A2=rng.standard_normal((N,M2,M3))
    dp=detplus(A2)
    dp=np.abs(dp)
    w=dp**(-b/2.0)
    Ts=[]
    for eps in [1e-1,1e-2,1e-3,1e-4,1e-5]:
        Ts.append(np.mean(np.where(dp>eps,w,0.0)))
    thr=(abs(M2-M3)+1)/2.0   # RLCT of det+   ; integrable iff b/2<thr iff b<=|M2-M3|
    return Ts,thr
for (M2,M3,b,name) in [(4,3,1,"(3,3,4,3) safe boundary"),(4,4,1,"(4,4,4,4) uniform b=1"),(5,4,2,"(3,4,5,4) b=2"),(5,5,1,"(5,5,5,5) uniform b=1"),(6,4,2,"(4,5,6,4)? b=2 room")]:
    Ts,thr=truncated(M2,M3,b)
    growing = Ts[-1] > 3*Ts[0]
    print(f"{name:26} M2={M2},M3={M3},b={b}: b/2={b/2}, RLCT(det+)={thr}, integrable={b/2<thr}")
    print(f"    truncated ∫ at eps=1e-1..1e-5: {np.round(Ts,4)}   ({'GROWING->divergent' if growing else 'stable->convergent'})")

import numpy as np
# RLCT via sublevel-set volume:  Vol{loss<eps} ~ eps^lambda  =>  int loss^{-c'} finite iff c'<lambda.
# This MC is RELIABLE (bounded indicator, not singular integrand).
rng=np.random.default_rng(1)

def rlct_from_volume(loss_fn, dim_sampler, box_vol, eps_list=None, N=8_000_000):
    if eps_list is None: eps_list=np.array([2**-k for k in range(2,16)])
    V=[]
    for eps in eps_list:
        s=dim_sampler(N)
        L=loss_fn(*s)
        V.append(np.mean(L<eps)*box_vol)
    V=np.array(V)
    # fit slope on the small-eps tail where log-log is linear
    mask=(V>0)
    le=np.log(eps_list[mask]); lv=np.log(V[mask])
    # use last ~7 points (smallest eps) for asymptotic slope
    k=min(7,mask.sum())
    slope=np.polyfit(le[-k:],lv[-k:],1)[0]
    return slope, list(zip([float(e) for e in eps_list],[float(v) for v in V]))

# ---- (2,2,3) full local model, alpha1 ~ 1 (in-plane part floored), all test vars + t in a box ----
# loss = (P+a1 B)^2 + (C+a1 Gp)^2 + (B^2+Gp^2)(t2^2+t3^2)
L=1.0
def samp_223(N):
    P=rng.uniform(-L,L,N); C=rng.uniform(-L,L,N); B=rng.uniform(-L,L,N); Gp=rng.uniform(-L,L,N)
    a1=rng.uniform(0.8,1.2,N); t2=rng.uniform(-L,L,N); t3=rng.uniform(-L,L,N)
    return (P,C,B,Gp,a1,t2,t3)
def loss_223(P,C,B,Gp,a1,t2,t3):
    return (P+a1*B)**2+(C+a1*Gp)**2+(B**2+Gp**2)*(t2**2+t3**2)
boxvol=(2*L)**6*0.4
lam,tab=rlct_from_volume(loss_223, samp_223, boxvol)
print("(2,2,3) full local model  lambda(RLCT) =",round(lam,3),"   [my branch analysis: 2 ; Codex pivot: 3/2]")
for e,v in tab[-8:]: print(f"    eps={e:.2e}  Vol={v:.3e}")

# ---- Pivot block ALONE (Codex's object): int_{P,B} ||[P|B] hsQ||^{-2c''}, hsQ=[[1,0,0],[a1,t2,t3]], t FIXED generic ----
# loss_pivot = (P+a1 B)^2 + B^2*(t2^2+t3^2), t fixed != 0 -> rank-2 quadratic in (P,B): lambda=1 => c''<1.
def samp_piv(N):
    P=rng.uniform(-L,L,N); B=rng.uniform(-L,L,N); return (P,B)
a1f,tf=1.0,0.5
def loss_piv(P,B): return (P+a1f*B)**2+B**2*(tf**2)
lam_piv,_=rlct_from_volume(loss_piv, samp_piv, (2*L)**2)
print("pivot block alone (t fixed=0.5)  lambda =",round(lam_piv,3),"  [rank-2 => 1]")

# ---- Pivot block WITH t integrated (t2,t3 in box, B,P in box) : is THIS the coupled object? ----
def samp_pivt(N):
    P=rng.uniform(-L,L,N); B=rng.uniform(-L,L,N); t2=rng.uniform(-L,L,N); t3=rng.uniform(-L,L,N); return (P,B,t2,t3)
def loss_pivt(P,B,t2,t3): return (P+a1f*B)**2+B**2*(t2**2+t3**2)
lam_pivt,_=rlct_from_volume(loss_pivt, samp_pivt, (2*L)**4)
print("pivot block + t integrated  lambda =",round(lam_pivt,3))

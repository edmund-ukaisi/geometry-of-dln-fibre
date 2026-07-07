import numpy as np
rng = np.random.default_rng(7)
def rpow(x,s): return (1.0 if s==0.0 else 0.0) if x==0.0 else x**s
def F_of_Q(Q,cp,M0,M1,nMC=400000):
    A0=rng.uniform(-1,1,size=(nMC,M0,M1)); P=np.einsum('nij,jk->nik',A0,Q)
    fs=np.sum(P**2,axis=(1,2)); fs=np.where(fs>1e-300,fs,np.nan)
    return np.nanmean(fs**(-cp))*(2.0**(M0*M1))
def rhs_of_Q(Q,cp,M0,M1):
    Pfull=np.sum(Q**2); s=0.0
    for t in range(0,min(M0,M1)+1):
        a=(M0-t)*(M1-t); Ptail=np.sum(Q[:t,:]**2) if t>0 else 0.0
        s+=rpow(Ptail,-(cp-a/2))*rpow(Pfull,-(a/2))
    return s
def scan(M0,M1,ML,cp,label,extra=None):
    tests=[]
    for _ in range(3): tests.append(("full",rng.uniform(-1,1,(M1,ML))))
    for eps in [0.3,0.05]:
        u=rng.uniform(-1,1,M1); v=rng.uniform(-1,1,ML); tests.append((f"rank1 e={eps}",eps*np.outer(u,v)))
    # P_tail=0 exactly (top row zero) but Q!=0:
    Q=np.zeros((M1,ML)); Q[M1-1,:]=rng.uniform(-1,1,ML); tests.append(("toprowZERO",Q))
    # near null: top rows tiny
    for g in [0.1,0.01]:
        Q=rng.uniform(-1,1,(M1,ML))*1.0; Q[:1,:]*=g; tests.append((f"toprow~{g}",Q))
    if extra: tests+=extra
    mx=0.0
    for desc,Q in tests:
        Fv=F_of_Q(Q,cp,M0,M1); Rv=rhs_of_Q(Q,cp,M0,M1)
        r=Fv/Rv if Rv>0 else float('inf'); mx=max(mx,r if np.isfinite(r) else mx)
        flag="  <-- RHS=0 but F>0!!" if (Rv==0 and Fv>0) else ""
        print(f"  {label} {desc:14s} F={Fv:11.3f} RHS={Rv:11.3f} F/RHS={r:9.3f}{flag}")
    print(f"  => {label}: max finite ratio = {mx:.3f}\n")

# (2,2,2) across c'
for cp in [0.8,1.5,1.9]: scan(2,2,2,cp,f"(2,2,2)c'={cp}")
# rectangular fronts
scan(3,2,2,0.8,"(3,2,*)c'=0.8"); scan(2,3,2,0.8,"(2,3,*)c'=0.8")
scan(3,3,3,1.0,"(3,3,3)c'=1.0"); scan(3,3,2,1.0,"(3,3,2)c'=1.0")
scan(2,2,3,1.5,"(2,2,3)c'=1.5")

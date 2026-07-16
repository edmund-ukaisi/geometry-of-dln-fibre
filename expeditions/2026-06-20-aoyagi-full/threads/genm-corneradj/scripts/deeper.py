import itertools, numpy as np
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
# find smallest binding cut with a+b=rho+2 (k=2), a,b>=1
found=None
for Lp in [3,4]:
  for M in itertools.product(range(1,6),repeat=Lp):
    mA=minAdm(M); rho=min(M[1:])
    for t in range(1,min(M[0],M[1])+1):
        a,b=M[0]-t,M[1]-t
        if a>=1 and b>=1 and a+b==rho+2 and a*b+minAdm((t,)+M[2:])==mA:
            found=(M,t,a,b,rho,mA); break
    if found: break
  if found: break
print("smallest k=2 binding cut:",found)
M,t,a,b,rho,mA=found
print(f"  a={a} b={b} rho={rho} 1/2minAdm(M)={mA/2}; redChain=({t},{M[2]},{M[3] if len(M)>3 else ''}) "
      f"minAdm(red)={minAdm((t,)+M[2:])} 1/2={minAdm((t,)+M[2:])/2}; need reduction={mA/2-minAdm((t,)+M[2:])/2}=ab/2={a*b/2}")
# test H(w) reduction at Ccross=0 for these (a,b,rho): Zf = rho x q rank rho.
rng=np.random.default_rng(88)
q=M[-1]; M2=M[2]
Zf=rng.standard_normal((M2,q))   # M2 x q, rank min(M2,q); want rank rho
print(f"  Zf {M2}x{q} rank={np.linalg.matrix_rank(Zf)} (rho={rho})")
def H0(cp,w,N=3_000_000):
    A=rng.uniform(-1,1,(N,b,M2)); G=rng.uniform(-1,1,(N,a,b))
    Mm=np.einsum('nij,jk->nik',A,Zf); GM=np.einsum('nij,njk->nik',G,Mm)
    base=w+np.sum(GM**2,(1,2))
    return (2.0**(b*M2+a*b))*np.mean(base**(-cp))
ab2=a*b/2
for cp in [mA/2-0.5, mA/2-0.1]:
    ws=np.array([2.0**(-k) for k in range(3,12)])
    Hs=np.array([H0(cp,w) for w in ws])
    beta=-np.polyfit(np.log(ws),np.log(Hs),1)[0]
    print(f"   c'={cp:.2f} (target<{mA/2}): beta={beta:.2f}; reduction=c'-beta={cp-beta:.2f} (need >= c'-1/2minAdm(red)={cp-minAdm((t,)+M[2:])/2:.2f} to converge; ab/2={ab2})")

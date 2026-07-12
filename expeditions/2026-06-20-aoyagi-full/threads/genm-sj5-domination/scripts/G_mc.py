import numpy as np, sys
rng=np.random.default_rng(11)
def build_Z(M2,Mlast,sigmas):
    A=rng.standard_normal((M2,M2)); U,_=np.linalg.qr(A)
    B=rng.standard_normal((Mlast,M2)); V,_=np.linalg.qr(B)
    return U@np.diag(sigmas[:M2])@V.T
def G_of(w,Z,a,b,cp,Nc=20000,Ng=4000):
    # MC over A_cor (b x M2) box and, for each, MC over Gamma (a x b) box.
    M2,Mlast=Z.shape
    Ac=rng.uniform(-1,1,size=(Nc,b,M2))
    Qb=np.einsum('nbm,ml->nbl',Ac,Z)                      # (Nc,b,Mlast)
    c0=0.3*np.ones((a,Mlast))
    # inner: for each n, MC over Gamma (Ng samples) -> but that's Nc*Ng huge; use shared Gamma block
    Ga=rng.uniform(-1,1,size=(Ng,a,b))                    # shared Gamma sample
    # loss[n,gg] = w + ||c0 + Ga[gg] @ Qb[n]||^2
    # GaQ[gg,n] = Ga[gg](a,b) @ Qb[n](b,Mlast) -> (a,Mlast); do in chunks over n
    volG=(2.0**(a*b)); volC=(2.0**(b*M2))
    tot=0.0
    chunk=500
    for s in range(0,Nc,chunk):
        Q=Qb[s:s+chunk]                                   # (c,b,Mlast)
        GaQ=np.einsum('gab,cbl->gcal',Ga,Q)               # (Ng,c,a,Mlast)
        loss=w+((c0[None,None]+GaQ)**2).sum(axis=(2,3))   # (Ng,c)
        inner=(loss**(-cp)).mean(axis=0)*volG             # (c,)  freed-corner integral per A_cor sample
        tot+=inner.sum()
    return tot/Nc*volC
def line(*a): print(*a); sys.stdout.flush()

def joint(name,a,b,M2,Mlast,cp,ws,sgs):
    ab=a*b; e=cp-ab/2
    line(f"[{name}] a={a} b={b} M2={M2} Mlast={Mlast} cp={cp} e=cp-ab/2={e}: R=G*w^{e} bounded as (w,sg)->0 ?")
    line("   w \\ sg   "+"".join(f"{s:>10.0e}" for s in sgs))
    for w in ws:
        row=[]
        for sg in sgs:
            sigmas=np.array([1.0]*(M2-1)+[sg]) if M2>1 else np.array([sg])
            Z=build_Z(M2,Mlast,sigmas); g=G_of(w,Z,a,b,cp)
            row.append(g*w**e)
        line(f"   {w:>7.0e} "+"".join(f"{r:>10.2f}" for r in row))

joint("anchor 3322",1,1,2,2,1.8,[1e-1,1e-2,1e-3],[1e-1,1e-2,1e-3])
joint("3223 a>=M2",2,1,2,3,1.9,[1e-1,1e-2,1e-3],[1e-1,1e-2,1e-3])
# corank-2, Zdeep with two small sing values (both -> 0): the shared-divisor stress. a=b=2.
line("")
line("[corank2 both-small] a=2 b=2 M2=4 Mlast=4 cp=3.9 (ab/2=2, e=cp-2=1.9): R=G*w^e, sg drives BOTH smallest sings")
cp=3.9; ab=4; e=cp-ab/2
for w in [1e-1,1e-2]:
    row=[]
    for sg in [1e-1,1e-2,1e-3]:
        Z=build_Z(4,4,np.array([1.0,1.0,sg,sg]))
        g=G_of(w,Z,2,2,cp,Nc=8000,Ng=2000); row.append(g*w**e)
    line(f"   w={w:.0e}: "+"".join(f"{r:>12.3f}" for r in row)+"   (sg=1e-1,1e-2,1e-3)")

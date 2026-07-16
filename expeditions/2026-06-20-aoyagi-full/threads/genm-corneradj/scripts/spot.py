import numpy as np
rng=np.random.default_rng(555)
# Binding-edge spot-check. Worst case Ccross=0. Verify H(w)~w^{-(c'-ab/2)}*ln(1/w): reduction = ab/2 EXACTLY.
def H0(a,b,Zf,cp,w,N=3_000_000):
    M2=Zf.shape[0]
    A=rng.uniform(-1,1,(N,b,M2)); G=rng.uniform(-1,1,(N,a,b))
    M=np.einsum('nij,jk->nik',A,Zf); GM=np.einsum('nij,njk->nik',G,M)
    base=w+np.sum(GM**2,(1,2))
    vol=(2.0**(b*M2))*(2.0**(a*b))
    return vol*np.mean(base**(-cp))
def check(tag,a,b,Zf,cprimes):
    ab2=a*b/2
    print(f"\n{tag}: a={a} b={b} rho={np.linalg.matrix_rank(Zf)} -> reduction should be ab/2={ab2}")
    for cp in cprimes:
        ws=np.array([2.0**(-k) for k in range(3,12)])
        Hs=np.array([H0(a,b,Zf,cp,w) for w in ws])
        beta=-np.polyfit(np.log(ws),np.log(Hs),1)[0]
        # log-corrected slope: fit H ~ w^{-(cp-ab2)} * (A + B ln(1/w))
        y=Hs*ws**(cp-ab2); x=np.log(1/ws); sl,_=np.polyfit(x,y,1)
        print(f"   c'={cp:4.2f}: plain-beta={beta:5.2f} (vs c'-ab/2={cp-ab2:.1f}); H*w^(c'-ab/2) vs ln(1/w) slope={sl:.3g} (>0=>log)")
# (3,3,4)@t=1: a=b=2, Zf=3x4 rank3
Zf1=rng.standard_normal((3,4)); check("(3,3,4)@t=1",2,2,Zf1,[3.0,4.0])   # target 1/2 minAdm(3,3,4)=4
# (3,4,4)@t=1: a=2,b=3, Zf=4x4 rank4
Zf2=rng.standard_normal((4,4)); check("(3,4,4)@t=1",2,3,Zf2,[4.0,5.0])   # target 1/2 minAdm(3,4,4)=5

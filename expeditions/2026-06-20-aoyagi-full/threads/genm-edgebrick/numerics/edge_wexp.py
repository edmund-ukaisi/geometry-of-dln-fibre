import numpy as np
rng = np.random.default_rng(2)
a,b,rho,n = 2,2,3,3
Zfix = np.eye(3)
c = 2.4                      # c' ; ab/2=2 ; clean reduction target exponent = c'-ab/2 = 0.4
def box_integral_over_Acor_Gamma(w, NA=4000, NG=4000, Cscale=1.0):
    tot=0.0
    for _ in range(NA):
        A = rng.uniform(-1,1,size=(b,rho)); K=A@Zfix
        Ccross = Cscale*rng.uniform(-1,1,size=(a,n))
        G = rng.uniform(-1,1,size=(NG,a,b))
        E = Ccross[None]+np.einsum('gij,jk->gik',G,K)
        loss = w+np.sum(E*E,axis=(1,2))
        tot += 2.0**(a*b)*np.mean(loss**(-c))
    return 2.0**(b*rho)*tot/NA
def univ_integral(w, NA=4000, NG=4000, sig=4.0, Cscale=1.0):
    tot=0.0
    for _ in range(NA):
        A=rng.uniform(-1,1,size=(b,rho)); K=A@Zfix
        Ccross=Cscale*rng.uniform(-1,1,size=(a,n))
        G=rng.normal(0,sig,size=(NG,a,b)); E=Ccross[None]+np.einsum('gij,jk->gik',G,K)
        loss=w+np.sum(E*E,axis=(1,2))
        wt=np.exp(np.sum(G*G,axis=(1,2))/(2*sig**2))*(sig*np.sqrt(2*np.pi))**(a*b)
        tot+=np.mean(loss**(-c)*wt)
    return 2.0**(b*rho)*tot/NA
ws=[0.2,0.05,0.0125,0.003125]
print(f"EDGE a=b=2 rho=3  c'={c}  ab/2=2  clean-reduction exponent = c'-ab/2 = {c-2}")
print("\nBOX-restricted:")
vb=[box_integral_over_Acor_Gamma(w) for w in ws]
for w,v in zip(ws,vb): print(f"   w={w:.5f}  I={v:12.3f}")
for i in range(len(ws)-1):
    slope=np.log(vb[i+1]/vb[i])/np.log(ws[i+1]/ws[i]); print(f"   -> local exponent (I~w^p): p={slope:.3f}")
print("\nUNIV(det-charge) proxy:")
vu=[univ_integral(w) for w in ws]
for w,v in zip(ws,vu): print(f"   w={w:.5f}  I={v:12.1f}")
for i in range(len(ws)-1):
    slope=np.log(vu[i+1]/vu[i])/np.log(ws[i+1]/ws[i]); print(f"   -> local exponent p={slope:.3f}")

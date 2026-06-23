"""
Fix H2 constants for the (3,2,3) multi-core upper sandwich.
Upper: (A_ij+B_ij)^2 <= 2A_ij^2 + 2B_ij^2 (AM-GM, cleanest).
sum (A+B)^2 <= 2 sum A^2 + 2 sum B^2.  sum B^2 = h^2 (x1^2+x2^2)(x3^2+x4^2).
On box ||x||<=eps (so each |xi|<=eps, h<=1/(1-eps)):
  (x1^2+x2^2)(x3^2+x4^2) <= eps^2 (x1^2+x2^2+x3^2+x4^2)   [since x3^2+x4^2<=eps^2, factor it out...
   actually (x1^2+x2^2)(x3^2+x4^2) <= eps^2*(x3^2+x4^2) <= eps^2*(reg) -- but also <= eps^2*(x1^2+x2^2).
   Use <= eps^2 * reg where reg = x1^2+x2^2+x3^2+x4^2.]  with h^2<=1/(1-eps)^2.
So F <= x0^2 + reg + 2 sum A^2 + 2 h^2 eps^2 reg <= x0^2 + (1 + 2eps^2/(1-eps)^2) reg + 2 sum A^2.
Take eps=0.25 -> 2*0.0625/0.5625 = 0.222 -> coeff 1.222. core coeff 2.
"""
import numpy as np
rng=np.random.default_rng(7)
def rlct(F,dim,R=0.25,N=18_000_000,ts=None):
    X=rng.uniform(-R,R,size=(N,dim)); fv=F(X)
    if ts is None: ts=np.array([1e-3,3e-4,1e-4,3e-5,1e-5,3e-6])
    vols=np.array([np.mean(fv<t)*(2*R)**dim for t in ts]); m=vols>0
    A=np.vstack([np.log(ts[m]),np.ones(m.sum())]).T
    return np.linalg.lstsq(A,np.log(vols[m]),rcond=None)[0][0]
def F(X):
    x0,x1,x2,x3,x4,U3,U5,V4,V5=[X[:,k] for k in range(9)]; h=1/(1+x0)
    return (x0**2+x1**2+x2**2+x3**2+x4**2
            +(U3*V4+h*x1*x3)**2+(U3*V5+h*x2*x3)**2+(U5*V4+h*x1*x4)**2+(U5*V5+h*x2*x4)**2)
def H2(X):
    x0,x1,x2,x3,x4,U3,U5,V4,V5=[X[:,k] for k in range(9)]
    reg=x1**2+x2**2+x3**2+x4**2; core=(U3*V4)**2+(U3*V5)**2+(U5*V4)**2+(U5*V5)**2
    return x0**2+1.30*reg+2*core   # 1.30 > 1.222 safety
def H1(X):
    x0,x1,x2,x3,x4,U3,U5,V4,V5=[X[:,k] for k in range(9)]
    reg=x1**2+x2**2+x3**2+x4**2; core=(U3*V4)**2+(U3*V5)**2+(U5*V4)**2+(U5*V5)**2
    return x0**2+0.70*reg+0.5*core  # lower: (A+B)^2>=A^2/2-2B^2, sum>=0.5 sumA^2 - 2 sumB^2 >= 0.5core - 2h^2eps^2 reg
X=rng.uniform(-0.25,0.25,size=(4_000_000,9))
print("H1<=F on box:", bool(np.all(H1(X)<=F(X)+1e-9)))
print("F<=H2 on box:", bool(np.all(F(X)<=H2(X)+1e-9)))
print("rlct F ~", round(rlct(F,9),3))
print("rlct H1~", round(rlct(H1,9),3), " rlct H2~", round(rlct(H2,9),3), " (target 3.5)")
print("""
The clean split losses x0^2 + c*reg + d*core all have rlct = nReg/2 + lambdaCore(2,1,2) regardless of c,d>0
(coordinate rescale). nReg=5 -> 5/2; lambdaCore(2,1,2)=1 -> total 7/2. So rlct(H1)=rlct(H2)=7/2 => rlct F=7/2.
""")

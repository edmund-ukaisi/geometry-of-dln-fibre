import numpy as np
rng=np.random.default_rng(3)

# lambda(f): Vol{f<eps}~eps^lambda. Reliable for low-codim pieces.
def lam(loss_fn, sampler, boxvol, kmax=20, N=20_000_000):
    eps=np.array([2.0**-k for k in range(1,kmax)])
    s=sampler(N); L=loss_fn(*s)
    V=np.array([np.mean(L<e)*boxvol for e in eps])
    m=V>50/N*boxvol  # keep only well-sampled
    le,lv=np.log(eps[m]),np.log(V[m]); k=min(6,m.sum())
    return np.polyfit(le[-k:],lv[-k:],1)[0], list(zip(eps[m].round(6),V[m]))

# (A) lambda(xi^2+eta^2)=1
la,_=lam(lambda x,y:x*x+y*y, lambda N:(rng.uniform(-1,1,N),rng.uniform(-1,1,N)), 4.0)
print("lambda(xi^2+eta^2) =",round(la,3)," [pred 1]")

# (B) lambda(h), h=(B^2+Gp^2)(t2^2+t3^2)  -> predicted 1 (with log): Vol~eps*log(1/eps)
def h(B,Gp,t2,t3): return (B*B+Gp*Gp)*(t2*t2+t3*t3)
lh,tabh=lam(h, lambda N:(rng.uniform(-1,1,N),)*1+(rng.uniform(-1,1,N),rng.uniform(-1,1,N),rng.uniform(-1,1,N)), 16.0)
print("lambda(h)          =",round(lh,3)," [pred 1, with log]")
for e,v in tabh[-6:]: print(f"     eps={e:.2e} Vol={v:.3e}  Vol/(eps*log(1/eps))={v/(e*np.log(1/e)):.3f}")

# (C) FULL (2,2,3): loss=xi^2+eta^2+h  -> lambda = 1+1 = 2 by disjoint-var additivity.
#     Verify additivity numerically via convolution of the 1D 'volume densities'.
#     Direct: reuse coordinatized separation. Predicted lambda(loss)=2 => int loss^{-c'} finite iff c'<2=T1.
print("=> By disjoint-variable additivity lambda(2,2,3 loss)=lambda(xi^2+eta^2)+lambda(h)=1+1=2=T1  [ANALYTIC]")

# (D) Codex's decoupled PIVOT block for M2>M1 witness (3,3,4)@u=1: pivot map (P,B)->[P|B]hsQ,
#     hsQ 3x4 (rows [Qp(1x4); Qb(2x4)]), u=1 copy x->x*hsQ, x in R^{M1}=R^3, rank=rho=min(3,4)=3.
#     kernel codim=3 => pivot alone lambda=3/2 => c'' < 3/2. Comparator needs 1/2 minAdm(M').
def piv334(x1,x2,x3):
    # hsQ 3x4 random-but-fixed full rank; pivot energy ||[x1,x2,x3] . hsQ||^2
    hsQ=np.array([[1,0,0,0],[0.3,1,0,0.2],[0.1,0.4,1,0.5]])
    v=np.stack([x1,x2,x3],1)@hsQ
    return (v*v).sum(1)
lp,_=lam(piv334, lambda N:(rng.uniform(-1,1,N),rng.uniform(-1,1,N),rng.uniform(-1,1,N)),8.0)
print("(3,3,4)@u=1 decoupled pivot-block lambda =",round(lp,3)," [pred rho/2=3/2=1.5]  -> pivot ALONE tops at c''<1.5")

# (E) Same (3,3,4)@u=1 but COUPLED with the corank/t structure: loss=||V||^2 + ||W Y||^2 style.
#     Confirm coupled object is finite to T1=1/2 minAdm(3,3,4). minAdm(3,3,4)=8 (r=1) => T1=4.
def minAdm3(M0,M1,M2):
    return min((M0-r)*(M1-r)+r*M2 for r in range(min(M0,M1)+1))
print("minAdm(3,3,4)=",minAdm3(3,3,4)," T1=",minAdm3(3,3,4)/2)

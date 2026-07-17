import numpy as np
np.random.seed(2)
print("D. TRUE inner I(S)=∫_box frobSq(ΓS)^{-c'} vs clean det-power det(SSᵀ)^{-a/2}, a=b=2")
print("   eigenvalues(SSᵀ)=(1,eps); active split p=a(b-1)=2, full ab=4. box=[-1,1]^{2x2}.")
# I(eps)=∫ (U + eps V)^{-c'}, U=g11²+g21² (wt-1 col), V=g12²+g22² (eps col). grid n=90.
n=90
xs,ws=np.polynomial.legendre.leggauss(n)
G=np.add.outer(xs**2,xs**2).ravel()      # 8100 vals of a 2-var square-block radius²
Wt=np.multiply.outer(ws,ws).ravel()
def I_inner(eps,cp):
    return float((( (G[:,None]+eps*G[None,:])**(-cp) )*(Wt[:,None]*Wt[None,:])).sum())
for cp,label in [(0.7,"2c'=1.4<p=2 REGIME 1 (bounded)"),(1.2,"p<=2c'=2.4<4 REGIME 2 (mild power)")]:
    print(f"\n c'={cp}  [{label}]   true-exponent e=max(0,c'-a(b-1)/2)=max(0,{cp}-1)={max(0,cp-1)}  (< a/2=1)")
    print(f"   {'eps':>10} {'I(eps)':>12} {'det^-a/2=eps^-1':>16} {'I*eps^e':>12}")
    for eps in [1.0,0.25,0.01,4e-4,1e-5]:
        Iv=I_inner(eps,cp); e=max(0,cp-1)
        print(f"   {eps:>10.0e} {Iv:>12.3f} {eps**-1:>16.1f} {Iv*eps**e:>12.3f}")
print("\n Regime1: I(eps) rises to a FINITE limit (bounded) while det-power ~eps^-1 blows up.")
print(" Regime2: I(eps)~eps^-e with e=c'-1 <1=a/2 (I*eps^e ~ const); det-power exponent a/2 STRICTLY larger.")
print(" => clean det-power OVERESTIMATES by eps^{-(a/2 - e)}, e=max(0,c'-a(b-1)/2). CONFIRMS l2morse.")

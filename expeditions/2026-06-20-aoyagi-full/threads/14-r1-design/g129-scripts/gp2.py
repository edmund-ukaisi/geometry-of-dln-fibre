import sympy as sp, numpy as np
p,q,r,s,t,u_,v,w = sp.symbols('p q r s t u v w', real=True)
b = sp.symbols('b0:9', real=True)
Ahat = sp.Matrix([[1,p,q],[r,s,t],[u_,v,w]]); A2 = sp.Matrix(3,3,b)
M = sp.expand(Ahat*A2)
def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))
F = fro2(M)
E0,E1,E2 = sp.symbols('E0 E1 E2', real=True)
sub = {b[0]: E0 - p*b[3] - q*b[6], b[1]: E1 - p*b[4] - q*b[7], b[2]: E2 - p*b[5] - q*b[8]}
F_E = sp.expand(F.subs(sub))
a = sp.Poly(F_E,E0,E1,E2).coeff_monomial(E0**2)
shifts={}
for Ei in [E0,E1,E2]:
    lin = sp.expand(F_E.diff(Ei).subs({E0:0,E1:0,E2:0})); shifts[Ei]= -lin/(2*a)
Gp = sp.expand(sp.cancel(F_E.subs({E0:shifts[E0],E1:shifts[E1],E2:shifts[E2]})))
S = sp.Matrix([[s-p*r, t-q*r],[v-p*u_, w-q*u_]]); A2red=A2[1:,:]
Score = sp.expand(fro2(sp.expand(S*A2red)))
allv = (p,q,r,s,t,u_,v,w,b[3],b[4],b[5],b[6],b[7],b[8])
fG = sp.lambdify(allv, Gp, 'numpy'); fS = sp.lambdify(allv, Score, 'numpy')
print("Ratio G'/Score near 0 (bounded unit => squeeze-equivalent):")
rng = np.random.default_rng(1)
for scale in [0.3,0.1,0.03,0.01]:
    X = rng.uniform(-scale,scale,(20000,14))
    sv = fS(*[X[:,i] for i in range(14)]); gv = fG(*[X[:,i] for i in range(14)])
    m = np.abs(sv)>1e-15
    ratio = gv[m]/sv[m]
    print(f"  scale={scale}: min={ratio.min():.4f} max={ratio.max():.4f}  (n={m.sum()})")
# Is G' lower-bounded by c*Score and upper by C*Score? squeeze both ways needs both finite & positive.
print("\nLeading-order: G' and Score at FIRST order. The denominator a=1+r²+u² -> 1 at origin, so")
print("at lowest order G' ≈ Score; the ratio range above quantifies the squeeze constants c1,c2.")

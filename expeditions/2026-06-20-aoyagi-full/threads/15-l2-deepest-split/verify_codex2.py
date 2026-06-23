"""Verify Codex's explicit change of variables EXACTLY."""
import sympy as sp
x1,x2,x3,p,q,u,v = sp.symbols('x1 x2 x3 p q u v', real=True)
D = 1 - p*q + x1
E11 = sp.simplify((u*v*(1-p*q+x1) + (p*v - x2)*(u*q - x3))/D)
print("E11 =", E11)

U = (u*(1+x1) - p*x3)/D
V = v - q*x2/(1+x1)
h = 1/(1+x1)
claim1 = sp.simplify(E11 - (U*V + h*x2*x3))
print("CLAIM 1: E11 - (U V + x2 x3/(1+x1)) =", claim1)

S = 1 + h**2 * x3**2
R = sp.sqrt(S)
C1, C2 = U, V/R
y1, y3 = x1, x3
y2 = R*x2 + h*x3*U*V/R
F_orig = x1**2 + x2**2 + x3**2 + (U*V + h*x2*x3)**2
F_new  = y1**2 + y2**2 + y3**2 + (C1*C2)**2
print("CLAIM 2: F_orig - (y1^2+y2^2+y3^2+(C1 C2)^2) =", sp.simplify(F_orig - F_new))

# Final-stage Jacobian (x1,x2,x3,U,V)->(y1,y2,y3,C1,C2) at 0
Uu,Vv = sp.symbols('U V', real=True)
hh = 1/(1+x1); RR=sp.sqrt(1+hh**2*x3**2)
ymap = [x1, RR*x2 + hh*x3*Uu*Vv/RR, x3, Uu, Vv/RR]
xs = [x1,x2,x3,Uu,Vv]
Jf0 = sp.Matrix([[sp.diff(f,xx) for xx in xs] for f in ymap]).subs({x1:0,x2:0,x3:0,Uu:0,Vv:0})
print("Final-stage Jac det at 0 =", sp.simplify(Jf0.det()))

J1 = sp.Matrix([[sp.diff(U,u),sp.diff(U,v)],[sp.diff(V,u),sp.diff(V,v)]]).subs({x1:0,x2:0,x3:0,p:0,q:0})
print("Stage-1 d(U,V)/d(u,v) at 0 det =", J1.det())

# FULL end-to-end: F in ORIGINAL 8 perturbation vars must equal y1^2+y2^2+y3^2+(C1 C2)^2 with
# everything pulled back. We already verified Phi gives F = x1^2+x2^2+x3^2+E11^2 (l2_222_diffeo).
# And E11 = U V + h x2 x3 (claim1). And the completion gives the clean form (claim2). So end-to-end holds
# IF claim1 and claim2 are both 0.

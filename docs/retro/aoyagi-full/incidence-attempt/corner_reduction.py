"""
Exact reduction of the (2,2,3),u=1,j=1 corner integral, and the coupling check.
"""
import sympy as sp

p,beta,c0,gam,t2,t3,r,cp,eps = sp.symbols('p beta c0 gam t2 t3 r cprime eps',real=True)

# honest loss at corner (Q_p=e1=(1,0,0), Q_b=(1,t2,t3))
loss = (p+beta)**2 + beta**2*(t2**2+t3**2) + (c0+gam)**2 + gam**2*(t2**2+t3**2)
print("loss =", sp.expand(loss))

# --- (A) confirm the degenerate locus & that it is a nondegenerate quadratic transverse to it ---
# set x=p+beta, y=c0+gam. On locus x=y=t2=t3=0, beta and gam free (spectators).
x,y = sp.symbols('x y',real=True)
lossxy = x**2 + y**2 + (beta**2+gam**2)*(t2**2+t3**2)
# Hessian in the 4 transverse coords (x,y,t2,t3) at a point of the locus (beta=b0,gam=g0):
b0,g0 = sp.symbols('b0 g0',real=True,positive=True)
H = sp.hessian(lossxy.subs({beta:b0,gam:g0}), (x,y,t2,t3))
Hloc = H.subs({x:0,y:0,t2:0,t3:0})
print("\nHessian at locus (x=y=t2=t3=0):")
sp.pprint(Hloc)
print("eigenvalues:", Hloc.eigenvals())
print("=> positive-definite iff b0^2+g0^2>0 (a UNIT there since beta~-1). 4-dim nondeg quadratic.")

# --- (B) radial reduction of a 4-dim positive-definite quadratic Q(v)=sum lam_i v_i^2 ---
# int_{|v|<d} Q(v)^{-c'} dv  ~  (const) int_0^d rho^{4-1} rho^{-2c'} d rho = int rho^{3-2c'} d rho
print("\n4-dim pos-def quadratic radializes: int rho^{3} * rho^{-2c'} drho = int rho^{3-2c'} drho")
for cc in [sp.Rational(19,10), sp.Rational(2), sp.Rational(21,10)]:
    I = sp.integrate(r**(3-2*cc), (r,0,1))
    print(f"   c'={cc}:  int_0^1 r^(3-2c') dr = {I}   ({'finite' if I.is_finite else 'DIVERGES'})")

# --- (C) COUPLING CHECK: after P-radial blow-up (p,beta)=R*(op,ob), is pivot weight A_cor-free? ---
R,op,ob = sp.symbols('R op ob',real=True)
pivot_w = (p+beta)**2 + beta**2*(t2**2+t3**2)          # = ||[P|B12] hsQ||^2  (u=1 row)
pivot_w_blow = pivot_w.subs({p:R*op, beta:R*ob})
pivot_w_blow = sp.factor(pivot_w_blow)
print("\npivot weight after (p,beta)=R(op,ob):")
sp.pprint(pivot_w_blow)
print("  = R^2 * [ (op+ob)^2 + ob^2 (t2^2+t3^2) ]  -> STILL depends on A_cor=(t2,t3).")
print("  => K5 P-radial blow-up does NOT decouple the pivot weight to an A_cor-free form (K4 blocked).")
print("     The residual coupling ob^2*(t2^2+t3^2) IS the transverse/incidence term.")

# --- (D) transverse Schur identity K2 sanity (numeric exact) ---
# hsQ = [[1,0,0],[q1,t2,t3]]; det(hsQ hsQ^T) = det(Q_p Q_p^T)*det(Q_b (I-Pi_p) Q_b^T)
q1 = sp.symbols('q1',real=True)
Qp = sp.Matrix([[1,0,0]]); Qb = sp.Matrix([[q1,t2,t3]])
hsQ = Qp.col_join(Qb)
lhs = (hsQ*hsQ.T).det()
Pi_p = Qp.T*(Qp*Qp.T).inv()*Qp                      # proj onto rowspan(Q_p)
I3 = sp.eye(3)
schur = (Qb*(I3-Pi_p)*Qb.T)[0,0]
rhs = (Qp*Qp.T).det() * schur
print("\nK2 Schur identity: det(hsQ hsQ^T) - det(QpQp^T)*det(Qb(I-Pi_p)Qb^T) =",
      sp.simplify(lhs-rhs))
print("   transverse Schur det(Qb(I-Pi_p)Qb^T) =", sp.simplify(schur), " (= t2^2+t3^2, ->0 at incidence)")
print("   bare Gram det(Qb Qb^T) =", sp.simplify((Qb*Qb.T).det()), " (~1 at incidence: q1~1) -> blind")

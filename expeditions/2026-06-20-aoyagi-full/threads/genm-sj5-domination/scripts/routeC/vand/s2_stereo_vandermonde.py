import sympy as sp

# ===== s=2: RATIONAL (tangent-half-angle) parametrization of the SO(2) frame =====
# Symmetric 2x2 H = [[p,r],[r,q]], eigenvalues mu1,mu2.
# Rational chart: t = tan(theta), Q(theta) rotation.  cos^2 = 1/(1+t^2), sin^2=t^2/(1+t^2), cs = t/(1+t^2)
mu1,mu2,t = sp.symbols('mu1 mu2 t', real=True)
den = 1+t**2
p = (mu1 + mu2*t**2)/den
q = (mu1*t**2 + mu2)/den
r = (mu1-mu2)*t/den

J = sp.Matrix([p,q,r]).jacobian([mu1,mu2,t])
detJ = sp.simplify(J.det())
print("s=2 stereographic map (mu1,mu2,t) -> (p,q,r):")
print("  det D(p,q,r)/D(mu1,mu2,t) =", detJ)
# factor out
fac = sp.factor(detJ)
print("  factored =", fac)

# Consistency: trace = p+q, det = pq - r^2 should be mu1+mu2, mu1*mu2
print("  trace check p+q-mu1-mu2 =", sp.simplify(p+q-mu1-mu2))
print("  det   check pq-r^2-mu1*mu2 =", sp.simplify(p*q-r**2-mu1*mu2))

# The classical eigenvalue Jacobian is dH = |mu1-mu2| dmu1 dmu2 dtheta.
# In stereographic coord: dtheta = 2/(1+t^2) dt (Haar SO(2) rational density).
# So dH should = |mu1-mu2| * (2/(1+t^2)) dmu1 dmu2 dt.
haar = 2/den
expected = (mu1-mu2)*haar
print("  detJ / [(mu1-mu2)*2/(1+t^2)] =", sp.simplify(detJ/expected))
print("  => detJ = (mu1-mu2) * [rational-in-t density]:", sp.simplify(detJ/(mu1-mu2)))

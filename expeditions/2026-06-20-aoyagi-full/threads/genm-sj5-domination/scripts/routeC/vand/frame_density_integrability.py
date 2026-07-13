import sympy as sp
# 1) SO(3) Cayley-Haar density integrability: int_{R^3} 8/(1+a^2+b^2+c^2)^2 da db dc  finite?
r=sp.symbols('r',positive=True)
val=sp.integrate(8*4*sp.pi*r**2/(1+r**2)**2,(r,0,sp.oo))
print("int_{R^3} 8/(1+|S|^2)^2 dS =", sp.simplify(val), " (finite => Cayley frame integrates to a CONSTANT)")

# 2) SO(2) stereographic Haar: int_R  1/(1+t^2) dt
t=sp.symbols('t',real=True)
print("int_R 1/(1+t^2) dt =", sp.integrate(1/(1+t**2),(t,-sp.oo,sp.oo)), " (finite)")

# 3) codim of collision locus {mu1=mu2} in Sym(2): {p=q, r=0} in (p,q,r) -> codim 2.
#    Vandermonde |mu1-mu2| = sqrt((p-q)^2+4r^2) ~ distance to that codim-2 locus (vanishes to order 1).
#    As a NUMERATOR factor: order-1 zero on codim-2 => trivially integrable, NO blow-up needed.
p,q,rr=sp.symbols('p q rr',real=True)
mu1=( (p+q)+sp.sqrt((p-q)**2+4*rr**2) )/2
mu2=( (p+q)-sp.sqrt((p-q)**2+4*rr**2) )/2
print("Sym(2): |mu1-mu2| =", sp.simplify(mu1-mu2), " -> zero locus {p=q,r=0} has codim 2")

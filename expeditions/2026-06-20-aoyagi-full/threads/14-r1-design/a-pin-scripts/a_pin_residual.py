import sympy as sp
# Compute the residual core after the (a)-split at v for (2,2,2). Solve the 3 regular generators,
# substitute into P10, identify the homogeneous residual.
w = sp.symbols('w0:8', real=True)
W1 = sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2 = sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1 = sp.Matrix([[1,0],[0,0]]); v2 = sp.Matrix([[0,0],[0,1]])
P = sp.expand((v1+W1)*(v2+W2))
# Regular generators: P00 (lin w4), P01 (lin w1+w5), P11 (lin w3). Solve for w4, (w1 or w5), w3 in
# terms of the rest, to leading order (implicit function thm).
P00,P01,P10,P11 = P[0,0],P[0,1],P[1,0],P[1,1]
# Solve P00=0 for w4, P11=0 for w3, P01=0 for w5 (each has a clean linear term).
sol = sp.solve([P00, P11, P01], [w[4], w[3], w[5]], dict=True)
print("solved (w4,w3,w5) from P00=P11=P01=0:")
s=sol[0]
for k,v in s.items(): print(f"  {k} = {sp.simplify(v)}")
# Substitute into P10 (the residual generator):
P10_res = sp.simplify(P10.subs(s))
print("\nResidual generator P10 on the regular-zero locus:")
print("  P10_res =", sp.expand(P10_res))
# The residual core = P10_res^2 (the surviving generator). Its leading homogeneous part:
P10_exp = sp.expand(P10_res)
# lowest-degree terms in the free vars (w0,w1,w2,w6,w7):
free = [w[0],w[1],w[2],w[6],w[7]]
poly = sp.Poly(P10_exp, *free)
mindeg = min(sum(m) for m in poly.monoms())
lead = sum(c*sp.prod([fr**e for fr,e in zip(free,m)]) for m,c in zip(poly.monoms(),poly.coeffs()) if sum(m)==mindeg)
print(f"\n  lowest-degree (={mindeg}) part of P10_res =", sp.expand(lead))
print()
print("INTERPRETATION: the residual core after the v-split is P10_res^2, a single generator of degree",
      mindeg, "in the free vars. The residual is a HOMOGENEOUS core (leading degree", mindeg, ").")
print("Whether it is itself a ||smaller-chain||^2 determines if #111 applies to it.")

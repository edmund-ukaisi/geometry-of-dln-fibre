import sympy as sp
w = sp.symbols('w0:12', real=True)
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[0,0],[1,1]]); v3=sp.Matrix([[1,1],[1,1]])
C1=v1+sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); C2=v2+sp.Matrix([[w[4],w[5]],[w[6],w[7]]]); C3=v3+sp.Matrix([[w[8],w[9]],[w[10],w[11]]])
P=sp.expand(C1*C2*C3)
g=[sp.expand(P[i,j]) for i in range(2) for j in range(2)]
sol=sp.solve([g[0],g[2]],[w[4],w[3]],dict=True)[0]
res1=sp.simplify(g[1].subs(sol)); res3=sp.simplify(g[3].subs(sol))
# Extract leading (lowest-degree) form by substituting w_i -> t*w_i and taking lowest t-power.
t=sp.symbols('t', positive=True)
free=[w[0],w[1],w[2],w[5],w[6],w[7],w[8],w[9],w[10],w[11]]
def leading_form(expr):
    e=expr
    for f in free: e=e.subs(f, t*f)
    e=sp.series(e, t, 0, 4).removeO()
    e=sp.expand(e)
    # lowest power of t:
    p=sp.Poly(e, t)
    if e==0: return 0, None
    md=min(m[0] for m in p.monoms())
    coeff=p.coeff_monomial(t**md)
    return md, sp.expand(coeff)
for nm,r in [('res1(g1)',res1),('res3(g3)',res3)]:
    md,lead=leading_form(r)
    print(f"  {nm}: leading degree {md}, leading form = {lead}")
print()
print("The residual core = res1^2 + res3^2 (the 2 dependent generators on the regular locus).")
print("If both leading forms are degree d (same), the core is HOMOGENEOUS of degree d at leading order.")
print("=> (a)-split at this intermediate v = [regular dim-2 quadratic] + [homogeneous-deg-d residual core].")

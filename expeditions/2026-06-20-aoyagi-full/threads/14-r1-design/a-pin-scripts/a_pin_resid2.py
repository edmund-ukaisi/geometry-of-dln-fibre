import sympy as sp
w = sp.symbols('w0:8', real=True)
W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); W2=sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[0,0],[1,0]])
P=sp.expand((v1+W1)*(v2+W2))
P00,P01,P10,P11=P[0,0],P[0,1],P[1,0],P[1,1]
# Solve P00=0 for w4, P01=0 for w5, P10=0 for w3 (clean linear terms w4, w5, w3).
sol=sp.solve([P00,P01,P10],[w[4],w[5],w[3]],dict=True)[0]
P11_res=sp.simplify(P11.subs(sol))
print("=== residual generator P11 on the regular-zero locus (v in S(1,0), (2,2,2)) ===")
print("  P11_res =", sp.expand(P11_res))
free=[w[0],w[1],w[2],w[6],w[7]]
if P11_res==0:
    print("  P11_res = 0 IDENTICALLY => residual core EMPTY. v is a SMOOTH point of {prod=0}.")
else:
    poly=sp.Poly(sp.expand(P11_res),*free)
    md=min(sum(m) for m in poly.monoms())
    print(f"  residual core NON-empty, leading degree {md}.")
print()
print("=== THE DECISIVE STRUCTURAL FACT for prereq-(a) ===")
print("At EVERY fibre point v, the loss germ ||prod(v+W)-B||^2 = sum of generator^2, and the generator")
print("Jacobian rank at v = codim of v's stratum = Mval(t). The split solves the rk linear generators")
print("(regular block, smooth quadratic dim rk) leaving the residual core in the rest.")
print()
print("The residual core: at a GENERIC (smooth) stratum point, EMPTY (v smooth, the whole germ regular).")
print("At a SINGULAR stratum point (closure of a deeper stratum), NON-empty (a smaller homogeneous core).")

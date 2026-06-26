import sympy as sp
from adv_dln import build_chain_symbols, product

print("="*72)
print("DISENTANGLE: gauge ORBIT (curved) flat vs Hessian-NULLSPACE (linear) direction not flat")
print("="*72)
# (2,1,2) r=1: C1 (2x1), C2 (1x2). deepest C1=[1,0]^T, C2=[1,0]. ambient 4, nReg 3, flat 1.
H=(2,1,2)
base=[sp.Matrix([[1],[0]]), sp.Matrix([[1,0]])]
mats, allv = build_chain_symbols(H, base)
P=product(mats); B=sp.zeros(2,2); B[0,0]=1
F=sp.expand(sum((P[i,j]-B[i,j])**2 for i in range(2) for j in range(2)))
Hm=sp.hessian(F,allv).subs({v:0 for v in allv})
ker=Hm.nullspace()
print(f"(2,1,2): ambient {len(allv)}, Hessian rank {Hm.rank()}, nullspace dim {len(ker)}")
t=sp.Symbol('t',real=True)
for i,kv in enumerate(ker):
    Fr=sp.expand(F.subs({allv[j]: t*kv[j] for j in range(len(allv))}))
    print(f"  along LINEAR nullspace dir {list(kv)}: F = {Fr}")
# The EXACT gauge orbit: C1 -> (1+t)*[1,0]^T, C2 -> [1/(1+t),0]. product invariant.
# vars: c0_0_0 (C1[0,0]), c0_1_0 (C1[1,0]), c1_0_0(C2[0,0]), c1_0_1(C2[0,1])
names={str(v):v for v in allv}
gauge={names['c0_0_0']: t, names['c0_1_0']:0, names['c1_0_0']: 1/(1+t)-1, names['c1_0_1']:0}
Fg=sp.simplify(F.subs(gauge))
print(f"  along EXACT gauge orbit C1=(1+t)e0, C2=e0/(1+t): F = {Fg}  -> {'FLAT' if Fg==0 else 'NOT FLAT'}")
print()
print("INTERPRETATION: the gauge ORBIT (curved) is genuinely flat. The Hessian-nullspace LINEAR direction")
print("is the orbit's tangent; moving linearly off the curved orbit re-enters the nondeg cone (the t^4).")
print()

print("="*72)
print("RLCT of the ACTUAL loss on a small degenerate-boundary case (does t^4 change nReg/2?)")
print("="*72)
# (2,1,2): the loss F as polynomial in 4 vars. RLCT = sup{c : |F|^{-c} integrable near 0}.
# Compute F explicitly and find its Newton-polytope / RLCT structure. Use the substitution to normal form.
F2=sp.expand(F)
print(f"  (2,1,2) loss F = {F2}")
# Let a=c0_0_0, b=c0_1_0, p=c1_0_0, q=c1_0_1. C1=[1+a, b], C2=[1+p, q]. product 2x2:
#   [[ (1+a)(1+p), (1+a)q ],[ b(1+p), b q ]]. B=e00. F = ((1+a)(1+p)-1)^2 + ((1+a)q)^2 + (b(1+p))^2 + (bq)^2
a,b,p,q=sp.symbols('a b p q',real=True)
Fexpl=((1+a)*(1+p)-1)**2 + ((1+a)*q)**2 + (b*(1+p))**2 + (b*q)**2
print(f"  explicit: {sp.expand(Fexpl)}")
# Leading behaviour near 0: (a+p+ap)^2 + (q+aq)^2 + (b+bp)^2 + (bq)^2.
# To 2nd order: (a+p)^2 + q^2 + b^2 + O(deg4). Hessian rank 3 (vars a,p appear as (a+p) -> rank1; q,b -> 2). =3 ✓
# The flat dir is a-p (a=-p ... actually the orbit). Set a = s, p such that (1+a)(1+p)=1 => 1+p=1/(1+s).
# Along the TRUE zero set of the first term: parametrize. The RLCT of sum of squares = (codim of common zero)/2
# IF the zero set is smooth. Common zero of F: F=0 iff all four terms 0.
sol=sp.solve([(1+a)*(1+p)-1, (1+a)*q, b*(1+p), b*q],[a,b,p,q],dict=True)
print(f"  zero set of F (F=0): solutions {sol}")

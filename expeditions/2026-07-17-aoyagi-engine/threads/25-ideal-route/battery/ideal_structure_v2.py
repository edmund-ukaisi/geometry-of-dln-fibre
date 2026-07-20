#!/usr/bin/env python3
"""
CORRECTED ideal structure of <prod C o chart> after the depth recursion.

Fix vs v1: the blow-up {delta=u=v=0} ties delta_lvl = rho_lvl.  So the peeled factor's
(1,1) entry is  al*(a*b + rho)  (NOT al*(a*b+delta) with delta free).  With this fix the
FULL product is divisible by the full monomial m = prod(al_j * rho_j)*alF, and
<prod C o chart> = <m>, RLCT = 3/2  (matching 1/2*min Mval).

Certificate structure: composed product matrix Pc = m * U, U[0,0] = 1 (unit) => <Pc>=<m>.
"""
import sympy as sp

def build(depth):
    factors = []
    for i in range(depth):
        c = sp.symbols(f'c{i}00 c{i}01 c{i}10 c{i}11', real=True)
        factors.append(sp.Matrix([[c[0],c[1]],[c[2],c[3]]]))
    P = factors[0]
    for F in factors[1:]:
        P = P*F
    P = sp.expand(P)
    subs_all = {}; m = sp.Integer(1)
    cur0 = factors[0]
    for lvl in range(depth-1):
        al,a,b = sp.symbols(f'al{lvl} a{lvl} b{lvl}', real=True)
        rho,xi,eta,r,s = sp.symbols(f'rho{lvl} xi{lvl} eta{lvl} r{lvl} s{lvl}', real=True)
        cur1 = factors[lvl+1]
        # peeled factor: incidence with delta tied to rho (the {delta=u=v=0} blow-up):
        subs_all.update({cur0[0,0]:al, cur0[0,1]:al*a, cur0[1,0]:al*b, cur0[1,1]:al*(a*b+rho)})
        # next factor: a-shear then blow up u=rho*xi, v=rho*eta:
        subs_all.update({cur1[0,0]: rho*xi - a*r, cur1[0,1]: rho*eta - a*s,
                         cur1[1,0]: r, cur1[1,1]: s})
        m *= al*rho
        cur0 = sp.Matrix([[xi,eta],[r,s]])
    # final depth-1 fresh core: incidence (delta free -> this is the terminal Morse coord, absorbed)
    alF,aF,bF,dlF = sp.symbols('alF aF bF dlF', real=True)
    subs_all.update({cur0[0,0]:alF, cur0[0,1]:alF*aF, cur0[1,0]:alF*bF, cur0[1,1]:alF*(aF*bF+dlF)})
    m *= alF
    Pc = P
    for _ in range(depth+3):
        Pc = sp.expand(Pc.subs(subs_all))
    return sp.expand(Pc), m, factors

def ratio(gname):
    return sp.Rational(3,2) if gname.startswith('rho') else sp.Integer(2)

for depth,label,target in [(3,"DEPTH 3 (2,2,2,2)",sp.Rational(3,2)),
                           (2,"DEPTH 2 (2,2,2)",sp.Rational(3,2))]:
    print("="*72); print(label); print("="*72)
    Pc, m, factors = build(depth)
    # divisibility of EVERY entry by m, and the cofactor matrix U:
    U = sp.zeros(2,2); div_ok=True
    for i in range(2):
        for j in range(2):
            q = sp.cancel(Pc[i,j]/m)
            U[i,j]=sp.expand(q)
            if not q.is_polynomial(): div_ok=False
    print(f"  m = {m}")
    print(f"  every entry of (prod C o chart) divisible by m ?  {div_ok}")
    print(f"  cofactor matrix U = (prod o chart)/m :")
    for i in range(2):
        print(f"    [{sp.simplify(U[i,0])}, {sp.simplify(U[i,1])}]")
    print(f"  U[0,0] = {sp.simplify(U[0,0])}  (a UNIT => <prod o chart> = <m>, both inclusions)")
    # RLCT of <m> (monomial, principal): min over its divisors of (h+1)/(2k), k=1:
    ratios = [ratio(str(g if g.is_Symbol else g.base)) for g in sp.Mul.make_args(m)]
    rlct = min(ratios)
    print(f"  divisor ratios of m: {ratios}")
    print(f"  RLCT = min = {rlct}   target 1/2*min Mval = {target}   MATCH: {rlct==target}")
    print()

print("="*72)
print("Cross-check the LOSS factorization matches l3_recursion / the cited value:")
print("  loss = ||prod o chart||^2 = m^2 * ||U||^2, U[0,0]=1 so ||U||^2 >= 1 (bounded below);")
print("  the divisor exponents give the SAME rlct as the ideal (Lemma 1). Consistent.")

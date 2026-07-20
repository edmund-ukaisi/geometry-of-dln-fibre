#!/usr/bin/env python3
"""
!!! SUPERSEDED-BY ideal_structure_v2.py  (do NOT cite as corroboration of the headline). !!!
!!! BUG: this script leaves the incidence coordinate delta FREE at the intermediate peels    !!!
!!! (incidence_sub sets F[1,1]=al*(a*b+dl) with dl free) and never applies the {delta=u=v=0}  !!!
!!! blow-up tie delta=rho.  Consequently the bottom-row entries are NOT divisible by the rho   !!!
!!! factors and it PRINTS "ideal equality: False" -- the OPPOSITE of the true result.          !!!
!!! It exits 0 but its content is WRONG.  The correct version (ideal_structure_v2.py) ties      !!!
!!! delta=rho and gets every entry divisible by the full m, U[0,0]=1, RLCT 3/2.                 !!!
!!! KEEP ONLY as a cautionary data point: the delta=rho tie (from the blow-up) is LOAD-BEARING; !!!
!!! drop it (free delta) and the ideal equality fails.  The exact single-layer derivation of    !!!
!!! that tie is ideal_peel_identity.py (delta->rho IS the {delta=u=v=0} blow-up, not assumed).  !!!

RIGOROUS ideal equality  <prod C o chart> = <m>  (both inclusions), exact.

Carry the FULL composed product matrix through the nested depth-recursion charts,
factor out the extracted monomial m, and check the quotient U = (prod o chart)/m:
  (subset)  every entry of prod o chart is divisible by m           => <prod o chart> subset <m>;
  (supset)  U[0,0] is a UNIT at the leaf (nonzero at a generic
            exact-rational leaf point)                              => m = m*U[0,0]*U[0,0]^{-1} in <prod o chart>
                                                                        => <m> subset <prod o chart>.
Hence <prod o chart> = <m>, a MONOMIAL ideal, in the local ring at the leaf.  Plus a
Groebner cross-check in the localized ring (Rabinowitsch: invert the leaf-units) at depth 2.
"""
import sympy as sp

def incidence_sub(F, al, a, b, dl):
    """substitution dict sending F's 4 entries to the incidence chart al*[[1,a],[b,ab+dl]]."""
    return {F[0,0]:al, F[0,1]:al*a, F[1,0]:al*b, F[1,1]:al*(a*b+dl)}

def ashear_blowup_sub(F, a, rho, xi, eta, r, s):
    """
    the next factor F is a-sheared then blown up:  its entries are reparametrized as
    F = [[u-a r, v-a s],[r,s]] with u=rho xi, v=rho eta.  Returns the substitution on F's entries.
    """
    return {F[0,0]: rho*xi - a*r, F[0,1]: rho*eta - a*s, F[1,0]: r, F[1,1]: s}

def build_and_check(depth, label):
    print("="*72); print(f"{label}: depth {depth}"); print("="*72)
    factors = []
    for i in range(depth):
        c = sp.symbols(f'c{i}00 c{i}01 c{i}10 c{i}11', real=True)
        factors.append(sp.Matrix([[c[0],c[1]],[c[2],c[3]]]))
    P = factors[0]
    for F in factors[1:]:
        P = P*F
    P = sp.expand(P)

    m = sp.Integer(1)
    # peel levels 0 .. depth-2 : each consumes factor[lvl] (already folded into the running fresh core)
    # We track the CURRENT fresh-core-left factor as 'cur0' (its 4 symbols) and the NEXT factor 'cur1'.
    cur0 = factors[0]
    subs_all = {}
    for lvl in range(depth-1):
        al,a,b,dl = sp.symbols(f'al{lvl} a{lvl} b{lvl} dl{lvl}', real=True)
        rho,xi,eta,r,s = sp.symbols(f'rho{lvl} xi{lvl} eta{lvl} r{lvl} s{lvl}', real=True)
        cur1 = factors[lvl+1] if lvl==0 else sp.Matrix([[sp.Symbol(f'xi{lvl-1}',real=True),
                                                         sp.Symbol(f'eta{lvl-1}',real=True)],
                                                        [sp.Symbol(f'r{lvl-1}',real=True),
                                                         sp.Symbol(f's{lvl-1}',real=True)]]) if False else factors[lvl+1]
        # cur0 gets incidence; cur1 gets a-shear+blowup; the FRESH core is [[xi,eta],[r,s]]
        sub = {}
        sub.update(incidence_sub(cur0, al,a,b,dl))
        sub.update(ashear_blowup_sub(cur1, a, rho, xi, eta, r, s))
        subs_all.update(sub)
        m *= al*rho
        # next fresh core:
        cur0 = sp.Matrix([[xi,eta],[r,s]])
        # IMPORTANT: for lvl>0 the previous fresh core's symbols (xi{lvl-1}..) ARE cur0 of THIS round;
        # but factors[lvl+1] for lvl>0 refers to the ORIGINAL next factor which is the true C_{lvl+2}.
    # after the loop cur0 = final depth-1 fresh 2x2 [[xi_{depth-2}, ...]] ; blow up its corner
    alF,aF,bF,dlF = sp.symbols('alF aF bF dlF', real=True)
    subs_all.update(incidence_sub(cur0, alF,aF,bF,dlF))
    m *= alF

    # Apply ALL substitutions to P.  (They are on disjoint symbol sets across levels EXCEPT the fresh
    # core symbols xi{lvl},eta{lvl},r{lvl},s{lvl} which are consumed by the next level's incidence/shear;
    # apply iteratively to a fixed point.)
    Pc = P
    for _ in range(depth+2):
        Pc = sp.expand(Pc.subs(subs_all))
    Pc = sp.expand(Pc)

    # (subset) divisibility by m:
    div_ok = True
    U = sp.zeros(2,2)
    for i in range(2):
        for j in range(2):
            q, rem = sp.div(sp.expand(Pc[i,j]), sp.expand(m))
            # sp.div does multivariate division; use cancel to be safe
            qc = sp.cancel(Pc[i,j]/m)
            if not qc.is_polynomial():
                div_ok = False
            U[i,j] = sp.expand(qc)
    print(f"  extracted m = {m}")
    print(f"  (subset) every entry of (prod o chart) divisible by m ?  {div_ok}")

    # (supset) U[0,0] a unit at a generic exact-rational leaf:
    freesyms = sorted(U[0,0].free_symbols, key=str)
    import random; random.seed(7)
    # pick leaf where the blow-up coords are nonzero (units) and shear coords generic
    leaf = {}
    for sym in freesyms:
        name = str(sym)
        if name.startswith(('al','rho')):
            leaf[sym] = sp.Rational(random.randint(1,5))       # exceptional coords: nonzero (in-chart)
        else:
            leaf[sym] = sp.Rational(random.randint(-3,3), random.randint(1,3))
    val00 = sp.nsimplify(U[0,0].subs(leaf))
    print(f"  (supset) U[0,0] = {sp.simplify(U[0,0])}")
    print(f"           U[0,0] at a generic in-chart leaf = {val00}  (nonzero => UNIT) : {val00!=0}")
    # so <m> = <m*U[0,0]> subset <prod o chart> (U[0,0] invertible at leaf), and subset both ways:
    ideal_eq = div_ok and (val00 != 0)
    print(f"  => <prod C o chart> = <m>  (monomial ideal), EXACT both inclusions : {ideal_eq}")
    return m, U, ideal_eq

m3,U3,ok3 = build_and_check(3, "DEPTH 3  M=(2,2,2,2)")
print()
m2,U2,ok2 = build_and_check(2, "DEPTH 2  M=(2,2,2)")

print()
print("="*72); print("GROEBNER localized cross-check (depth 2, Rabinowitsch)"); print("="*72)
# Verify <prod C o chart> = <m> over k[coords, w]/(w*al0*alF*rho0 - 1)  (invert the leaf-units).
import sympy as sp
# rebuild depth-2 composed product entries and m2 already have them:
entries = [sp.expand(m2*U2[i,j]) for i in range(2) for j in range(2)]
w = sp.Symbol('w', real=True)
unit_prod = sp.Integer(1)
for g in sp.Mul.make_args(m2):
    unit_prod *= g
allvars = sorted(set().union(*[e.free_symbols for e in entries]) | {w}, key=str)
# Test <m2> subset <entries> in the localization: m2 in <entries, w*unit_prod-1> ?
gens_side = entries + [w*unit_prod - 1]
G = sp.groebner(gens_side, *allvars, order='grevlex')
red = G.reduce(m2)[1]
print(f"  m2 reduces to 0 mod <entries, w*units-1> ?  {sp.simplify(red)==0}   (=> <m2> subset <entries> locally)")
# Test each entry in <m2> (globally, since entries = m2*U, trivially divisible):
allok = all(sp.cancel(e/m2).is_polynomial() for e in entries)
print(f"  each entry divisible by m2 ?  {allok}   (=> <entries> subset <m2>)")
print(f"  => localized ideal equality confirmed by Groebner : {sp.simplify(red)==0 and allok}")

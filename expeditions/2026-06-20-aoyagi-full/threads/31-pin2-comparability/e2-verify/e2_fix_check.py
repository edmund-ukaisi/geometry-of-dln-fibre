import sympy as sp, random
random.seed(23)
# FIX CHECK: a Ψ that fixes the WHOLE raw flat product prod(symm x) EXCEPT it must change the absorbed
# Schur core (E1). Question: can a (T1,Y1)-only action fix BOTH P01 and P11 while satisfying E1?
# E1: T1' - Z1 A1^-1 Y1' = (1-K) S1.  Constraints to also fix Sreg under GENERAL frames:
#   P01 fixed: A0 Y1' + Y0 T1' = A0 Y1 + Y0 T1
#   P11 fixed: Z0 Y1' + T0 T1' = Z0 Y1 + T0 T1
# Two matrix eqns in (Y1',T1') + E1 (a third). Generically OVERDETERMINED. Check consistency at a point.
r,m0,mmid,mlast=1,1,2,1
def rnd(a,b): return sp.Matrix(a,b, lambda i,j: sp.Rational(random.randint(-3,3),random.choice([5,7])))
fails_consistency=0
for _ in range(5):
    X0=rnd(r,r);X1=rnd(r,r);Y0=rnd(r,mmid);Z0=rnd(m0,r);T0=rnd(m0,mmid)
    Z1=rnd(mmid,r);Y1=rnd(r,mlast);T1=rnd(mmid,mlast)
    A0=sp.eye(r)+X0;A1=sp.eye(r)+X1
    try: A0i=A0.inv();A1i=A1.inv();P00f=(A0*A1+Y0*Z1).inv()
    except: continue
    K=Z1*P00f*Y0; S1=T1-Z1*A1i*Y1
    # unknowns Y1' (r x mlast), T1' (mmid x mlast)
    Y1v=sp.Matrix(r,mlast, lambda i,j: sp.Symbol(f"yv_{i}_{j}"))
    T1v=sp.Matrix(mmid,mlast, lambda i,j: sp.Symbol(f"tv_{i}_{j}"))
    eqs=[]
    # E1
    for e in (T1v - Z1*A1i*Y1v - (sp.eye(mmid)-K)*S1): eqs.append(e)
    # P01 fixed
    for e in (A0*Y1v + Y0*T1v - (A0*Y1+Y0*T1)): eqs.append(e)
    # P11 fixed
    for e in (Z0*Y1v + T0*T1v - (Z0*Y1+T0*T1)): eqs.append(e)
    unknowns=list(Y1v)+list(T1v)
    sol=sp.linsolve(eqs, unknowns)
    if len(sol)==0: fails_consistency+=1
print(f"Fix-A (fix P01 AND P11 AND E1 with (T1,Y1)-only): inconsistent in {fails_consistency}/5 draws")
print("(#unknowns =", r*mlast+mmid*mlast, ", #eqns =", mmid*mlast + r*mlast + m0*mlast, ")")

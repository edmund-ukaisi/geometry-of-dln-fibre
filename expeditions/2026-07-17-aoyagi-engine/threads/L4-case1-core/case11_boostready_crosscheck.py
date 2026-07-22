import sympy as sp
u11,u12,beta,gamma = sp.symbols('u11 u12 beta gamma')
b00,b01,b10,b11 = sp.symbols('b00 b01 b10 b11')
z00,z01,z10,z11 = sp.symbols('z00 z01 z10 z11')
Delta = sp.symbols('Delta')
B = sp.Matrix([[b00,b01],[b10,b11]])
Z = sp.Matrix([[z00,z01],[z10,z11]])
C = (u12,b00,b10)
S = (b00,b01,b10,b11)
allvars = (u11,u12,beta,gamma,*S,z00,z01,z10,z11)
def degs(f, xs):
    return [sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms()]
def checks(R):
    fs = list(R)
    a1 = all(sp.expand(f).subs({x:0 for x in C}, simultaneous=True) == 0 for f in fs)
    a2 = all(max(degs(f,C), default=0) <= 1 for f in fs)
    pulled = [sp.expand(f.subs({b00:u12*b00,b10:u12*b10}, simultaneous=True)) for f in fs]
    a3 = all(sp.expand(f.subs(u12,0)) == 0 and bool(sp.cancel(f/u12).is_polynomial(*allvars)) for f in pulled)
    return a1,a2,a3
Qinv = sp.Matrix([[1,beta],[0,1]])
R1 = sp.expand(Z*B*sp.diag(1,Delta)*Qinv)
R_actual = sp.expand(R1.subs(Delta,u12))
R_literal = sp.expand(R1.subs(Delta,1))
R_bad = sp.expand(Z*B*sp.Matrix([[1,beta],[gamma,u12]]))
print('actual A1,A2,A3 =', checks(R_actual))
print('literal A1,A2,A3 =', checks(R_literal))
print('bad full-support degree sets =', [set(degs(f,S)) for f in list(R_bad)])
print('bad A1,A2,A3 =', checks(R_bad))
print('bad center-zero witness (entry 0,0) =', sp.expand(R_bad[0,0]).subs({x:0 for x in C}, simultaneous=True))
assert checks(R_actual) == (True,True,True), "actual not boost-ready!"
assert checks(R_bad)[0] is False, "R_bad unexpectedly boost-ready"
assert all(set(degs(f,S)) == {1} for f in list(R_bad)), "R_bad not full-support-deg1"
print("PASS: actual TTT; R_bad = full-support-Deg1 but NOT boost-ready (A1 False)")

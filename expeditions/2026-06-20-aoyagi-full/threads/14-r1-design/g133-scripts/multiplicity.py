"""
Attack (ii): MULTIPLICITY-2 UNDERSHOOT. Does any exceptional divisor have loss-multiplicity k_E >= 2?

Mechanism: in the pivot resolution, each blow-up introduces an exceptional coordinate u; along {u=0}
we measure ord_u(F) = the order of vanishing of F as a function of u (other coords generic). The
RLCT contribution of that divisor is (h+1)/(2k) where k = ord_u(F)/2  (since F = g^2, ord_u F = 2*ord_u g)
... careful: the 'loss multiplicity k_E' in the (h+1)/(2k) formula is k = ord_u(F)/2 only if F factors as
(monomial)^{2k} * unit. The TRAP is when F ~ u^{2k}*unit with k>=2, OR F ~ (smooth block)^2 giving an
even-order non-monomial divisor.

pp-claim: F = ||prod||^2 is MULTILINEAR => scaling ONE factor A^(s) by lambda scales prod by lambda, so
F by lambda^2 => ord exactly 2 in that factor's scaling. So along a blow-up that scales one factor's
entries by u, ord_u(F) = 2 exactly => k_E = 1.

I TEST the order of vanishing of F along the explicit pivot blow-up divisors, EXACTLY (sympy), on
asymmetric chains. The danger: a SECOND blow-up (nested) could make u divide MULTIPLE factors'
contributions, pushing ord_u(F) above 2.
"""
import sympy as sp

def chain_prod(mats):
    P = mats[0]
    for M in mats[1:]:
        P = P*M
    return P

def F_of(mats):
    P = chain_prod(mats)
    return sum(P[i,j]**2 for i in range(P.rows) for j in range(P.cols))

def mat(name, r, c):
    return sp.Matrix(r, c, lambda i,j: sp.symbols(f'{name}_{i}{j}', real=True))

def ord_along(F, allvars, scale_vars, extra_subs=None):
    """order of vanishing of F when scale_vars -> u*scale_vars (others generic), as function of u."""
    u = sp.symbols('u', positive=True)
    subs = {v: u*v for v in scale_vars}
    if extra_subs: subs.update(extra_subs)
    Fs = sp.expand(F.subs(subs))
    poly = sp.Poly(Fs, u)
    return poly.as_dict(), sp.simplify(Fs)

# ---- (3,1,3): A 3x1, B 1x3. prod = A*B, a 3x3 rank<=1 matrix. F=||AB||^2.
print("="*70)
print("(3,1,3): A 3x1, B 1x3, prod 3x3 rank<=1")
A = mat('a',3,1); B = mat('b',1,3)
F = F_of([A,B])
allv = list(A.free_symbols|B.free_symbols)
# Blow up scaling A by u (one factor). ord_u(F):
d,_ = ord_along(F, allv, list(A.free_symbols))
print("  scale A by u: F orders in u:", sorted(d.keys()))   # expect just {2}
# scale a SINGLE entry a_00 by u:
u=sp.symbols('u',positive=True)
Fs=sp.expand(F.subs({A[0,0]:u*A[0,0]}))
print("  scale entry a_00 by u: orders", sorted(sp.Poly(Fs,u).as_dict().keys()))
# nested: scale a_00 by u then within that chart scale b_00 by u (two nested pivots sharing u):
Fs2=sp.expand(F.subs({A[0,0]:u*A[0,0], B[0,0]:u*B[0,0]}))
print("  scale a_00 AND b_00 by SAME u (nested-shared): orders", sorted(sp.Poly(Fs2,u).as_dict().keys()))

# ---- (2,3,2): A 2x3, B 3x2, prod 2x2.
print("="*70)
print("(2,3,2): A 2x3, B 3x2, prod 2x2")
A = mat('a',2,3); B = mat('b',3,2)
F = F_of([A,B])
u=sp.symbols('u',positive=True)
Fs=sp.expand(F.subs({v:u*v for v in A.free_symbols}))
print("  scale ALL of A by u: orders", sorted(sp.Poly(Fs,u).as_dict().keys()))
Fs=sp.expand(F.subs({A[0,0]:u*A[0,0]}))
print("  scale entry a_00 by u: orders", sorted(sp.Poly(Fs,u).as_dict().keys()))

# ---- depth-4 (2,2,2,2): A,B,C each 2x2.
print("="*70)
print("(2,2,2,2): A,B,C 2x2 each, prod 2x2")
A=mat('a',2,2);B=mat('b',2,2);C=mat('c',2,2)
F=F_of([A,B,C])
u=sp.symbols('u',positive=True)
for label,subs in [
    ("scale A by u", {v:u*v for v in A.free_symbols}),
    ("scale A and B by SAME u", {**{v:u*v for v in A.free_symbols},**{v:u*v for v in B.free_symbols}}),
    ("scale A,B,C all by SAME u", {**{v:u*v for v in A.free_symbols},**{v:u*v for v in B.free_symbols},**{v:u*v for v in C.free_symbols}}),
    ("scale entry a_00 by u", {A[0,0]:u*A[0,0]}),
]:
    Fs=sp.expand(F.subs(subs))
    print(f"  {label}: orders", sorted(sp.Poly(Fs,u).as_dict().keys()))

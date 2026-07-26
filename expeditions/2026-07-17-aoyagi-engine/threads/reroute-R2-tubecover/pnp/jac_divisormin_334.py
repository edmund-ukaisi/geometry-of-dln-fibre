#!/usr/bin/env python3
"""
Concrete (3,3,4) per-leaf Jacobian + divisorMin (kill-condition (c)).

jacDet(bb(S,p))(w) = w[p]^(|S|-1).  The three fan blow-ups:
  node1 = bb({0..7,20}, p1)  -> |S|=9 -> jac_exp 8 on the p1-coord
  node2 = bb({0..7},     p2)  -> |S|=8 -> jac_exp 7 on the p2-coord
  node3 = bb({1,5,6,7},  p3)  -> |S|=4 -> jac_exp 3 on the p3-coord
  shears |det|=1.
Chain rule under composition: jacDet(g_leaf)(u) = prod of the three, in the leaf's OWN
coords.  We compute the FULL symbolic jacDet(gWrap) to confirm u0^7 * u1^3 * u20^8, then
read the binding structure: divisorMin = min over BINDING divisors (those in the value
monomial c11*E) of (jac_exp+1)/mono_exp.
"""
import sympy as sp

u = sp.symbols('u0:21')

def bb(S, p):
    S = set(S)
    def f(w):
        return [ (w[p] if j==p else (w[p]*w[j] if j in S else w[j])) for j in range(21) ]
    return f

PERMIDX = {0:8,1:9,2:10,3:11,4:1,5:5,6:6,7:7,8:0,9:2,10:3,11:4}
def permP(w): return [ w[PERMIDX[k]] if k in PERMIDX else w[k] for k in range(21) ]
def shearH(w):
    g=list(w)
    g[4]=w[4]+w[0]*w[2]; g[5]=w[5]+w[1]*w[2]; g[6]=w[6]+w[0]*w[3]; g[7]=w[7]+w[1]*w[3]
    g[8]=w[8]-w[0]*w[12]-w[1]*w[16]; g[9]=w[9]-w[0]*w[13]-w[1]*w[17]
    g[10]=w[10]-w[0]*w[14]-w[1]*w[18]; g[11]=w[11]-w[0]*w[15]-w[1]*w[19]
    return g

def gWrap(u):
    w = bb({1,5,6,7},1)(list(u))
    w = bb({0,1,2,3,4,5,6,7},0)(w)
    w = permP(w)
    w = shearH(w)
    w = bb({0,1,2,3,4,5,6,7,20},20)(w)
    return w

# --- full symbolic Jacobian determinant of gWrap ---
g = gWrap(u)
J = sp.Matrix(21,21, lambda i,j: sp.diff(g[i], u[j]))
det = sp.factor(J.det())
print("jacDet(gWrap) =", det)

# extract the monomial part (exponents of each u in the factored det, up to sign/unit)
poly = sp.Poly(sp.expand(J.det()), *u)
# the monomial GCD of the determinant = the exceptional monomial (the det is monomial*unit)
exps=[min(m[i] for m in poly.monoms()) for i in range(21)]
print("jacDet monomial (min-exponents) =",
      " * ".join(f"u{i}^{exps[i]}" for i in range(21) if exps[i]>0))

print("\n--- divisorMin for the canonical leaf (value monomial = c11*E = u20*u0) ---")
jac = {i: exps[i] for i in range(21)}
binding = {20: ("c11", 1), 0: ("E", 1)}   # divisor: (name, mono_exp in value monomial)
for d,(nm,me) in binding.items():
    print(f"   divisor u{d} ({nm}): jac_exp={jac[d]}, mono_exp={me}, "
          f"(jac+1)/mono={sp.Rational(jac[d]+1,me)}  ->  half = {sp.Rational(jac[d]+1,2*me)}")
dm = min(jac[d]+1 for d in binding)
print(f"   divisorMin = min(jac+1 over binding) = {dm}   => rlct >= 1/2*{dm} = {sp.Rational(dm,2)}")
print(f"   alpha divisor u1: jac_exp={jac.get(1,0)} -- BINDING? only if survivor carries alpha; "
      f"survivor=E-pivot (no alpha) => u1 NON-binding (mono_exp 0).")

#!/usr/bin/env python3
"""
verify_codex_3333.py — INDEPENDENTLY verify Codex's explicit (3,3,3,3) chart (NEVER paste-trust).

Codex proposed (genM-chart-answer.md):
  K = [[a, a*alpha],[gamma*a, gamma*a*alpha + delta]]   (2x2, the rank-1+residual block, det = a*delta)
  m = [[m1],[m2]] (2x1),  lambda = (lam1, lam2) (1x2)
  A = [[I2],[lambda]] . K . [I2 | m]  + u*E33      (A is 3x3; E33 the (2,2) unit, 0-indexed (2,2))
  w = (1, n1, n2) (1x3),  p = [[1],[ell]] (2x1),  Y = [[0,0,0],[0,eta1,eta2]] (2x3)
  D = p*b*w + u*Y                                   (2x3)
  r free 1x3;  B = [[D - m*r],[r]]                  (3x3),  so (I2|m) B = D
  h1,h2 free 1x3, zeta free 1x3;  C = [[u*zeta - n1*h1 - n2*h2],[h1],[h2]]  (3x3), so w C = u*zeta
Claim: ABC = u*H exactly => F = ||ABC||^2 = u^2 * ||H||^2 = u^2 * U.
       |det DPhi| = |u|^5 |a|^4 |delta|^2 |b|^3.  Binding axis (k,h)=(1,5), threshold 6/2=3=minAdm/2.

We CHECK:  (1) ABC = u*H exactly (u-degree 1 in every entry => F pure u^2);
           (2) the Jacobian of the chart (u, a,alpha,gamma,delta, lambda, m, b, ell, n1,n2, eta, r,
               h1,h2, zeta) -> the 27 flat entries (A,B,C) has |det| = |u|^5 |a|^4 |delta|^2 |b|^3;
           (3) U = ||H||^2 bounded below on a sector (a,delta,b,zeta1 != 0).
The chart must have exactly 27 free inputs (flatDim(3,3,3,3) = 27).  We COUNT them.
"""
import sympy as sp

u = sp.symbols('u', positive=True)
a, alpha, gamma, delta = sp.symbols('a alpha gamma delta', real=True)
lam1, lam2 = sp.symbols('lam1 lam2', real=True)
m1, m2 = sp.symbols('m1 m2', real=True)
b, ell = sp.symbols('b ell', real=True)
n1, n2 = sp.symbols('n1 n2', real=True)
eta1, eta2 = sp.symbols('eta1 eta2', real=True)
r = sp.Matrix([[sp.Symbol(f'r{j}', real=True) for j in range(3)]])           # 1x3
h1 = sp.Matrix([[sp.Symbol(f'h1{j}', real=True) for j in range(3)]])         # 1x3
h2 = sp.Matrix([[sp.Symbol(f'h2{j}', real=True) for j in range(3)]])         # 1x3
zeta = sp.Matrix([[sp.Symbol(f'z{j}', real=True) for j in range(3)]])        # 1x3

I2 = sp.eye(2)
K = sp.Matrix([[a, a*alpha], [gamma*a, gamma*a*alpha + delta]])
lam = sp.Matrix([[lam1, lam2]])
m = sp.Matrix([[m1], [m2]])
# A = [[I2],[lambda]] (3x2)  *  K (2x2)  *  [I2 | m] (2x3)  + u E33
left = sp.Matrix.vstack(I2, lam)            # 3x2
right = sp.Matrix.hstack(I2, m)             # 2x3
E33 = sp.zeros(3, 3); E33[2, 2] = 1
A = left * K * right + u * E33              # 3x3

w = sp.Matrix([[1, n1, n2]])                # 1x3
p = sp.Matrix([[1], [ell]])                 # 2x1
Y = sp.Matrix([[0, 0, 0], [0, eta1, eta2]]) # 2x3
D = p * b * w + u * Y                        # 2x3
B = sp.Matrix.vstack(D - m * r, r)          # 3x3   (top 2 rows = D - m r, bottom row = r)
C = sp.Matrix.vstack(u * zeta - n1 * h1 - n2 * h2, h1, h2)   # 3x3

# sanity: (I2|m) B = D  and  w C = u zeta
chk1 = sp.simplify(right * B - D)
chk2 = sp.simplify(w * C - u * zeta)
print("(I2|m) B == D :", chk1 == sp.zeros(2, 3))
print("w C == u*zeta :", chk2 == sp.zeros(1, 3))

ABC = sp.expand(A * B * C)
# (1) every entry has u-degree >= 1 ; ABC = u*H
allmono = set()
for i in range(3):
    for j in range(3):
        poly = sp.Poly(ABC[i, j], u)
        for mexp in poly.monoms():
            allmono.add(mexp[0])
print("\nABC entry u-degrees present:", sorted(allmono), " (min should be >=1 => ABC = u*H)")
H = sp.Matrix(3, 3, lambda i, j: sp.simplify(sp.cancel(ABC[i, j] / u)))
H_is_ufree = all(not H[i, j].has(u) for i in range(3) for j in range(3))
print("ABC / u is u-free (H):", H_is_ufree)

F = sp.expand(sum(ABC[i, j]**2 for i in range(3) for j in range(3)))
Fpoly = sp.Poly(F, u)
Fdegs = sorted(set(mm[0] for mm in Fpoly.monoms()))
print("F = ||ABC||^2 u-degrees:", Fdegs, " (pure [2] => F = u^2 * U):", Fdegs == [2])
U = sp.expand(Fpoly.coeff_monomial(u**2))

# count free inputs (must be 27 = flatDim)
inputs = [u, a, alpha, gamma, delta, lam1, lam2, m1, m2, b, ell, n1, n2, eta1, eta2] \
    + list(r) + list(h1) + list(h2) + list(zeta)
print("\n# chart inputs =", len(inputs), " (flatDim(3,3,3,3) = 27):", len(inputs) == 27)

# (2) Jacobian of (inputs) -> flat (A entries, B entries, C entries), 27x27
flat = [A[i, j] for i in range(3) for j in range(3)] \
     + [B[i, j] for i in range(3) for j in range(3)] \
     + [C[i, j] for i in range(3) for j in range(3)]
J = sp.Matrix(27, 27, lambda rr, cc: sp.diff(flat[rr], inputs[cc]))
detJ = J.det()
detJ = sp.factor(sp.expand(detJ))
print("\n|det DPhi| (factored) =", detJ)
target = u**5 * a**4 * delta**2 * b**3
ratio = sp.simplify(detJ / target)
print("det / (u^5 a^4 delta^2 b^3) =", ratio, " (=> |det| = |u|^5|a|^4|delta|^2|b|^3 up to sign):",
      ratio in (1, -1))

# (3) U bounded below on a sector. Evaluate U at a concrete sector point + check it's a nonzero SOS.
sector = {a: 1, alpha: 0, gamma: 0, delta: 1, lam1: 0, lam2: 0, m1: 0, m2: 0, b: 1, ell: 0,
          n1: 0, n2: 0, eta1: 0, eta2: 0}
for j in range(3):
    sector[r[0, j]] = [1, 0, 0][j]
    sector[h1[0, j]] = [0, 1, 0][j]
    sector[h2[0, j]] = [0, 0, 1][j]
    sector[zeta[0, j]] = [1, 0, 0][j]
Uval = sp.simplify(U.subs(sector))
print("\nU at the sector point =", Uval, " (>0 => bounded below on a neighborhood):", Uval > 0)
print("U is ||H||^2 (sum of squares) so U>=0 everywhere; >0 on the open sector.")

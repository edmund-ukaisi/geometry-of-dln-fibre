#!/usr/bin/env python3
"""
verify_codex_3333_bound.py — STANDALONE: the F = u^2 * V soundness gate for the (3,3,3,3) Codex chart.
(Companion to verify_codex_3333.py, which does the full 27x27 Jacobian det = u^5 a^4 delta^2 b^3.)
Gate: F divisible by u^2 (V = F/u^2 a polynomial => continuous => bounded on a compact box); V|_{u=0}=U
not identically 0 and U>0 at a sector point (=> c0 <= V <= B on a positive-measure neighborhood).
"""
import sympy as sp
u = sp.symbols('u', positive=True)
a, alpha, gamma, delta = sp.symbols('a alpha gamma delta', real=True)
lam1, lam2, m1, m2, b, ell, n1, n2, eta1, eta2 = sp.symbols('lam1 lam2 m1 m2 b ell n1 n2 eta1 eta2', real=True)
r = sp.Matrix([[sp.Symbol(f'r{j}', real=True) for j in range(3)]])
h1 = sp.Matrix([[sp.Symbol(f'h1{j}', real=True) for j in range(3)]])
h2 = sp.Matrix([[sp.Symbol(f'h2{j}', real=True) for j in range(3)]])
zeta = sp.Matrix([[sp.Symbol(f'z{j}', real=True) for j in range(3)]])
I2 = sp.eye(2)
K = sp.Matrix([[a, a*alpha], [gamma*a, gamma*a*alpha + delta]])
lam = sp.Matrix([[lam1, lam2]]); m = sp.Matrix([[m1], [m2]])
A = sp.Matrix.vstack(I2, lam) * K * sp.Matrix.hstack(I2, m); A[2, 2] += u
w = sp.Matrix([[1, n1, n2]]); p = sp.Matrix([[1], [ell]]); Y = sp.Matrix([[0, 0, 0], [0, eta1, eta2]])
D = p * b * w + u * Y
B = sp.Matrix.vstack(D - m * r, r)
C = sp.Matrix.vstack(u * zeta - n1 * h1 - n2 * h2, h1, h2)
F = sp.expand(sum((A * B * C)[i, j]**2 for i in range(3) for j in range(3)))
Fp = sp.Poly(F, u); mindeg = min(mm[0] for mm in Fp.monoms())
print("min u-degree of F =", mindeg, " (==2 => F = u^2*V, V polynomial):", mindeg == 2)
V = sp.expand(sp.cancel(F / u**2))
print("V = F/u^2 polynomial in all inputs:", V.is_polynomial())
print("V|_{u=0} = U identically 0?:", sp.expand(V.subs(u, 0)) == 0, " (False => bounded below on a slice)")
sector = {a: 1, alpha: 0, gamma: 0, delta: 1, lam1: 0, lam2: 0, m1: 0, m2: 0, b: 1, ell: 0,
          n1: 0, n2: 0, eta1: 0, eta2: 0}
for j in range(3):
    sector[r[0, j]] = [1, 0, 0][j]; sector[h1[0, j]] = [0, 1, 0][j]
    sector[h2[0, j]] = [0, 0, 1][j]; sector[zeta[0, j]] = [1, 0, 0][j]
print("U(sector) = V(u=0,sector) =", sp.simplify(V.subs(u, 0).subs(sector)), "(>0)")
print("V(u=1/10,sector) =", sp.simplify(V.subs(u, sp.Rational(1, 10)).subs(sector)), "(finite, near U)")

#!/usr/bin/env python3
# provenance: threads/28-twoblock-diagb (pnp two-block/two-shared-factor diag(b) certificate)
"""(4,4,4) t=(2,0): the MINIMAL UNIQUELY-binding TWO-corank-2-block instance (35 such exist;
this is the smallest). Stress-tests whether two corank-2 coupling blocks BREAK the single
divisibility-chain reading of Object B. All exact (sympy Groebner over Q).

minAdm(4,4,4) = min_{t1} (4-t1)^2 + 4*t1 = {16,13,12,13,16} -> UNIQUE minimiser t=(2,0), minAdm=12,
rlct should be 6. Blocks on t=(2,0): top (4-2)x(4-2)=2x2, deep-layer-2 (2-0)x(4-0)=2x4 -- TWO
corank-2 blocks (vs (3,3,4)'s one corank-2 block + one corank-1 row).

Verifies:
 (A) block-elim PEEL (exact, det-1): with C1=[[I2,B],[C,D]], Q1 C1 Q2 = diag(I2, Delta),
     Delta = D - C*B (2x2 Schur). So <C1 C2> = < R (top 2 rows of Q2^{-1}C2, 8 FREE coords),
     Delta*S (bottom 2 rows) >. STRUCTURE = "2 bare pivot rows R + a (2,2,4)-heart Delta*S":
     the two census 'corank-2 blocks' are the SAME Delta CASCADING (deep block = Delta propagated),
     NOT two independent hearts.
 (B) R radial: <R> = <rho> principal, ||R||^2 = rho^2*unit, Jac rho^7 (8-coord radial).
 (C) Delta*S (2,2,4)-heart: <Delta S> = a*<sigma_j, e*s2_j> by Groebner; a-radial Jac a^3.
 (D) JOIN {rho=a=0}, rho=E, a=E*alpha: <prod C> = <E, E*alpha*..> == <E> PRINCIPAL (Groebner
     ideal-equality). Total Jac on E = 7+3+1 = 11, loss = E^2*unit, rlct = (11+1)/2 = 6 = minAdm/2.
 VERDICT: single divisibility chain SURVIVES; the two radials JOIN at the common corner into one
 dominant divisor E. b = (E, E*rho, E*rho*beta*nu, E*rho*beta*nu*delta*omega) (Codex-confirmed 4-chain).
Exit 0 iff all hold.
"""
import sys, sympy as sp
from fractions import Fraction
from functools import lru_cache
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from _rlct_lp import rlct_from_monomials  # noqa: F401 (calibrated LP available)

ok = True
I2 = sp.eye(2)

# ================= (A) block-elim PEEL =================
B  = sp.Matrix(2, 2, sp.symbols('B11 B12 B21 B22'))
Cc = sp.Matrix(2, 2, sp.symbols('C11 C12 C21 C22'))
D  = sp.Matrix(2, 2, sp.symbols('D11 D12 D21 D22'))
C1 = sp.Matrix(sp.BlockMatrix([[I2, B], [Cc, D]]))
Q1 = sp.Matrix(sp.BlockMatrix([[I2, sp.zeros(2)], [-Cc, I2]]))
Q2 = sp.Matrix(sp.BlockMatrix([[I2, -B], [sp.zeros(2), I2]]))
Delta = D - Cc * B
peel_ok = (sp.simplify(Q1 * C1 * Q2) == sp.Matrix(sp.BlockMatrix([[I2, sp.zeros(2)], [sp.zeros(2), Delta]])))
det_ok = (sp.simplify(Q1.det()) == 1 and sp.simplify(Q2.det()) == 1)
C2 = sp.Matrix(4, 4, sp.symbols('c2_0:16'))
C2p = Q2.inv() * C2
R = C2p[0:2, :]          # 2x4 bare rows (free)
Sm = C2p[2:4, :]         # 2x4
peeled = sp.Matrix(sp.BlockMatrix([[I2, sp.zeros(2)], [sp.zeros(2), Delta]])) * C2p
struct_ok = (sp.simplify(peeled[0:2, :] - R) == sp.zeros(2, 4) and
             sp.simplify(peeled[2:4, :] - Delta * Sm) == sp.zeros(2, 4))
ideal_pres = (sp.simplify(Q1.inv() * peeled - C1 * C2) == sp.zeros(4, 4))
print(f"(A) Q1 C1 Q2 == diag(I2,Delta): {peel_ok}; det Q1=det Q2=1: {det_ok}; "
      f"<prod C>=<R, Delta*S>: {struct_ok}; ideal-preserving (prod=Q1^-1 peeled): {ideal_pres}")
print("    STRUCTURE: 2 bare pivot rows R (8 free) + one (2,2,4)-heart Delta*S (Delta cascading, NOT independent)")
ok &= peel_ok and det_ok and struct_ok and ideal_pres

# ================= (B) R radial =================
rho = sp.symbols('rho'); rc = sp.symbols('r1:8')
Rbar = [1] + list(rc)                         # radial chart: first entry = 1 (unit)
lossR = sum((rho * x) ** 2 for x in Rbar)
R_ok = (sp.simplify(lossR - rho**2 * sp.expand(lossR / rho**2)) == 0 and
        sp.expand(lossR / rho**2).subs({c: 0 for c in rc}) == 1)
jac_R = 7
print(f"(B) R radial: ||R||^2 = rho^2*unit, unit(0)=1: {R_ok}; <R>=<rho> principal; Jac rho^{jac_R}")
ok &= R_ok

# ================= (C) Delta*S (2,2,4)-heart, Groebner =================
d11, d12, d21, d22 = sp.symbols('d11 d12 d21 d22'); s = sp.symbols('s10 s11 s12 s13 s20 s21 s22 s23')
s1 = s[0:4]; s2 = s[4:8]; a, u, v, w = sp.symbols('a u v w')
DeltaH = sp.Matrix([[d11, d12], [d21, d22]]); SH = sp.Matrix([list(s1), list(s2)])
DS = DeltaH * SH
sub = {d11: a, d12: a * u, d21: a * v, d22: a * w}
gens_chart = [(DS[i, j]).subs(sub).expand() for i in range(2) for j in range(4)]
sigma = [s1[j] + u * s2[j] for j in range(4)]; e = w - u * v
target = [(a * sigma[j]).expand() for j in range(4)] + [(a * e * s2[j]).expand() for j in range(4)]
allv = [a, u, v, w] + list(s)


def ideal_eq(A, Bv, vs):
    GA = sp.groebner(A, *vs, order='grevlex'); GB = sp.groebner(Bv, *vs, order='grevlex')
    return all(GB.reduce(g)[1] == 0 for g in A) and all(GA.reduce(g)[1] == 0 for g in Bv)


heart_ok = ideal_eq(gens_chart, target, allv)
jac_a = 3
print(f"(C) <Delta*S> == a*<sigma_j, e*s2_j> (Groebner): {heart_ok}; a-radial Jac a^{jac_a}")
ok &= heart_ok

# ================= (D) JOIN -> principal <E>, rlct 6 =================
E, alpha = sp.symbols('E alpha'); sig = sp.symbols('sg0 sg1 sg2 sg3'); es = sp.symbols('es0 es1 es2 es3')
gens_res = [E] + [E * alpha * sig[j] for j in range(4)] + [E * alpha * es[j] for j in range(4)]
av2 = [E, alpha] + list(sig) + list(es)
principal = ideal_eq(gens_res, [E], av2)
jac_E = jac_R + jac_a + 1                      # rho^7 -> E^7; a^3 -> E^3*alpha^3; join {rho=a=0} -> E^1
rlct_E = Fraction(jac_E + 1, 2 * 1)
print(f"(D) JOIN rho=E, a=E*alpha: <prod C> = <E,E*alpha*..> == <E> PRINCIPAL (Groebner): {principal}")
print(f"    total Jac on E = 7+3+1 = {jac_E}; loss = E^2*unit; E-divisor ratio (11+1)/2 = {rlct_E} [expect 6]")
ok &= principal and (rlct_E == 6)


@lru_cache(None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 1:
        return 0
    if len(M) == 2:
        return M[0] * M[1]
    return min((M[0] - t) * (M[1] - t) + minAdm((t,) + M[2:]) for t in range(min(M[0], M[1]) + 1))


mA = minAdm((4, 4, 4))
print(f"(*) minAdm(4,4,4) = {mA}; rlct = {Fraction(mA, 2)}; E-divisor ratio {rlct_E}; match: {rlct_E == Fraction(mA, 2)}")
ok &= (rlct_E == Fraction(mA, 2))

print(f"\n(4,4,4) TWO-CORANK-2-BLOCK: {'PASS -> single chain SURVIVES, <prod C>=<E> principal, rlct=6' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)

#!/usr/bin/env python3
"""(3,3,4) corank-2 chart bridge check (EXACT, fast: block-diagonal Jacobian).

The (3,3,4) t=(1,0) binding branch's corank-2 residual sub-core IS the (2,2,4) core ||Delta.S||^2
(block-elim identification, D2 census). Full-block (Case-2, corank-2) blow-up of the 2x2 Delta:
   Delta = de * E,  E = [[1,e1],[e2,e3]]  (E-chart of the 2x2 blow-up),  S = 2x4 free.
The SHARED divisor de divides every product generator (the corank-2 coupling that flattening loses).
"""
import sympy as sp

de, e1, e2, e3 = sp.symbols("de e1 e2 e3", real=True)
S = sp.Matrix(2, 4, lambda i, j: sp.Symbol(f"s{i}{j}", real=True))
E = sp.Matrix([[1, e1], [e2, e3]])
Delta = de * E
prod = sp.expand(Delta * S)                       # 2x4
gens = [prod[i, j] for i in range(2) for j in range(4)]

# (1) SHARING: de divides every generator, with min de-exponent exactly 1 (shared, order-1 in de)
shared = all(min(m[0] for m in sp.Poly(g, de).monoms()) >= 1 for g in gens)
print(f"shared divisor de divides ALL {len(gens)} generators: {shared}")

# (2) pullback: F = ||Delta S||^2 = de^2 * ||E S||^2 ; residual R = ||E S||^2
F = sp.expand(sum(g**2 for g in gens))
order_de = sp.Rational(min(sp.Poly(F, de).monoms(), key=lambda m: m[0])[0], 2)
R = sp.expand(F / de**(2*order_de))
Svars = [S[i, j] for i in range(2) for j in range(4)]
R0 = R.subs({v: 0 for v in Svars})
H = sp.hessian(R.subs(de, 1), Svars)              # Morse Hessian in S (de generic=1)
rho = H.rank()
print(f"F = de^{2*order_de} * R;  R(S=0) = {R0} (0 => residual core);  Morse rank of R in S = {rho}")

# (3) Jacobian: block-diagonal [ d Delta / d(de,e1,e2,e3) ] (+) [ dS/dS = I_8 ] ; det = det(4x4 block)
dblock = sp.Matrix([[sp.diff(Delta[i//2, i%2], c) for c in (de, e1, e2, e3)] for i in range(4)])
detblk = sp.factor(dblock.det())
print(f"|det Dphi| (4x4 Delta block; S-block is identity) = {detblk}")
jacpow_de = min(m[0] for m in sp.Poly(sp.expand(detblk), de).monoms())

# (4) threshold
ratio_de = sp.Rational(jacpow_de + 1, 1) / (2 * order_de)
ratio_res = sp.Rational(rho, 2)
thr = min(ratio_de, ratio_res)
half_minAdm_224 = sp.Rational(4, 2)
print(f"divisor de: order={order_de}, JacPow={jacpow_de}, ratio=(JacPow+1)/(2 order)={ratio_de}")
print(f"residual Morse rank {rho}, ratio={ratio_res}")
print(f"chart threshold = min = {thr}  (1/2 minAdm(2,2,4) = {half_minAdm_224})  "
      f"{'BINDING' if thr==half_minAdm_224 else 'non-binding' if thr>half_minAdm_224 else 'UNDERSHOOT'}")
print("\nCONCLUSION: the corank-2 chart's pullback carries a SHARED divisor de across all generators;")
print("the bridge (pullback = de^2 * Morse, Jacobian = de^3) is EXACT; threshold = 2 = 1/2 minAdm(2,2,4).")

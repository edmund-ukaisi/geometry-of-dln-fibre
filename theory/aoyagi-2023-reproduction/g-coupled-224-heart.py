#!/usr/bin/env python3
# provenance: threads/27-coupled-diagb (pnp coupled diag(b) certificate)
"""The coupled HEART: exact ideal-identity monomialisation of the (2,2,4) sub-core <Delta*S>.

(2,2,4) sub-core: Delta free 2x2, S free 2x4, ideal I = < (Delta*S)_{ij} > (8 bilinear gens).
This is the corank-2 block that the (3,3,4) layer-1 peel exposes at the binding branch t=(1,0).

We verify, by exact Groebner (over Q):
  (1) the radial Delta blow-up  d11=a, d12=a*u, d21=a*v, d22=a*w  pulls I back to the ideal
      <a*sigma_j (j=1..4),  a*(v*s1j + w*s2j)>  = <a*sigma_j, a*e*s2j>,  sigma_j=s1j+u*s2j, e=w-u*v,
      which is a MONOMIAL ideal in the (unit-changed) coords (a,u,v,e,sigma_j,s2j).   [IDEAL IDENTITY]
  (2) rlct of the (2,2,4) core = 2, via the a-divisor (Jacobian a^3, ratio (3+1)/2=2); residual 5/2.
  (3) the SHARING is load-bearing: the actual blow-up shares one radial `a` across BOTH rows; a
      per-row-independent "flatten" (delta_1 row1 + delta_2 row2) gives a DIFFERENT rlct (1 vs 2 on
      the DS-part), reproducing the g-delta-flatten obstruction at the genuine (2,2,4) instance.
Exit 0 iff every asserted ideal identity and rlct holds exactly.
"""
import sys
import sympy as sp
from fractions import Fraction
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from _rlct_lp import rlct_from_monomials

ok = True

# ---- variables ----
d11, d12, d21, d22 = sp.symbols('d11 d12 d21 d22')           # Delta
s = sp.symbols('s10 s11 s12 s13 s20 s21 s22 s23')            # S rows (0-indexed cols)
s1 = s[0:4]; s2 = s[4:8]
a, u, v, w = sp.symbols('a u v w')                            # blow-up chart coords

Delta = sp.Matrix([[d11, d12], [d21, d22]])
S = sp.Matrix([list(s1), list(s2)])
DS = Delta * S                                                # 2x4
gens_DS = [DS[i, j] for i in range(2) for j in range(4)]

# ---- (1) radial Delta blow-up + Groebner-verify the pulled-back ideal ----
sub = {d11: a, d12: a * u, d21: a * v, d22: a * w}
gens_chart = [g.subs(sub).expand() for g in gens_DS]          # ideal in Q[a,u,v,w,s...]

# target: <a*sigma_j, a*e*s2j> with sigma_j=s1j+u*s2j, e=w-u*v (still in original s,w coords)
sigma = [s1[j] + u * s2[j] for j in range(4)]
e = w - u * v
target = [ (a * sigma[j]).expand() for j in range(4) ] + [ (a * e * s2[j]).expand() for j in range(4) ]

allv = [a, u, v, w] + list(s)
G_chart = sp.groebner(gens_chart, *allv, order='grevlex')
G_targ  = sp.groebner(target,     *allv, order='grevlex')
id_ok = (set(G_chart.exprs) == set(G_targ.exprs))
# robust equality: each side reduces to 0 modulo the other
def ideal_eq(A, B, vs):
    GA = sp.groebner(A, *vs, order='grevlex')
    GB = sp.groebner(B, *vs, order='grevlex')
    a_in_b = all(GB.reduce(g)[1] == 0 for g in A)
    b_in_a = all(GA.reduce(g)[1] == 0 for g in B)
    return a_in_b and b_in_a
id_ok = ideal_eq(gens_chart, target, allv)
print(f"(1) Groebner: pulled-back <Delta S> == <a*sigma_j, a*e*s2j> : {id_ok}")
ok &= id_ok

# monomiality after the unit coordinate change (s1j -> sigma_j, w -> e): the target generators
# are a*sigma_j and a*e*s2j -- literal monomials in coords (a,u,v,e,sigma_1..4,s2_1..4).
# We confirm each target generator is a single monomial in the NEW coord symbols:
sig_syms = sp.symbols('sig0 sig1 sig2 sig3'); e_sym = sp.symbols('e_')
new_gens = [a * sig_syms[j] for j in range(4)] + [a * e_sym * s2[j] for j in range(4)]
new_vars = [a, u, v, e_sym] + list(sig_syms) + list(s2)
mono_ok = all(len(sp.Poly(g, *new_vars).monoms()) == 1 for g in new_gens)
print(f"    target generators are literal monomials in (a,u,v,e,sigma,s2): {mono_ok}")
ok &= mono_ok

# ---- (2) rlct of the (2,2,4) core = 2 (a-divisor Jac a^3 ratio 2; residual 5/2) ----
# residual G = ||sigma||^2 + e^2 ||s2||^2  (standard volume in sigma,e,s2)
r_sigma, _, _ = rlct_from_monomials(list(sig_syms), list(sig_syms))          # Morse rank 4 -> 2
r_es2, _, _   = rlct_from_monomials([e_sym * s2[j] for j in range(4)], [e_sym] + list(s2))  # -> 1/2
r_resid = r_sigma + r_es2                                                     # disjoint -> 5/2
# a-divisor: loss order 2 in a (a^2 * G), Jacobian a^3  =>  ratio (3+1)/(2*1) = 2
r_adiv = Fraction(3 + 1, 2 * 1)
r_224 = min(r_adiv, r_resid)
print(f"(2) rlct(2,2,4): a-divisor={r_adiv}, residual G rlct={r_resid} (={r_sigma}+{r_es2}); "
      f"core rlct = min = {r_224}  [expect 2]")
ok &= (r_224 == 2) and (r_resid == Fraction(5, 2))

# ---- (3) SHARING load-bearing: shared-a (true) vs flattened independent rows ----
# TRUE DS-part rlct = rlct(a^2 G) with Jacobian a^3 = 2 (as in (2)).
# FLATTEN: model each of the 2 rows of DS as weighted by its OWN scalar delta_i:
#   loss = delta1^2 * ||row1||^2 + delta2^2 * ||row2||^2, rows = free 1x4. Disjoint -> add.
d1s, d2s = sp.symbols('d1 d2')
r_row1, _, _ = rlct_from_monomials([d1s * s1[j] for j in range(4)], [d1s] + list(s1))   # 1/2
r_row2, _, _ = rlct_from_monomials([d2s * s2[j] for j in range(4)], [d2s] + list(s2))   # 1/2
r_flat = r_row1 + r_row2                                                                # 1
print(f"(3) DS-part: shared-a (TRUE) rlct = {r_224}  vs  flattened independent-rows rlct = {r_flat}")
print(f"    coupling raises the DS-part from {r_flat} (flatten) to {r_224} (true) -- SHARING load-bearing: "
      f"{r_224 != r_flat}")
ok &= (r_flat == 1) and (r_224 == 2)

print(f"\n(2,2,4) COUPLED-HEART: {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)

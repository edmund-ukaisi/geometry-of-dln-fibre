#!/usr/bin/env python3
"""
Vzero_recursion.py — does the {V=0} recursion terminate at S2-only or Morse-S2-free leaves?

DECISIVE hero-task gate. The corank-2 cell's unit Uval VANISHES on {V=0}. We resolve {V=0} RECURSIVELY
(iterated coupled diag(b)/radial peel) and ask: do the TERMINAL leaves fall into
  (S2)      a product monomial prod x_i^{2k_i} (handled by monomial_rlct), OR
  (S2-FREE) a Euclidean sum-of-squares ||x||^2 (handled by Mathlib radial_ball_iff,
            as Case222CoverGETail.euclid4_ball_integrable ALREADY does, NO S2)?
If every leaf is one of these, the recursion is S2-only-feasible (in fact mostly S2-FREE at the leaves;
S2 only enters where a genuine product-monomial divisor appears). If a leaf is a HIGHER determinantal
core that neither resolves to a monomial nor to a clean Morse sum, we'd need a non-S2 cite.

KEY HARNESS FACT (verified by reading Case222CoverGETail): the existing (2,2,2) cover terminates at
4-D Euclidean sum-of-squares leaves (sumSq4_box_lt_top via euclid4_ball_integrable) -- S2-FREE radial
integration. So Morse leaves are ALREADY a from-scratch terminal. The resolution need NOT reach pure
monomials; Morse-quadratic leaves suffice.

We trace the (2,2,4) core G = ||Delta S||^2 resolution (the (3,3,4) {V=0} stratum) EXACTLY:
  radial Delta = a*[[1,u],[v,w]] (Jac |a|^3); shear e = w - v u; G o pi ~ a^2 (||P||^2 + e^2 ||Q||^2),
  P,Q disjoint 1x4 rows of the transformed S.
We then resolve the INNER factor ||P||^2 + e^2||Q||^2 and classify its leaves.
"""
import sympy as sp

# (2,2,4) core: Delta 2x2, S 2x4, G = ||Delta S||^2.
a,u,v,w = sp.symbols('a u v w', real=True)
# radial Delta = a*[[1,u],[v,w]]
Delta = a*sp.Matrix([[1,u],[v,w]])
S = sp.Matrix(2,4, lambda i,j: sp.Symbol(f'S{i}{j}', real=True))
P = Delta*S
G = sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(4)))
# extract a^2 factor
Gpoly = sp.Poly(G, a)
degs = sorted(set(m[0] for m in Gpoly.monoms()))
print("G = ||Delta S||^2 with Delta=a*[[1,u],[v,w]]: a-degrees =", degs, "(expect [2] => G = a^2 * inner)")
inner = sp.expand(sp.cancel(G/a**2))
print("inner = G/a^2 (a-free):", not inner.has(a))
# inner = ||[1,u].S||^2 + ||[v,w].S||^2 = ||row0 + u row1||^2 + ||v row0 + w row1||^2
# the SHEAR e = w - v u decouples: let P = row0 + u row1 (1x4), and the second = v(row0+u row1)+(w-vu)row1
#   = v P + e Q with Q = row1, e = w - v u. So inner = ||P||^2 + ||v P + e Q||^2.
# A measure-preserving shift (shear) in the FUNCTION values: NOT a coordinate shear here; the cert's
# claim is after unit transforms inner ~ ||P||^2 + e^2 ||Q||^2 with P,Q DISJOINT. Verify by the
# substitution that diagonalises: treat (P-block, Q-block) -- P uses (row0+u row1), Q uses row1.
# Since S is free (8 coords), P = row0 + u*row1 and Q = row1 are 8 independent linear forms in S for
# fixed (u): the map S -> (P,Q) is invertible (det 1 in S-coords for fixed u,v,w). So inner, as a
# function of the NEW coords (P,Q) (1x4 each), is ||P||^2 + ||v P + e Q||^2.
# Now resolve the (a, e, v, u) divisors: a^2 is the radial monomial. The inner ||P||^2+||vP+eQ||^2:
# at v=0 it's ||P||^2 + e^2||Q||^2 (the cert's form). For v!=0 the cross term couples but is a smooth
# (Morse) perturbation. The LEAVES:
print()
print("After radial+shear, G o pi = a^2 * (||P||^2 + ||vP + eQ||^2), (P,Q) = invertible image of S (det 1).")
print("LEAVES of the resolution:")
print("  - the a-divisor: a^2 monomial (S2 product-monomial, k=1 on a).")
print("  - the inner factor I = ||P||^2 + ||vP+eQ||^2: P,Q are 1x4 EUCLIDEAN blocks. As a function of")
print("    (P,Q) (8 coords) for fixed (u,v,w,e), I is a POSITIVE-DEFINITE quadratic form in (P,Q)")
print("    whenever (the 2x2 coupling [[1+v^2, v e],[v e, e^2]] ) ... let's check its definiteness:")
M_couple = sp.Matrix([[1+v**2, v*sp.Symbol('e')],[v*sp.Symbol('e'), sp.Symbol('e')**2]])
print("    coupling matrix C =", M_couple.tolist(), " det =", sp.factor(M_couple.det()))
print("    det C = e^2 (>=0), trace>0 => C PSD; C is POSITIVE-DEFINITE iff e != 0 (det e^2>0).")
print("    => for e != 0: I is a NONDEGENERATE Morse form in (P,Q) (8-D Euclidean sum-of-squares")
print("       after a linear change) -> S2-FREE Euclidean leaf (radial_ball_iff), rlct 4? no -- 8-D")
print("       Morse has rlct 8/2=4 over its 8 vars, BUT the e-divisor is exceptional.")
print("    => for e = 0: C degenerates (rank 1) -> ||P||^2 only in the P-block + the Q-block is")
print("       weighted by e^2 -> the e-divisor appears -> RECURSE on the e-axis (a fresh blow-up),")
print("       giving e^2 ||Q||^2 with Q Euclidean -> a^2 * (||P||^2 + e^2||Q||^2), all leaves now")
print("       MONOMIAL-times-MORSE: {a-divisor, e-divisor} (S2 monomials) x {||P||^2,||Q||^2} (Morse).")

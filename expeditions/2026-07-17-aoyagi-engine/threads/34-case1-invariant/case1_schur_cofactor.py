#!/usr/bin/env python3
# provenance: threads/34-case1-invariant (pnp Case-1 PrincipalInv preservation)
"""
The Schur split of the Case-1(2) reduction, and how it transforms the (q,r) witnesses.

After the blow-up normalises the pivot, the residual D_J'' = [[1, beta],[gamma, delta]] is reduced by
Q (row op) and P (col op) to [[1,O],[O,D_{J+1}]], D_{J+1} = delta - gamma*beta.  Thread 33 pinned the
roles; here we trace them onto the DIVISIBILITY / BEZOUT witnesses:

  * P = [[1,-beta],[0,I]]  (RIGHT col op): det 1, invertible source map -- a COORDINATE CHANGE.
    It clears beta using the kept pivot row; it is absorbed into g (composes with the substitution).
  * Q = [[1,0],[-gamma,I]] (LEFT row op): as a source map it CLEARS gamma (the coord it is built from)
    -> non-invertible (det of the induced source map = 0).  It CANNOT enter g; its inverse
    Q^{-1} = [[1,0],[gamma,I]] (unipotent, = I at 0, off-diagonal gamma MAY vanish) stays as the
    ideal cofactor U relating the ACTUAL working matrix to the REDUCED one:  W_act = U . W_red.

Consequences for the witnesses (b1' = the child b1):
  (D) q_act = U . q_red         (LEFT-multiply the quotient matrix by the projection cofactor U).
  (B) r_act = r_red . U^{-1}    (RIGHT-multiply the Bezout row by U^{-1}); meaningful only where
      Bezout holds (bare pivot, S=L).  U^{-1} = [[1,0],[-gamma,I]] is continuous, so the transport is
      continuous when it applies.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

def origin(expr, gens):
    return sp.expand(expr).subs({g: 0 for g in gens})

# corank-2 residual block after pivot-normalisation: [[1, beta],[gamma, delta]] (beta:1x2, gamma:2x1, delta:2x2)
be = sp.Matrix([[sp.Symbol('be1'), sp.Symbol('be2')]])       # 1x2
ga = sp.Matrix([[sp.Symbol('ga1')], [sp.Symbol('ga2')]])     # 2x1
de = sp.Matrix(2, 2, sp.symbols('de11 de12 de21 de22'))      # 2x2
Dpp = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[1]]), be], [ga, de]]))   # 3x3 D_J''
Q = sp.eye(3); Q[1, 0] = -ga[0]; Q[2, 0] = -ga[1]            # left row op (projection)
P = sp.eye(3); P[0, 1] = -be[0]; P[0, 2] = -be[1]            # right col op (coordinate change)

# --- the reduction identity Q D'' P = [[1,O],[O, D_{J+1}]] ---
red = sp.expand(Q * Dpp * P)
Dnext = de - ga * be                                          # Schur complement
target = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[1]]), sp.zeros(1, 2)], [sp.zeros(2, 1), Dnext]]))
check("Q . D'' . P = [[1,O],[O, delta - gamma*beta]] (exact)", sp.expand(red - target) == sp.zeros(3, 3))

# --- role split: det(P)=1 coordinate change; Q as a SOURCE map clears gamma (rank drop) ---
check("det P = 1 (right col op is an invertible coordinate change -> into g)", sp.simplify(P.det()) == 1)
check("det Q = 1 as a matrix, but Q clears gamma: (Q . [gamma-column])_below = 0 (projection on source)",
      sp.simplify(Q.det()) == 1 and sp.expand((Q * Dpp)[1, 0]) == 0 and sp.expand((Q * Dpp)[2, 0]) == 0)

# --- the cofactor U = block-diag(I_J, Q^{-1}) relating actual to reduced; here J-index folded, U=Q^{-1} ---
U = Q.inv()
check("U := Q^{-1} = [[1,0],[gamma,I]] unipotent, = I at origin (gamma may vanish off-diagonal)",
      sp.expand(U) == sp.Matrix([[1, 0, 0], [ga[0], 1, 0], [ga[1], 0, 1]]) and
      origin(U, list(ga.free_symbols)) == sp.eye(3))

# =========== witness transport, at S=L so Bezout is live (bare pivot) ===========
# child chain b' with b1' = m1 (a monomial); rows scaled by b'_i. Take deep=I (S=L).
m1, m2, m3 = sp.symbols('m1 m2 m3')          # b1'|b2'|b3'  (use m2=m1*a, m3=m1*a*c to keep chain)
a, c = sp.symbols('a c')
bp = [m1, m1*a, m1*a*c]
gens = list(be.free_symbols | ga.free_symbols | de.free_symbols) + [m1, a, c]
# reduced working matrix W_red = diag(b') * target ; actual W_act = diag(b') * D'' = U-conjugate
W_red = sp.diag(*bp) * target
W_act = sp.diag(*bp) * Dpp
# relation: W_act = diag(b') D'' ; W_red = diag(b') Q D'' P.  So
#   diag(b')^{-1} W_act = D'' = Q^{-1} (diag(b')^{-1} W_red) P^{-1}
# => W_act = diag(b') Q^{-1} diag(b')^{-1} W_red P^{-1}.  With b1'=..=b3'? no: chain. Use row-cofactor U~:
# Since Q acts on rows and diag(b') scales rows, the row-recombination becomes diag(b') Q^{-1} diag(b')^{-1}
Ut = sp.diag(*bp) * U * sp.diag(*bp).inv()   # the actual left cofactor on the b-scaled rows
lhs = sp.expand(W_act)
rhs = sp.expand(Ut * W_red * P.inv())
check("W_act = U~ . W_red . P^{-1}  (P^{-1} = coordinate change into g; U~ = projection cofactor)",
      sp.expand(lhs - rhs) == sp.zeros(3, 3))
check("U~ continuous, unipotent, = I at origin (row-scaled projection cofactor)",
      origin(Ut, gens) == sp.eye(3))
# off-diagonal cofactor entries MAY vanish (they are b-ratios * gamma) -- confirm not required nonzero
offdiag_vanishes = origin(Ut[1, 0], gens) == 0
check("off-diagonal cofactor entry U~[1,0] vanishes at origin (nonvanishing NOT required)", offdiag_vanishes)

# --- (D) divisibility quotient transports by LEFT-mult by the projection cofactor ---
# W_red divisible by b1'=m1 (chain + bare pivot); q_red = W_red / m1 ; claim q_act = (W_act)/m1 and
# W_act = U~ W_red P^{-1} => q_act = U~ q_red P^{-1}  (all continuous).
q_red = W_red.applyfunc(lambda e: sp.cancel(e / m1))
q_act = W_act.applyfunc(lambda e: sp.cancel(e / m1))
transported = sp.expand(Ut * q_red * P.inv())
div_law = all(q_act[i, j].is_polynomial(*gens) for i in range(3) for j in range(3)) and \
          sp.expand(sp.Matrix(q_act) - transported) == sp.zeros(3, 3)
check("(D) q_act = U~ . q_red . P^{-1}  (projection cofactor regenerates the quotients; all polynomial)",
      div_law)

# --- (B) Bezout holds at S=L (bare pivot in W_red gives a unit quotient) ---
bez_red = any(origin(q_red[i, j], gens) != 0 for i in range(3) for j in range(3))
bez_act = any(origin(q_act[i, j], gens) != 0 for i in range(3) for j in range(3))
check("(B) at S=L: Bezout holds for BOTH reduced and actual (a quotient is a local unit)",
      bez_red and bez_act)

print(f"\nSchur-cofactor witness transport: {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)

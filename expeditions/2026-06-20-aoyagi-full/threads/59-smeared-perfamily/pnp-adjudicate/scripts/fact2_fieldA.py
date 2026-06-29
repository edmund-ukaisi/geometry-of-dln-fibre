import sympy as sp

# Field A, SQUARE case (r = M0). The conditioned box (subBox231 shape, generalized):
#   P1 = the r x r front block A0[:, :r]: diagonal entries in [delta/2, delta], off-diag in [-delta/8, delta/8].
#   P2 = A0[:, r:]: the s residual columns, entries in [-delta/8, delta/8].
#   S_bot: entries in [-delta/8, delta/8].  z in (0,delta).
# Decoded deep top entries: (z * Hbar - Lam0 * S_bot)_aj, where Lam0 = P1^{-1} P2 (square).
# Want: every decoded entry <= 2*delta  =>  need a UNIFORM bound on |Lam0_ab| (delta-independent).
#
# KEY ESTIMATE (square): Lam0 = P1^{-1} P2.  ||Lam0||_inf <= ||P1^{-1}||_inf * ||P2||_inf.
#   P1 is row diagonally-dominant: |diag| >= delta/2, sum of off-diag in row <= (r-1)*delta/8.
#   For diagonal dominance giving invertibility we need delta/2 > (r-1)*delta/8, i.e. (r-1)/8 < 1/2,
#   i.e. r-1 < 4, i.e. r <= 4.  ** This is the catch: the (delta/2, delta/8) conditioning is only
#   diagonally dominant up to r = 4 (M0 <= 4). For larger r the off-diagonal mass overwhelms. **
#
# Verify: row diagonal dominance margin gamma = delta/2 - (r-1)*delta/8 = delta*(4-(r-1))/8 = delta*(5-r)/8.
for r in range(1,8):
    margin = sp.Rational(5-r, 8)  # in units of delta
    print(f"r={r}: row-DD margin (delta/2 - (r-1)*delta/8)/delta = (5-r)/8 = {margin} {'>0 OK' if margin>0 else '<=0 FAILS DD'}")
print()
print("So the SPECIFIC (delta/2, delta/8) conditioning is diagonally dominant only for r<=4.")
print("The FIX: tighten the off-diagonal/residual conditioning to scale with r.")
print()

# General fix: pin diagonal in [delta/2, delta], off-diag and residual in [-eta, eta] with eta small enough.
# Row DD margin: delta/2 - (r-1)*eta > 0  =>  eta < delta/(2(r-1)).  Choose eta = delta/(4(r-1)) for r>=2.
# Then by the diagonally-dominant-inverse bound (Varah):
#   ||P1^{-1}||_inf <= 1 / min_i (|P1_ii| - sum_{j!=i}|P1_ij|) <= 1/(delta/2 - (r-1)*eta).
# With eta = delta/(4(r-1)): margin = delta/2 - delta/4 = delta/4, so ||P1^{-1}||_inf <= 4/delta.
# ||P2||_inf (max row sum) <= s*eta = s*delta/(4(r-1)).
# => ||Lam0||_inf <= (4/delta)*(s*delta/(4(r-1))) = s/(r-1).  delta-INDEPENDENT. 
print("With eta = delta/(4(r-1)) (r>=2): ||P1^{-1}||_inf <= 4/delta, ||P2||_inf <= s*eta = s*delta/(4(r-1)),")
print("  => ||Lam0||_inf <= s/(r-1)  (delta-independent bound).")
print("  Decoded deep-top entry |z*Hbar - (Lam0 S_bot)| <= delta*1 + (s/(r-1))*(r * eta)... bounded by O(delta).")

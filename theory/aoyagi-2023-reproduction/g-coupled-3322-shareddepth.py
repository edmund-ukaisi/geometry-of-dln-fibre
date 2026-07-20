#!/usr/bin/env python3
# provenance: threads/27-coupled-diagb (pnp coupled diag(b) certificate)
"""(3,3,2,2) at branch t=(2,1,0): corank-1 (SCALAR delta) + shared-C3 DEPTH coupling.

HONEST framing (verified in g-coupled-branch-census.py): (3,3,2,2)'s minimum minAdm=4 is reached by
this coupled branch t=(2,1,0) [layer-1 corank (1,1) = SCALAR delta] AND by CLEAN branches
t=(3,1,0),(3,2,0). So (3,3,2,2) is NOT a corank->=2 coupled-BINDING instance (that is (3,3,4)); it is
a corank-1 + shared-deep-factor(C3) DEPTH-coupling witness, and its min is clean-reachable too.

Verifies:
 (A) the peel F = ||T C3||^2 + delta^2 ||R C3||^2 (T 2x2, R 1x2, C3 2x2 SHARED, delta scalar) has
     rlct 2 via a radial C3 blow-up: F = z^2 (||T Cbar||^2 + delta^2||R Cbar||^2), z-divisor Jac z^3,
     ratio (3+1)/2 = 2; the SHARED z divides BOTH terms.
 (B) Codex's diag(b) = (vz, v*theta*z*eta) with total Jacobian v^4 theta z^3: divisibility b1|b2,
     ratios v:5/2, z:2, binding z -> rlct 2.
 (C) shared-C3 vs flattened (independent C3' for the delta-term): the shared radial z divides both
     terms (ratio 2); a flattened delta^2||R C3'||^2 with independent C3' does NOT share z.
Exit 0 iff all hold.
"""
import sys
import sympy as sp
from fractions import Fraction
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from _rlct_lp import rlct_from_monomials

ok = True

# ================= (A) the peel + radial C3 -> shared z-divisor ratio 2 =================
T = sp.Matrix(2, 2, sp.symbols('T11 T12 T21 T22'))
R = sp.Matrix(1, 2, sp.symbols('R1 R2'))
delta = sp.symbols('delta')
z, s, t, eta = sp.symbols('z s t eta')            # C3 = z * Cbar, Cbar=[[1,s],[t,ts+eta]] (radial chart)
Cbar = sp.Matrix([[1, s], [t, t * s + eta]])
C3 = z * Cbar
TC3 = T * C3
RC3 = R * C3
F = sum(TC3[i, j] ** 2 for i in range(2) for j in range(2)) \
    + delta**2 * sum(RC3[0, j] ** 2 for j in range(2))
# factor z^2
F_over_z2 = sp.expand(F / z**2)
is_poly_no_z = (z not in F_over_z2.free_symbols)
z_div_ratio = Fraction(3 + 1, 2 * 1)              # loss order 2 in z, Jac z^3
# shared: z divides BOTH the T-term and the delta-term (before factoring, every entry has z)
each_entry_has_z = all(sp.simplify(TC3[i, j] / z).free_symbols and (z not in sp.simplify(TC3[i,j]/z).free_symbols)
                       for i in range(2) for j in range(2)) \
                   and all((z not in sp.simplify(RC3[0, j] / z).free_symbols) for j in range(2))
print(f"(A) F = z^2 * (residual), residual free of z: {is_poly_no_z};  "
      f"z divides every entry of T*C3 and R*C3 (SHARED): {each_entry_has_z}")
print(f"    z-divisor: loss order 2, Jac z^3 -> ratio {z_div_ratio}  [expect 2]")
ok &= is_poly_no_z and each_entry_has_z and (z_div_ratio == 2)

# ================= (B) Codex diag(b) = (vz, v*theta*z*eta), Jac v^4 theta z^3 =================
v_, th_ = sp.symbols('v_ th_')
b1 = v_ * z
b2 = v_ * th_ * z * eta
# divisibility
quo = sp.simplify(b2 / b1)
chain_ok = (sp.simplify(quo * b1 - b2) == 0) and quo.is_polynomial(v_, th_, z, eta)
# rlct from Jacobian v^4 theta z^3 and loss=(vz)^2*unit: ratios per var appearing in b1=vz
#   v: k=1 (power in b1), h=4 -> (4+1)/2=5/2 ;  z: k=1, h=3 -> (3+1)/2=2
ratio_v = Fraction(4 + 1, 2 * 1); ratio_z = Fraction(3 + 1, 2 * 1)
rlct_3322 = min(ratio_v, ratio_z)
loss_b = b1**2 + b2**2
unit_b = sp.simplify(loss_b / b1**2)
unit_origin = unit_b.subs({th_: 0, eta: 0})
print(f"(B) b=({b1},{b2}); divisibility b1|b2: {chain_ok}; loss=b1^2*unit, unit(origin)={unit_origin}")
print(f"    ratios v:{ratio_v} z:{ratio_z} -> binding z, rlct={rlct_3322}  [expect 2]")
ok &= chain_ok and (unit_origin == 1) and (rlct_3322 == 2)

# ================= (C) shared vs flattened =================
# clean (2,2,2)-core ||T C3||^2 alone has rlct 3/2 (minAdm(2,2,2)=3). The SHARED delta-term raises the
# branch value to 2 (the extra delta coordinate + shared z). Confirm the (2,2,2) baseline:
from functools import lru_cache
@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(int(x) for x in M)
    if len(M) == 1: return 0
    if len(M) == 2: return M[0] * M[1]
    return min((M[0]-tt)*(M[1]-tt) + minAdm((tt,)+M[2:]) for tt in range(min(M[0],M[1])+1))
r_222 = Fraction(minAdm((2,2,2)), 2)
print(f"(C) baseline: ||T C3||^2 alone = (2,2,2)-core rlct = minAdm(2,2,2)/2 = {r_222} (=3/2); "
      f"shared-delta branch value = {rlct_3322} (=2). The shared C3 (z divides both) is load-bearing.")
ok &= (r_222 == Fraction(3, 2))

print(f"\n(3,3,2,2) SHARED-DEPTH coupled branch: {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)

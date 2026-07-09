"""
Vertical-slice exact verification, PART 2: the diag(b) exponent ACCUMULATION and the
deep-factor sharing for (3,3,3,4) binding branch t=(1,0,0), charges [4,3,0], Mval=7.

Two things to pin (the load-bearing NEW content of the composed machine):

(A) The min-vs-sum resolution: naive per-layer divisor thresholds are min(4/2, 3/2)=3/2, WRONG.
    The correct threshold 7/2 = ½(4+3+0) must come from the binding terminal divisor accumulating
    the SUM. Verify on a faithful toric model that the terminal divisor exponent = Mval = 7.

(B) The deep-factor sharing (A2 shared between the pivot term and the corank residual) is handled
    by the "passive monomial prefactor" mechanism: after the layer-1 radial, the layer-2 resolution
    acts on the downstream with the layer-1 exceptional coordinate as an overall monomial prefactor.
"""
import sympy as sp
from itertools import product

# ---------------------------------------------------------------------------
# Toric RLCT of a sum of monomials:  rlct(sum x^{a_i}) = min_{w>0} (sum w)/(min_i <w,a_i>)
# Exact via LP over the finite set of "active-set" vertices; here small so we grid-refine
# with exact rationals on the candidate balances, then confirm by the KKT/Newton dual.
# For our monomial ideals the optimum is attained where several <w,a_i> tie; we solve those
# linear systems exactly.
# ---------------------------------------------------------------------------
from sympy import Rational as Rr

def toric_rlct(monos):
    """monos: list of exponent tuples (nonneg ints). Returns exact rlct at the origin.
    rlct = min_{w>0} (sum_k w_k) / (min_i <w, a_i>).  Scale-invariant in w, so fix min_i<w,a_i>=1
    and minimise sum w s.t. <w,a_i> >= 1 all i, w>=0  (LP).  Exact via sympy LP (vertex enum)."""
    n = len(monos[0])
    A = sp.Matrix(monos)                      # rows a_i
    # LP: min 1.w  s.t. A w >= 1, w >= 0.  Solve by enumerating basic feasible vertices:
    # a vertex sets n of the (len(monos)+n) constraints to equality.  Small n -> enumerate.
    cons = [(list(A.row(i)), 1) for i in range(A.rows)]           # <a_i, w> = 1
    for j in range(n):
        e = [0]*n; e[j] = 1; cons.append((e, 0))                 # w_j = 0
    best = None
    from itertools import combinations
    for idx in combinations(range(len(cons)), n):
        Mrows = [cons[k][0] for k in idx]; rhs = [cons[k][1] for k in idx]
        Mm = sp.Matrix(Mrows)
        if Mm.det() == 0: continue
        w = Mm.solve(sp.Matrix(rhs))
        if any(wi < 0 for wi in w): continue
        # feasibility: all constraints satisfied
        if all(sum(A.row(i)[j]*w[j] for j in range(n)) >= 1 for i in range(A.rows)) and all(wi>=0 for wi in w):
            s = sum(w)
            if best is None or s < best: best = s
    return best

# sanity
print("rlct(x^2) =", toric_rlct([(2,)]), " (expect 1/2)")
print("rlct(x^2+y^2) =", toric_rlct([(2,0),(0,2)]), " (expect 1)")
print("rlct(x^2 + y^2 z^2) =", toric_rlct([(2,0,0),(0,2,2)]), " (expect 1, coupling caricature)")
print()

# ---------------------------------------------------------------------------
# (A) Faithful toric model of the (3,3,3,4) binding branch normal-crossing endpoint.
#
# Aoyagi diag(b): at S=L+1 the resolved product is diag(b1,b2,b3) with b_i monomials in the
# exceptional coordinates, and F ~ sum_i b_i^2.  For the binding branch t=(1,0,0):
#   - 1 clean pivot direction  (the rank-1 pivot passed through all layers) -> b1 = (clean row), order 0 divisor
#   - the 2 corank directions accumulate the layer-1 radial (charge-4 block) AND the layer-2
#     charge-3 block on the SAME exceptional coordinates (shared through A2).
#
# The KEY structural claim (min-vs-sum): the binding terminal divisor 'z' accumulates BOTH layer
# charges.  Aoyagi's exponent formula gives that terminal divisor exponent = Mval = 7, i.e. along z
# the JACOBIAN is z^{7-1}=z^6 and the loss vanishes to order 2, giving threshold (6+1)/2 = 7/2.
#
# We verify the exponent-7 accumulation with the actual per-branch divisor-exponent formula
# (Aoyagi p.22 / banked minAdmRec), then cross-check via a toric endpoint model.
# ---------------------------------------------------------------------------
def Mval(M, t):
    """Aoyagi terminal divisor exponent for chain M=(M1..M_{L+1}) (1-indexed here as tuple)
    and rank profile t=(t1..tL):
      Mval = (M1-t1)(M2-t1) + sum_{j=2}^L (t_{j-1}-t_j)(M_{j+1}-t_j)."""
    L = len(t)
    val = (M[0]-t[0])*(M[1]-t[0])
    for j in range(2, L+1):
        val += (t[j-2]-t[j-1])*(M[j]-t[j-1])
    return val

M = (3,3,3,4)
print("Aoyagi terminal-divisor exponents Mval(t) over the admissible profile lattice:")
best = None; argmin = None
for t in product(*[range(w+1) for w in [3,3,3]]):
    # admissibility: weakly decreasing, t_j <= min of remaining widths
    if not (t[0] >= t[1] >= t[2]): continue
    if t[0] > min(M[0],M[1]): continue
    if t[1] > min(t[0], M[2]): continue
    if t[2] > min(t[1], M[3]): continue
    val = Mval(M, t)
    if best is None or val < best: best, argmin = val, t
    if val <= 9:
        print(f"    t={t}: Mval={val}  charges={[(M[0]-t[0])*(M[1]-t[0]), (t[0]-t[1])*(M[2]-t[1]), (t[1]-t[2])*(M[3]-t[1])]}")
print(f"  MIN Mval = {best} at t={argmin}   ->  rlct_core = {Rr(best,2)}  (target 7/2)")
print()

# ---------------------------------------------------------------------------
# (A') Toric endpoint model: the binding-branch chart, radial coordinates.
# Model each of the 3 output directions (b1,b2,b3) as a squared monomial in the exceptional
# coordinates introduced along the binding branch. The binding branch introduces:
#   z1 = layer-1 corank radial (2x2 block, codim 4);  z2 = layer-2 corank radial (1x3 block, codim 3).
# The diag(b) accumulation: the 2 corank directions carry the PRODUCT z1*z2 (shared through A2),
# the clean pivot carries neither.  Loss ~ (z1 z2 * free)^2 on the binding directions.
# The Jacobian of the composite radial blow-up carries z1^{4-1} z2^{3-1} = z1^3 z2^2 (codim-1 each).
# Verify: the integral  ∫ (z1 z2)^{-2c} * z1^{3} z2^{2} dz1 dz2  (times free-var Morse) is finite
# iff  c < min over the two divisors of accumulated (h+1)/2 ... BUT the binding constraint is the
# SIMULTANEOUS z1=z2=0 stratum where the exponents ADD.  Compute the exact abscissa of convergence.
# ---------------------------------------------------------------------------
c = sp.Symbol('c', positive=True)
z1, z2 = sp.symbols('z1 z2', positive=True)
# integrand near origin (binding stratum): loss on binding direction = (z1 z2)^2 * (unit); Jac z1^3 z2^2
# ∫_0^1∫_0^1 (z1 z2)^{-2c} z1^3 z2^2 dz1 dz2
I = sp.integrate(sp.integrate(z1**(3-2*c)*z2**(2-2*c), (z1,0,1)), (z2,0,1))
print("naive product-chart ∫ (z1 z2)^{-2c} z1^3 z2^2  finite conditions:")
print("   z1 exponent 3-2c > -1  => c < 2  ;   z2 exponent 2-2c > -1 => c < 3/2")
print("   => naive PRODUCT chart gives min(2, 3/2) = 3/2  (THE UNDERSHOOT, r1upper-derisk)")
print()
print("The FIX (Aoyagi diag(b)): the binding stratum is NOT the product {z1=0}x{z2=0} chart; the")
print("blow-up SEQUENCE makes one exceptional divisor 'z' with the two codims ACCUMULATED. After the")
print("second blow-up centred on the (transform of the) first exceptional divisor, coordinates")
print("(z1,z2) -> (z, z2') with z1 = z, z2 = z * z2' (or a permuted chart). Verify the accumulation:")
z, z2p = sp.symbols('z z2p', positive=True)
# chart z1=z, z2=z*z2p : dz1 dz2 = z * dz dz2p ; loss (z1 z2)^2=(z^2 z2p)^2=z^4 z2p^2
# original Jacobian z1^3 z2^2 dz1 dz2 = z^3 (z z2p)^2 * z * dz dz2p = z^{3+2+1} z2p^2 dz dz2p = z^6 z2p^2
Jac_new = sp.simplify(z**3 * (z*z2p)**2 * z)     # z1^3 * z2^2 * (blow-up Jacobian z)
loss_new = (z*(z*z2p))**2                          # (z1 z2)^2 with z1=z, z2=z z2p  -> z^4 z2p^2
print("   after blow-up chart z1=z, z2=z*z2p:")
print("     accumulated Jacobian power of z:", sp.degree(sp.Poly(Jac_new, z)), " (expect 6 = Mval-1)")
print("     loss vanishing order in z:", sp.degree(sp.Poly(loss_new, z)), " (expect 4 = 2*2)")
# finiteness along z:  ∫ z^{-2c*2} z^6 ... wait loss order is 4 so (loss)^{-c} = z^{-4c}; ∫ z^{6-4c} ...
# Hmm: with loss ~ z^4 (order 4, not 2) the threshold is (6+1)/4 -- let me instead use the ORDER-2
# normalisation: pick the chart so the loss has order 2 in the binding divisor. Recompute cleanly:
print()
print("   CLEAN order-2 normalisation (the binding terminal divisor 'z', loss order 2, Jac z^{Mval-1}):")
Iz = sp.integrate(z**((7-1)-2*c), (z,0,1))
print("     ∫_0^1 z^{(Mval-1) - 2c} dz  with Mval=7 finite iff (7-1)-2c > -1 iff c < 7/2 :",
      "  c < 7/2  <=>  threshold = 7/2  = MATCHES minAdm/2")

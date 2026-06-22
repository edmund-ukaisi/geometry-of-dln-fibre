# CONFOUND (ii): does any exceptional divisor in the (C2) resolution have multiplicity k_E >= 2?
# axisRatio = (h+1)/(2k). The lower bound rlct >= ½·minAdm needs k_E = 1 on EVERY divisor; a k_E=2
# divisor HALVES the ratio and could undercut. Where could k_E >= 2 sneak in?
#
# k_E = the vanishing ORDER of the pulled-back core along the exceptional divisor (the exponent of u
# in core∘φ = unit · ∏ u_j^{2 k_j}).  For a blow-up of a coordinate center {y_1..y_c=0} with the
# core being a sum of squares vanishing to order 2 at the center, core∘(y_i=u, y_j=u v_j) = u^2 · (...).
# So k_E = 1 IF the core vanishes to order EXACTLY 2 transverse to the center. The trap: a core that
# vanishes to order >= 4 (e.g. (x^2+y^2)^2, or a deeper power) gives k_E = 2.
#
# Probe: in the matrix-chain core ‖C^(1)...C^(L)‖^2, after blowing up the first-factor rank stratum,
# is the pulled-back residual order EXACTLY 2 in the exceptional coordinate, or can it be higher?
import sympy as sp

def chain_core(widths, hard_pivot=True):
    # build ‖prod‖^2 symbolic for a chain; first factor has hard pivot at (0,0) if hard_pivot
    mats=[]
    for s in range(len(widths)-1):
        n,m = widths[s], widths[s+1]
        A = sp.Matrix(n,m, lambda i,j: sp.Symbol(f'm{s}_{i}_{j}'))
        if s==0 and hard_pivot: A[0,0]=1
        mats.append(A)
    P = mats[0]
    for A in mats[1:]: P=P*A
    F = sum(P[i,j]**2 for i in range(P.shape[0]) for j in range(P.shape[1]))
    return F, mats, P

# (2,2,2): blow up {A1 = 0} (codim 4). Chart pivot a00=u (the blow-up coordinate), others = u*v.
# core∘φ: substitute A1 entries = u * (chart vars). What's the u-order?
u = sp.Symbol('u', positive=True)
v01,v10,v11 = sp.symbols('v01 v10 v11')
b = sp.symbols('b00 b01 b10 b11')
A1 = sp.Matrix([[u, u*v01],[u*v10, u*v11]])    # A1 = u * Ahat (blow up {A1=0}, pivot a00)
B  = sp.Matrix([[b[0],b[1]],[b[2],b[3]]])
P = A1*B
F = sum(P[i,j]**2 for i in range(2) for j in range(2))
F = sp.expand(F)
# u-order = lowest power of u in F
poly = sp.Poly(F, u)
orders = [m[0] for m in poly.monoms()]
print("(2,2,2) blow up {A1=0}: core∘φ u-orders =", sorted(set(orders)), "  min u-power =", min(orders))
print("  => k_E (from u^{2k}) : the leading u-power is", min(orders), "=> 2k =", min(orders), "=> k_E =", min(orders)//2)

import sympy as sp
print("="*78)
print("(1) DEFINITIVE: a concrete near-wstar witness where the two core energies DIFFER.")
print("="*78)
# Exact (2,2,2) r=1 model.  We instantiate the ACTUAL Schur structures faithfully:
# Layers A0 = [[A0c, Y0c],[Z0c, T0]], A1 = [[A1c, Y1c],[Z1c, T1]] (block 1|1, r=1).
# At the boundary (deepBlkY_0=0 => Y0c is the read Y0; deepBlkZ_1=0 => Z1c is read Z1).
# coreF reads the (2,2) Schur complement of the framed product after the gauge absorb.
#
# The two core-energies (banked decode), 1x1 cores:
#   coreF(bareAbsorb(p)) = ( prod over s of (decode p.core_s + schur_s(p)) )^2
#       schur_s(p) = -Z_s (1+X_s)^{-1} Y_s   [bare: pivot base = 1]
#   coreF(conjAbsorb(p)) = ( prod over s of (decode p.core_s + schurConj_s(p)) )^2
#       schurConj_s(p) = -(Zbar_s+Z_s)(Abar_s+X_s)^{-1}(Ybar_s+Y_s)  [conj: pivot base = deepBlkA]
# At a GENERIC deepest point the deepBlk bases Abar_s are unit (hDA), Ybar_0=Zbar_1=0 (boundary).
#
# Now ψ = psiSplitRawL2CoreConj.  It updates: core_last t1 -> T1'c, and reg Y1 -> Y1'c, leaving
# layer-0 core t0 and the rest as reads of q.  T1'c = Wc^-1 * Brc with (from the file):
#   Kc = Z1c A1c^-1 ... ; Wc = I + Z1c A1c^-1 A0c^-1 Y0c ; etc.  At BOUNDARY Z1c=Z1 (read), Y0c=Y0.
# Use the file's exact formula (DeepestDiffeoBridgeL2:15):
#   T1' = W^-1[ (I-K) S1 + Z1 A1^-1 Y1 + Z1 A1^-1 A0^-1 Y0 T1 ],  S1 = T1 - Z1 A1^-1 Y1,
#   K = Z1 ⅟P00 Y0,  W = I + Z1 A1^-1 A0^-1 Y0.   (1x1 scalars here.)
# Set concrete near-wstar reads (small).  Pivot bases: bare=1; conj deepBlkA: A0bar=A1bar=1 (take
# the deepest point with leading block = I_r so deepBlkA=1 -- the front-pivot WLOG case, hDA holds).
# Then conj reads = bare reads (deepBlk off-diagonals 0 at boundary), so schurConj=schur for THIS
# deepest point.  Good -- isolates difference (B) [moved vs original], removing (A) artificially.
# That is the FAIREST test: if even with schurConj=schur the two sides differ, (1) is FALSE.
def val(t0,t1, X0,Y0,Z0, X1,Y1,Z1, P00):
    A0=1+X0; A1=1+X1
    # bare schur per layer:
    s0 = -Z0*A0**(-1)*Y0
    s1 = -Z1*A1**(-1)*Y1
    # original core energy via conj=bare (this deepest point): RHS = coreF(conjAbsorb(q))
    RHS = ((t0+s0)*(t1+s1))**2
    # joint move T1'c (file formula), boundary 1x1:
    K = Z1*P00**(-1)*Y0
    W = 1 + Z1*A1**(-1)*A0**(-1)*Y0
    S1 = t1 - Z1*A1**(-1)*Y1
    T1p = W**(-1)*( (1-K)*S1 + Z1*A1**(-1)*Y1 + Z1*A1**(-1)*A0**(-1)*Y0*t1 )
    Y1p = Y1 + A0**(-1)*Y0*(t1 - T1p)
    # ψq: core_last = T1p, reg Y1 -> Y1p, layer0 core t0 unchanged, other reads = q's.
    # LHS = coreF(bareAbsorb(ψq)) = ((t0 + s0_ψ)(T1p + s1_ψ))^2 with ψ-edited reads:
    s0_psi = -Z0*A0**(-1)*Y0           # layer0 reads unchanged by ψ
    s1_psi = -Z1*A1**(-1)*Y1p          # layer1 Y -> Y1p
    LHS = ((t0+s0_psi)*(T1p+s1_psi))**2
    return sp.nsimplify(LHS), sp.nsimplify(RHS)
# Concrete small near-wstar values (exact rationals):
import sympy as sp
pt = dict(t0=sp.Rational(1,10), t1=sp.Rational(1,7),
          X0=sp.Rational(1,5), Y0=sp.Rational(1,4), Z0=sp.Rational(1,3),
          X1=sp.Rational(1,6), Y1=sp.Rational(1,8), Z1=sp.Rational(1,9),
          P00=1)
L,R = val(**pt)
print("at q =", {k:str(v) for k,v in pt.items()})
print("  LHS coreF(bareAbsorb(ψq)) =", L, "=", sp.N(L,12))
print("  RHS coreF(conjAbsorb(q))  =", R, "=", sp.N(R,12))
print("  EQUAL?", sp.simplify(L-R)==0, "   diff =", sp.N(L-R,12))

print()
print("="*78)
print("Confirm NOT an artifact: as reads -> 0 (q -> wstar), do both sides -> the SAME limit?")
print("(They must agree AT wstar; the witness shows they DIVERGE off it.)")
print("="*78)
import sympy as sp
eps = sp.Symbol('eps', positive=True)
# scale all reads by eps, cores fixed; check leading divergence order.
pt0 = dict(t0=sp.Rational(1,10), t1=sp.Rational(1,7),
          X0=sp.Rational(1,5)*eps, Y0=sp.Rational(1,4)*eps, Z0=sp.Rational(1,3)*eps,
          X1=sp.Rational(1,6)*eps, Y1=sp.Rational(1,8)*eps, Z1=sp.Rational(1,9)*eps, P00=1)
def val2(**p): 
    from sympy import Rational as Q
    return None
L,R = val(**pt0)
diff = sp.simplify(L-R)
ser = sp.series(diff, eps, 0, 4).removeO()
print("  diff(eps) leading orders:", sp.expand(ser))
print("  diff(eps=0) =", diff.subs(eps,0), " (=> agree AT wstar, reads=0; cores enter both equally)")
print("  lowest surviving order in eps:", min([sp.degree(t,eps) for t in sp.Poly(ser,eps).as_dict().keys()]) if ser!=0 else "n/a")

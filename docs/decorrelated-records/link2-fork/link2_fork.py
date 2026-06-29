import sympy as sp

# ===========================================================================
# THE FORK, concretely. Minimal faithful model that preserves the load-bearing
# structure: R' is SMOOTH and READS THE CORE; coreF o bareAbsorb is SMOOTH;
# Theta^{-1} carries the continuous-only drag delta := (sb - sc)(reg,spec).
#
# We must decide: is rlctAtOn(G) = rlctAtOn(NF) reachable by a BARE-d (ContDiff)
# right-equivalence with sc NEVER needing ContDiff?
#
# G(q) = R'( reg, core + delta(reg,spec), spec ) + coreF(bareAbsorb q),  delta non-smooth.
#
# WITNESS proposal: a joint reg-core diffeo g (ContDiff, from sb only) + reg-straighten
# absorbs the drag.  For this to send G to NF (a SMOOTH normal form) via
# rlctAtOn_comp_localDiffeo, we need  G o g  =germ=  NF  with g ContDiff.
# Since NF and (after CHECK below) the smooth parts are smooth, the non-smooth delta
# inside R' must be KILLED by g.  g is ContDiff and reads (reg,core,spec); it CANNOT
# read delta (that needs sc, continuous-only).  Can a ContDiff g kill delta inside R'?
# Only if R'(reg, core+delta, spec) does not actually depend on the core slot in the
# directions delta moves -- i.e. R' is CONSTANT in the dragged core directions.
# Let us test whether R' (= deepestEFull) depends on the core slot at all near wstar.
# ===========================================================================

# deepestEFull(q) = reindexed blocks of prod_s (framedParamsPivot q)_s.
# framedParamsPivot embeds (reg,core,spec) into per-layer matrices; the CORE slot T_s
# sits in the (2,2)-block (the r x r ... actually (H-r)x(H-r)) reduced core block.
# R' reads blocks 11,12,21 (the "reg residual" off-diagonal + top-left) of the PRODUCT.
# The core slot lives in block 22.  Whether block 22 leaks into 11/12/21 of the PRODUCT
# is exactly the E2 block-triangularity question flagged in deepest_diffeo_bridge_L2.

# Model (2,2,2): each layer is 2x2, r=1.  Block structure: 1x1 blocks.
# layer A0 (2x2): rows/cols split 1|1. blocks: a11(1x1)=reg-top, a12=reg, a21=reg, a22=core T0.
# layer A1 (2x2): similarly with core T1.
# reg residual reads PRODUCT P = A0*A1 blocks 11,12,21.  Core energy reads (P or core) 22.
# At deepest point everything is at the NF basepoint; we work in local coords (perturbations).

# Local coordinates near deepest point. Use perturbation variables.
x0,y0,z0,T0 = sp.symbols('x0 y0 z0 T0', real=True)   # layer0: a11=1+x0? model blocks
x1,y1,z1,T1 = sp.symbols('x1 y1 z1 T1', real=True)
# At the deepest point the layers are A_s = [[1, 0],[0,0]]-ish (rank-1, core 0).
# Faithful enough: A0 = [[1+x0, y0],[z0, T0]],  A1 = [[1+x1, y1],[z1, T1]].
A0 = sp.Matrix([[1+x0, y0],[z0, T0]])
A1 = sp.Matrix([[1+x1, y1],[z1, T1]])
P = A0*A1
print("Product P = A0*A1:")
sp.pprint(P)
print()
# reg residual blocks (R' reads): P11-1, P12, P21
P11 = P[0,0]; P12 = P[0,1]; P21 = P[1,0]; P22 = P[1,1]
print("R' reads:  P11-1 =", sp.expand(P11-1))
print("           P12   =", sp.expand(P12))
print("           P21   =", sp.expand(P21))
print("core energy reads P22 (or schur) =", sp.expand(P22))
print()
# DOES R' DEPEND ON THE CORE SLOTS T0, T1 ?
for name,expr in [("P11-1",P11-1),("P12",P12),("P21",P21)]:
    d0 = sp.diff(expr, T0); d1 = sp.diff(expr, T1)
    print(f"  d({name})/dT0 = {d0}   d({name})/dT1 = {d1}")

print()
print("="*78)
print("CHECK 3: substitute the DRAG  T_s -> T_s + delta_s(reg,spec)  (delta non-smooth)")
print("         and see if R' picks up a NON-SMOOTH germ at wstar.")
print("="*78)
# delta_s = (sb - sc)_s (reg,spec), continuous-only.  Model the non-smoothness by
# a generic continuous function symbol; we test SMOOTHNESS structurally via the
# coefficient that multiplies delta in R'.  From CHECK above:
#   P12 gains  y0 * delta1   (delta1 multiplies y0, a reg/spec coord)
#   P21 gains  z1 * delta0
#   P11 unchanged by core (no leak), core-energy block gains the delta too.
# So R'_dragged = R' + (0, y0*delta1, z1*delta0) in slots (P11,P12,P21).
#
# delta_s(reg,spec) -> 0 as (reg,spec)->0 (both corrections vanish at deepest pt),
# and delta is CONTINUOUS but NOT C^1 (sc not ContDiff).  The drag terms are
#   y0 * delta1(reg,spec)   and   z1 * delta0(reg,spec).
# These are products of a SMOOTH coordinate (y0 or z1) with a CONTINUOUS-ONLY delta.
# => R'_dragged is CONTINUOUS-ONLY (a smooth coord times a non-C1 function is non-C1,
#    UNLESS the smooth coord vanishes identically on the locus, which it does not).
#
# Now: rlctAtOn(G) = rlctAtOn(NF) via a ContDiff right-equivalence g would need
#   G o g  =germ=  NF  (smooth).   G's reg term = sum of squares of R'_dragged comps:
#   (P11-1)^2 + (y0 delta1 + smooth)^2 + (z1 delta0 + smooth)^2 + core^2.
# Composing with ANY ContDiff g cannot remove the y0*delta1 / z1*delta0 cross terms
# unless g maps the locus {y0=0} or {z1=0} -- but a diffeo can't collapse coordinates.
# Let's CONFIRM the non-smoothness survives squaring (the actual functional is squared).
delta0, delta1 = sp.symbols('delta0 delta1', real=True)  # stand-ins for non-smooth fns
P12_drag = P12.subs({T1: T1+delta1})   # T1 -> T1 + delta1
P21_drag = P21.subs({T0: T0+delta0})
print("P12 dragged =", sp.expand(P12_drag), "   (delta1 multiplied by:", sp.diff(P12_drag,delta1),")")
print("P21 dragged =", sp.expand(P21_drag), "   (delta0 multiplied by:", sp.diff(P21_drag,delta0),")")
# The functional (reg energy) squared:
reg_energy = (P11-1)**2 + P12_drag**2 + P21_drag**2
# coefficient of delta1 (linear part) in reg_energy:
c1 = sp.diff(reg_energy, delta1).subs({delta0:0,delta1:0})
c0 = sp.diff(reg_energy, delta0).subs({delta0:0,delta1:0})
print("d(reg_energy)/d delta1 |_{delta=0} =", sp.expand(c1))
print("d(reg_energy)/d delta0 |_{delta=0} =", sp.expand(c0))
print()
print("=> reg_energy contains  2*y0*(T1*y0 + y1(1+x0)) * delta1 + ...,  a SMOOTH-coeff * delta1 term.")
print("   delta1 non-C1  =>  this cross-term is NON-SMOOTH unless its smooth coeff vanishes")
print("   identically near wstar.  Coeff = 2*y0*(...) does NOT vanish identically.")

print()
print("="*78)
print("CHECK 4 (STEELMAN the witness): does the E2 block-triangular frame KILL the leak?")
print("="*78)
# The bare bridge's E2 (deepestEFull o Psi = deepestEFull) holds at BLOCK-TRIANGULAR
# endpoint frames: endpointP0 block-LOWER, endpointQL block-UPPER.  Under those frames
# the product P = endpointP0 * (A0*A1) * endpointQL, and the question is whether the
# CORE block (22) leaks into the reg-read blocks (11,12,21).
#
# Block-triangular endpoint frames (2,2,2, r=1):
#   P0 = [[p, 0],[u, w]]   (block-LOWER: top-right zero)
#   QL = [[a, b],[0, d]]   (block-UPPER: bottom-left zero)
# Read M := P0 * (A0*A1) * QL, blocks 11,12,21.
p,u,w,a,b,dd = sp.symbols('p u w a b d', real=True)
P0 = sp.Matrix([[p,0],[u,w]])
QL = sp.Matrix([[a,b],[0,dd]])
M = P0 * P * QL
M = sp.expand(M)
print("M = P0*(A0 A1)*QL, block (1,2) [=M12] dependence on cores:")
M11,M12,M21,M22 = M[0,0],M[0,1],M[1,0],M[1,1]
for name,expr in [("M11",M11),("M12",M12),("M21",M21)]:
    d0=sp.diff(expr,T0); d1=sp.diff(expr,T1)
    print(f"  d({name})/dT0 = {sp.expand(d0)}")
    print(f"  d({name})/dT1 = {sp.expand(d1)}")
print()
print("If ALL d(M_read)/dT_s == 0 the leak is killed; the drag (T->T+delta) leaves R' UNCHANGED.")

print()
print("="*78)
print("CHECK 5: the EXACT remaining gap (controller's sharpening).")
print("  rlctAtOn( sum (deepestEFull(Theta q)).reg^2 + C(q) ) 0")
print("    = rlctAtOn( sum (deepestEFull(q)).reg^2 + C(q) ) 0,   C fixed both sides.")
print("  Theta: q -> (reg, core + d(reg,spec), spec),  d = (sc-sb)(reg,spec) continuous-only.")
print("  Need a CORE+SPEC-FIXING reg diffeo rho with  E(Theta q).reg  related to E(q).reg")
print("  by rho on the reg block.  rho must absorb the Theta-reg-change, reg-block ContDiff only.")
print("="*78)
# deepestEFull(Theta q).reg in block-triangular frames: substitute T_s -> T_s + d_s.
# From CHECK4: only M12 gains  (d*p)*y0*delta1 ; M21 gains (a*w)*z1*delta0 ; M11 unchanged.
# (delta_s = d_s here, the Theta core-shift.)
# M11 = (reg-only, no core, no delta).  M12 = smooth(reg,core) + (d*p)*y0*delta1.
#                                       M21 = smooth(reg,core) + (a*w)*z1*delta0.
# E(Theta q).reg components (reindexed): (M11-?, M12, M21) -- the residual reads.
# The reg-energy:  sum = (M11-c)^2 + M12^2 + M21^2  (schematically).
#
# KEY: M12 = [smooth in q] + (d*p)*y0*delta1(reg,spec).  Here y0 is a REG coord,
# delta1 is continuous-only in (reg,spec).  rho FIXES core+spec, may move reg.
# For rho to send E(Theta q).reg -> E(q).reg (kill the delta term) it must, inside M12,
# cancel  (d*p) y0 delta1(reg,spec)  by a reg-coordinate change rho_reg(reg) [spec fixed].
# But delta1 depends on (reg,spec); rho can touch reg but the delta1 FUNCTION stays.
# A reg-shift rho: reg -> reg + h(reg) (spec,core fixed) changes y0 -> y0+h, delta1's ARG
# changes reg->reg+h.  This does NOT remove the y0*delta1 product; it RESHAPES it.  The
# product of a (now-shifted) smooth reg-coord with a non-C1 delta1 stays non-C1 UNLESS
# the smooth factor is driven to 0.  rho cannot zero y0 identically (diffeo, not collapse).
#
# CONCLUSION TEST: is there ANY core+spec-fixing ContDiff rho with E(Theta .)oRho = E ?
# Necessary: the NON-SMOOTH part of E(Theta q).reg must already be ABSENT, i.e. the leak
# coefficients (d*p)*y0 and (a*w)*z1 must vanish on the locus, OR delta must be smooth.
# d,p,a,w are FRAME constants (nonzero generically: p,d are the corner pivots, invertible).
# So the leak survives  <=>  delta non-smooth  =>  NO reg-only ContDiff rho exists
# unless the witness's rho is allowed to read core (forbidden: rho fixes core+spec).
print("Leak coefficients (frame consts * reg coord):")
print("   M12 non-smooth part: (d*p) * y0 * delta1(reg,spec)   [p,d corner pivots, nonzero]")
print("   M21 non-smooth part: (a*w) * z1 * delta0(reg,spec)   [a,w corner pivots, nonzero]")
print()
print("A core+spec-FIXING reg diffeo rho cannot cancel y0*delta1 (delta1 non-C1, y0 not")
print("identically 0).  => reg-block-only ContDiff rho CANNOT straighten E(Theta .) to E")
print("   UNLESS the leak is zero, i.e. UNLESS deepestEFull does NOT read the dragged core.")

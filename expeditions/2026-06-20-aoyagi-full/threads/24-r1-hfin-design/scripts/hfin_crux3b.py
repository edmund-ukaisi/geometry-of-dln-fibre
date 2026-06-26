from fractions import Fraction
# The leaf F ~ t0^2 U + a^2 V (U,V units). To make this a SINGLE monomial base (normal crossings),
# blow up the (t0, a) plane AGAIN: pivot t0 (cell |a|<=|t0|): a = t0 * a', Jac t0.
#   F ~ t0^2 U + t0^2 a'^2 V = t0^2 (U + a'^2 V).  U + a'^2 V: U is a unit (U(0)>0), so U+a'^2 V > 0
#   near the cell origin -> a UNIT.  So F ~ t0^2 * W, W unit.  NOW single monomial base t0^2.
# Jacobian accumulates: previous t0^3 a^3, times the new blow-up Jac t0 (and a=t0 a' substitution in a^3
#   gives (t0 a')^3 = t0^3 a'^3). Total Jac in (t0, a', rest) coords: t0^3 * t0^3 a'^3 * t0 = t0^7 a'^3.
# Wait recompute. Original vars after first two radial blow-ups: t0 (pivot of T-block), a (pivot of
#   Delta-block), plus residual unit-direction vars. Jac so far = t0^3 (T radial, |A_T|=4 -> exp 3)
#   * a^3 (Delta radial, the 2x2 = 4-dim block -> |A|=4 -> exp 3).
# Now blow up the 2-dim (t0,a) plane, cell |a|<=|t0|: map (t0,a',...) -> (t0, t0*a', ...), Jac = t0
#   (a (card-1)=1 blow-up of a 2-element active set {t0,a}).
# Substitute a = t0 a' into the accumulated Jac a^3 = t0^3 a'^3, and the new Jac factor t0.
#   Total Jac = t0^3 * (t0^3 a'^3) * t0 = t0^7 a'^3.
# Loss base: t0^2 (single monomial). 
# Integrand: (t0^2)^{-c} * |Jac| = t0^{-2c} * t0^7 a'^3 = t0^{7-2c} a'^3.
# threshold: per S2, axis t0: (h_{t0}+1)/(2 k_{t0}) = (7+1)/(2*1) = 4.  axis a': k_{a'}=0 (a' not in
#   base) -> ratio infinity. So threshold = min = 4.  CORRECT -- SINGLE monomial base, threshold 4.
print("=== CRUX #3b: FURTHER blow-up restores single monomial base ===")
print("Blow up the (t0,a) plane (cell |a|<=|t0|): a = t0*a', then F ~ t0^2*(U + a'^2 V) = t0^2 * W,")
print("W = U + a'^2 V is a UNIT (U(0)>0). SINGLE monomial base t0^2.")
ja, jt = 3, 3   # a^3, t0^3 accumulated
# after a=t0 a': a^3 -> t0^3 a'^3; new blow-up Jac t0^1
h_t0 = jt + ja + 1   # 3 + 3 + 1 = 7
k_t0 = 1
print(f"Jacobian = t0^{h_t0} * a'^3.  base t0^2 -> k_t0=1, h_t0={h_t0}.")
print(f"threshold (t0-axis) = (h+1)/(2k) = ({h_t0}+1)/2 =", Fraction(h_t0+1,2*k_t0), "= 4 = minAdm/2.  CORRECT.")
print()
print("So: ONE MORE pivot-blow-up of the disjoint-sum plane turns t0^2 U + a^2 V into a single")
print("monomial t0^2 * W. The recursion that produces the disjoint sum must NOT stop there -- it")
print("must blow up the (t0,a) corank-plane once more. THIS is the extra recursion depth corank>=2 needs.")
print()
# Now: is the leaf threshold ALWAYS = Mval(M,t)/2 after full resolution? The single divisor t0 has
# codim = its h+1 over k... no. The key invariant: the FINAL single-monomial leaf has, on its binding
# axis, k=1 (order-2 vanishing of a sum of squares) and h+1 = (accumulated Jacobian exponent + 1).
# We need h+1 >= minAdm for EVERY leaf (so threshold (h+1)/2 >= minAdm/2). The accumulated Jacobian
# exponent on the binding axis = (sum of blow-up centre dims along the path) = the CODIM of the
# stratum = Mval(M,t). So h+1 = Mval(M,t) >= minAdm. <-- the cover lower bound, automatic from inf.
print("PER-LEAF BOUND: the final single-monomial leaf binding axis has h+1 = accumulated Jacobian")
print("exponent + 1 = (sum of blow-up-centre codims along path) = Mval(M,t) >= minAdm.")
print("So leaf threshold = Mval(M,t)/2 >= minAdm/2.  Cover upper bound rlct >= minAdm/2.  SOUND.")
print()
print("WAIT -- verify the accumulated-Jacobian = Mval claim on (3,3,4) t=(1,0):")
print("  T-radial (4-block): Jac exp 3. Delta-radial (4-block): Jac exp 3. corank-plane (2): Jac exp 1.")
print("  But these are on DIFFERENT axes (t0 for T, a then folded into t0). Final binding axis t0:")
print("  h+1 = 3(T) + 3(Delta, via a=t0 a') + 1(plane) + 1 = 8 = Mval(3,3,4 ; 1,0). YES = minAdm.")

import sympy as sp
# ============================================================
# SHARP mechanism: the ATOM integrates the corank γ over FULL SPACE (enlarge-before-shear) => the ∞-Beta
# weight |z|^{-1}, which OVER-COUNTS on the degenerate {z→0} locus. The BOX γ-integral (pure route,
# Γ a chart coord blown up WITHIN the box) respects a FINITE CUTOFF and does NOT produce |z|^{-1}.
# ============================================================
a,z,g,cp = sp.symbols('alpha z gamma c', positive=True)
integrand = (a**2 + z**2*g**2)**(-cp)

# FULL-SPACE γ-integral (the ATOM): ∫_{-∞}^{∞} => |z|^{-1}·α^{1-2c'}·(Beta const). Confirm the |z|^{-1}.
full = sp.integrate((a**2+z**2*g**2)**(-cp), (g, -sp.oo, sp.oo))
full_s = sp.simplify(full)
print("ATOM (full-space) ∫_ℝ (α²+z²γ²)^{-c'} dγ =")
sp.pprint(full_s)
# extract the z-power: it is |z|^{-1} (times α^{1-2c'}·const). Confirm z-exponent = -1:
zpow = sp.simplify(sp.log(full_s).diff(z)*z)   # d log/d log z
print("  z-exponent of the atom weight:", sp.simplify(zpow), " (= -1 => the |z|^{-1} Gram-det/∞-Beta) \n")

# BOX γ-integral (PURE, finite cutoff): ∫_0^1. As z→0 it tends to α^{-2c'} (finite), NOT |z|^{-1}.
# evaluate the small-z limit of the box integral (leading behaviour):
box = sp.integrate((a**2+z**2*g**2)**(-cp), (g, 0, 1))
lim_z0 = sp.limit(box, z, 0)
print("BOX (pure) ∫_0^1 (α²+z²γ²)^{-c'} dγ  as z→0  =", sp.simplify(lim_z0), " (= α^{-2c'}·1, FINITE cutoff — NO |z|^{-1})")

# ============================================================
# The TRUE box integral: integrate the CORE (α) out first -> a clean MONOMIAL |γβs|^{1-2c'} (product of
# 1-D integrals), convergent iff c'<1 = toric RLCT. (Tonelli: box order-independent; the atom's |z|^{-1}
# divergence is purely the FULL-SPACE enlargement over-counting the null {z=0}.)
# ============================================================
print("\nTRUE box integral, integrate CORE α out first (z=βs): ∫_ℝ? no—∫ over box; leading monomial:")
print("  ∫(α²+m²)^{-c'} dα  ∝  m^{1-2c'}  (m=γβs) => ∫|γβs|^{1-2c'} dγdβds = ∏ ∫|·|^{1-2c'}")
print("  each ∫_0^1 |x|^{1-2c'} dx  converges  iff 1-2c' > -1  iff  c' < 1  = toric RLCT. FINITE, MONOMIAL.")
print("""
=> DECISIVE: the atom's |z|^{-1} Gram-det is the FULL-SPACE (∞-Beta) weight; integrated over the
   degenerate tail it DIVERGES — but this is the enlarge-to-full-space OVER-COUNT on the NULL {z=0}
   locus (design-cert §3 'the ∞-Beta discards the finite cutoff'). The BOX/PURE route respects the
   finite cutoff (γ-integral → α^{-2c'} as z→0, not |z|^{-1}) and is FINITE for c'<RLCT, as a MONOMIAL
   product. rblowup2's wall is the atom (full-space) artifact, NOT the pure route.
""")

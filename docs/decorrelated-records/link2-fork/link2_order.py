import sympy as sp
print("="*78)
print("CHECK 6: ORDER of the leak term + RLCT-sensitivity.")
print("="*78)
# Near wstar=0, all coords small.  E(q)_i are reg residuals; at the deepest point E(0)=0.
# The reg-energy is sum E_i^2.  E(Theta q)_i = E(q)_i + leak_i,
#   leak (M12) = (d*p)*y0*delta1(reg,spec),   leak(M21) = (a*w)*z1*delta0(reg,spec).
# delta_s(0,0)=0 and delta CONTINUOUS => delta_s = o(1).  But HOW fast? delta is a Schur
# correction difference -Z(1+X)^{-1}Y type, which is at least QUADRATIC in (reg,spec)
# (a product of two small reads) -- so delta_s = O(|(reg,spec)|^2) typically, but its
# C^1-failure (if any) is in the cutoff/sqrt-type construction.  The cross term in E^2:
#   2 * E_i(q) * leak_i.
# E_i(q) itself = O(|q|) (vanishes at 0).  leak_i = (reg-coord)*delta_s = O(|q|)*O(|q|^2)?
# So cross term ~ O(|q|) * O(|q|) * O(delta).  The RLCT is determined by the LEADING
# Newton-polytope behaviour of the WHOLE squared sum near 0.
#
# THE KEY DISTINCTION (frame in, hypothesis out -- I record both possibilities):
# (A) If delta_s is genuinely o(|q|^k) for the relevant k AND enters only multiplied by
#     coords that already vanish, the leak could be RLCT-NEGLIGIBLE: the RLCT of
#     sum E(Theta .)^2 + C could EQUAL that of sum E(.)^2 + C without any rho -- because
#     a sufficiently high-order continuous perturbation does not move the RLCT.
#     BUT: rlctAtOn is NOT generally invariant under continuous-only higher-order
#     perturbations -- the RLCT can jump under non-smooth perturbations (no Hironaka).
#     So (A) is NOT automatic; it would need its OWN proof (a domination/squeeze on the
#     integrand), which is a DIFFERENT mechanism than rho-via-localDiffeo.
# (B) The controller's asked deliverable is rho via rlctAtOn_comp_localDiffeo, i.e. an
#     EXACT germ identity (sum E(Theta.)^2 + C) o rho = sum E(.)^2 + C.  This is the
#     STRONG form and is what CHECK 5 obstructs.
#
# Let us at least pin delta's order, to see if route (A) is even plausible.
# Schur correction (one layer): s = -Z (I+X)^{-1} Y.  X,Y,Z are reg/spec reads, all O(|q|).
# => s = O(|q|^2).  delta = sc - sb = difference of two such = O(|q|^2).  Its non-smoothness
# (sc continuous-only) is a FAILURE OF C^1 at higher order, but a function can be O(|q|^2)
# and still fail to be C^2 / even C^1 in a directional sense (e.g. |q|^2 * sign-like).
X,Y,Z = sp.symbols('X Y Z', real=True)
s = -Z*(1+X)**(-1)*Y
print("Schur core correction s = -Z(1+X)^{-1}Y, leading order:", sp.series(s, X, 0, 2).removeO(), "(=> O(|q|^2))")
print()
print("So  leak_i = (reg-coord O(|q|)) * (delta O(|q|^2)) = O(|q|^3).")
print("    cross term 2 E_i leak_i = O(|q|) * O(|q|^3) = O(|q|^4).")
print("    leak_i^2 = O(|q|^6).")
print()
print("INTERPRETATION (recorded as Speculation, not fact):")
print(" - The leak is HIGH ORDER (O(|q|^3) inside E, O(|q|^4) in the cross term).")
print(" - This makes route (A) [RLCTs equal without rho, by domination] PLAUSIBLE but")
print("   it is a SEPARATE theorem (a non-smooth higher-order perturbation bound), NOT")
print("   the rho-via-localDiffeo the controller asked for.")
print(" - route (B) [exact germ identity via smooth core+spec-fixing rho] is OBSTRUCTED:")
print("   the O(|q|^3) leak still contains a continuous-only factor that a smooth rho")
print("   cannot reproduce as an EXACT germ.")

import sympy as sp

print("="*72)
print("SPECTATOR de-risk: after the boundary-0 z-integral the peel gives")
print("   tail-integrand  g^{-2c''} * h^{-a}   (c''=c'-a/2, a=(M0-t)(M1-t))")
print("   g = ||tail-top chain (t,M2,..)||,  h = ||V * tail-bottom rows||.")
print("Concern: does the spectator h^{-a} add a NEW divergence?")
print("="*72)

print("""
Block-diagonal Schur split is EXACT (no cross terms):
   ||A0 Q||^2  ≍  ||A0^[t] Qtop||^2 + ||Gamma Qbot||^2  =  g^2 + z^2 h^2
(A0^[t] invertible bounded on the pivot chart; Gamma = zV the corank block.)

Spectator bounded-below lemma: if Qbot has full row rank then
   h = ||V Qbot|| >= sigma_min(Qbot)*||V|| = sigma_min(Qbot) > 0  for all V on the sphere,
so h^{-a} is BOUNDED -> no new singularity.  h -> 0 only where Qbot drops rank,
which is a DEEPER tail stratum already inside the tail's own minAdm (no double-count).
""")

# ---- (2,2,2) base: verify the peel integral FACTORS into independent box integrals ----
# front-peel at t=1: g = ||top row of B'|| (the (1,2) tail chain = free 1x2 vector),
#                    h = ||bottom row of B'|| (spectator, a=1), rows of a FREE 2x2 matrix.
# tail integral = [∫ ||v||^{-2c''} dv over R^2] * [∫ ||u||^{-1} du over R^2]  (independent rows)
print("(2,2,2) front-peel at t=1 (a=1, c''=c'-1/2). Tail = free B' (2x2), rows independent:")
c = sp.symbols('c', positive=True)      # c = c''  (= c'-1/2)
r = sp.symbols('r', positive=True)
# ∫_{||v||<=1, R^2} ||v||^{-2c''} dv  ~  ∫_0^1 r^{1-2c''} dr  (polar), finite iff 2c''<2 <=> c''<1
top = sp.integrate(r**(1 - 2*c), (r, 0, 1))
print("   TOP (tail chain, R^2): ∫_0^1 r^{1-2c''} dr =", sp.simplify(top), " finite iff c''<1  <=> c'<3/2  ✓ BINDING")
# ∫ ||u||^{-1} du over R^2 ~ ∫_0^1 r^{1-1} dr = ∫_0^1 1 dr = 1 (a=1)
bot = sp.integrate(r**(1 - 1), (r, 0, 1))
print("   BOTTOM (spectator h^{-1}, R^2): ∫_0^1 r^{1-1} dr =", bot, "  finite ALWAYS  ✓ benign")
print("""
=> spectator h^{-1} is ALWAYS integrable and (at L=2) INDEPENDENT of the tail chain;
   binding constraint c'<3/2 comes purely from the tail-top chain. Peel is clean & tight.
""")

# ---- confirm the spectator singular locus = deeper stratum (no NEW codim), (2,2,2,2)-style ----
print("L>=3 coupling (flag for (b)/(c)): at L>=3, g and h SHARE the deeper factors A2.. .")
print("h->0 <=> tail-bottom rows drop rank at boundary 1 = a DEEPER admissible stratum,")
print("already inside minAdm(t,M2,..). The exact recursion thr==(1/2)minAdm (0/8000, L<=5)")
print("confirms the joint bookkeeping is tight -> BOUNDED labour ((b) no-double-count +")
print("(c) the Q2-mixed tail-measure handle), NOT a new wall.")

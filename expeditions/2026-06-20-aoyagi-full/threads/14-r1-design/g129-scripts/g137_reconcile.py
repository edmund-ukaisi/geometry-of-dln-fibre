import sympy as sp
# RECONCILE pp3's C2 + C3 with my #132 witness leg. Verify the two sharpening witnesses exactly.
print("=== C2: MISSED LATER-FACTOR stratum — (1,2,1), C1 full rank but C1·C2=0 ===")
# M=(1,2,1): C1 is 1x2, C2 is 2x1. product C1·C2 is 1x1 (scalar). 
x1,x2,y1,y2 = sp.symbols('x1 x2 y1 y2', real=True)
C1 = sp.Matrix([[x1,x2]]); C2 = sp.Matrix([[y1],[y2]])
P = sp.expand(C1*C2)  # scalar x1 y1 + x2 y2
f = sp.expand(P[0,0]**2)
print(f"  C1=(x1,x2) 1x2, C2=(y1,y2)ᵀ 2x1. product = {P[0,0]}, f = {f}")
print("  C1 can be FULL rank (rank 1 = max for 1x2) while C1·C2 = 0 (y ⊥ x). So the rank-DROP is in the")
print("  PRODUCT, not in C1's rank. A first-factor-rank-defect-only recursion blows up {C1=0} (codim 2)")
print("  and MISSES the stratum {C1·C2=0, C1≠0} (codim 1). ⟹ C2 (pass-through Schur) is REQUIRED.")
print("  rlct(f=(x1y1+x2y2)²): the zero-set {x·y=0} is a smooth hypersurface off 0, f vanishes to order 2")
print("  ⟹ rlct = 1/2 = ½·Mval(t=(1,0)), Mval=1. The missed stratum IS the minimiser here.")
print()
print("=== C3: k_E=2 at INTERSECTION blow-up — (1,1,1), f=x²y², blow up origin ===")
u,v = sp.symbols('u v', real=True)
# f = x²y²; chart x=u, y=u v (blow up origin)
f111 = (sp.Symbol('x')*sp.Symbol('y'))**2
fb = sp.expand(f111.subs({sp.Symbol('x'):u, sp.Symbol('y'):u*v}))
print(f"  f=x²y², chart (x,y)=(u,uv): f∘φ = {fb} = u⁴v² ⟹ k_E(u)=2 (NOT 1!), k_E(v)=1.")
print("  Jacobian |det Dφ| = |u| (∂(u,uv)/∂(u,v) = [[1,0],[v,u]], det=u). So h_u = 1.")
print("  axisRatio(h=1,k=2) for u = (1+1)/(2·2) = 2/4 = 1/2.  axisRatio(h=0,k=1) for v = 1/2.")
print("  min = 1/2 = ½·minAdm Mval (Mval=1 for (1,1,1) deepest). VALUE HOLDS, but k_E=2 ≠ 1.")
print("  ⟹ C3: the LOWER bound must use multiplicity-control m·k≤h+1 (axisRatio_ge_of_mult), NOT k_E=1.")
print()
print("=== RECONCILE with my #132 (which claimed k_E=1 via multilinearity) ===")
print("""
My #132 multilinearity argument (scaling ONE factor by x ⟹ F degree-2 in x ⟹ k=1) is correct FOR A
SINGLE-COORDINATE (homogeneous factor) blow-up. pp3's k_E=2 arises at an INTERSECTION/ORIGIN blow-up
(x=u, y=uv) where ONE exceptional coord u absorbs TWO factors' vanishing — that is the NORMAL-CROSSING
COMPLETION step (combining two already-separated divisors), NOT the per-factor rank-defect blow-up.
So both are right: per-factor blow-ups give k=1 (my multilinearity), but the NC-completion that turns
the union of divisors into a normal-crossing arrangement can produce k_E≥2 — and there the Jacobian
discrepancy h compensates so the RATIO stays = codim/2. The SOUND lower bound is C3's multiplicity-
control (m·k ≤ h+1 ⟹ ratio ≥ m/2), robust to k_E≥2 — NOT my "k_E=1 everywhere" (true only pre-NC-completion).
MY #132 OVERCLAIMED 'k_E=1 on every exceptional divisor'; the correct statement is 'k_E=1 on per-factor
rank-defect divisors; k_E≥2 possible at NC-completion, where the discrepancy compensates (mult-control)'.
""")

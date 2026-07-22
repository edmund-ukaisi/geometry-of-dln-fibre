"""
pnp-transport STAGE 3:
  (A) the (3,3,2,2) DOUBLE-boost residual: A1/A2/A3 at the second (δ=1) boost, and the
      max exponent of the twice-boosted divisor u13 in the residual (b-ratio => binary?).
  (B) a CLEAN abstract test of whether a δ=0 blockBlowupMap accumulation of w SURVIVES to
      produce w^2 at a later δ=1 boost of the SAME w (the joint-degree-in-center2 danger).
  (C) COUNTERMODELS: the case11 unprepared-shear R_bad (banked) + a case12 (Schur split) exercise.

Distinction under test: the RESIDUAL coord exponent (foldResid, b-ratio driven, t̃-reset) vs the
JACOBIAN / terminal M-exponent (foldB, accumulated M += runLen*resCols). boostReady is about the RESIDUAL.
"""
import sympy as sp

# ============================================================================
# (A) (3,3,2,2) double-boost residual at the SECOND (delta=1) boost (3,0).
#     b-chain there = (u11, u11*u12*u13) ; b_2/b_1 = u12*u13 (SQUAREFREE). The residual is the
#     recoordinatised layer-3 block B times the pending-boost column shear [[1,beta],[0, b2/b1]].
#     (Same anchor methodology validated for the single boost; here s = u12*u13, not just u12.)
# ============================================================================
print("="*70)
print("(A) (3,3,2,2) coupled-binder DOUBLE boost, residual at (3,0), pivot w=u13")
u11,u12,u13,beta = sp.symbols('u11 u12 u13 beta')
b00,b01,b10,b11 = sp.symbols('b00 b01 b10 b11')   # recoordinatised layer-3 block
B = sp.Matrix([[b00,b01],[b10,b11]])
s = u12*u13                       # b_2/b_1  (the b-chain ratio on the suffix row 2)
Rp = sp.expand(B * sp.Matrix([[1,beta],[0,s]]))
w = u13
center2 = [w, b00, b10]           # boost#2 center = {u13} U {layer-3 col-0}
support_only = [b01, b11]         # col-1 = support \ center
allv = (u11,u12,u13,beta,b00,b01,b10,b11)

def degc(f, xs): return max([sum(m) for m in sp.Poly(sp.expand(f),*xs).monoms()],default=0)
def maxexp(f, x):
    P=sp.Poly(sp.expand(f),*allv); xi=P.gens.index(x)
    return max([m[xi] for m in P.monoms()],default=0)

A1 = all(sp.expand(f).subs({x:0 for x in center2},simultaneous=True)==0 for f in Rp)
A2 = all(degc(f,center2)<=1 for f in Rp)
pulled=[sp.expand(f.subs({b00:w*b00,b10:w*b10},simultaneous=True)) for f in Rp]
A3 = all(sp.expand(g.subs(w,0))==0 and sp.cancel(g/w).is_polynomial(*allv) for g in pulled)
maxw = max(maxexp(f,w) for f in Rp)
print(f"  A1={A1}  A2 (joint deg<=1 in center2, incl w)={A2}  A3 (w | after boost)={A3}")
print(f"  MAX exponent of w=u13 in any residual monomial: {maxw}   (b-chain squarefree => expect 1)")
for i,f in enumerate(Rp): print(f"    R[{i}] = {sp.expand(f)}")
assert (A1,A2,A3)==(True,True,True), "double-boost NOT boost-ready"
assert maxw==1, "u13 appears with exponent >1 in the residual!"
print("  => residual u13-exponent is BINARY (=1 on suffix col-1); A2 holds; NO w^2.")
print("  NOTE: u13's JACOBIAN/terminal exponent here is M=4 (accumulated over 2 boosts) -- a")
print("        DIFFERENT quantity living in foldB/Jacobian, NOT in the residual.")

# ============================================================================
# (B) Does a delta=0 blockBlowupMap accumulation of w produce a SURVIVING w^2 at a later
#     delta=1 boost of the SAME w?  Faithful abstract model of the mechanism:
#     - parent residual r0 Deg1-supported on center1 = {w, g0} (an EARLIER/current layer block),
#       with a b-ratio suffix term carrying w (models b_i/b_1).
#     - BOOST#1 (delta=0, pivot w): r1 = r0 . blockBlowupMap(center1, w)  [multiplies center1 coords by w].
#     - the layer-1 block coord g0 is then CLEARED (absorbed) before boost#2: model absorption by the
#       strict-transform quotient of g0's own blow-up (g0 -> its exceptional, removed from the residual).
#     - BOOST#2 (delta=1, pivot w): test Deg1-on-center2 = {w, h0} (a DIFFERENT layer block) + max w-exp.
# ============================================================================
print("\n"+"="*70)
print("(B) abstract: delta=0 accumulation of w, then absorption, then delta=1 boost of same w")
w,g0,g1,h0,h1,c1,c2,c3 = sp.symbols('w g0 g1 h0 h1 c1 c2 c3')
def bbmap(expr, center, piv, subs_syms):
    # blockBlowupMap: piv->piv ; j in center -> piv*j ; else j.  (apply as substitution)
    sub = {j:(piv*j) for j in center if j!=piv}
    return sp.expand(expr.subs(sub, simultaneous=True))
# parent residual r0 on center1={w,g0}: a col-0 term (g0, no w) + a suffix col-1 term carrying w via b-ratio.
# (h0,h1 = deeper/next-layer coords appearing in coefficients; c_i = free.)
r0 = c1*g0 + w*(c2*g1)            # g0 in center1 (col-0); g1 is support-only (col-1) carrying b-ratio w
print(f"  r0 = {r0}   (center1={{w,g0}}; g1 carries b-ratio w)")
# BOOST#1 delta=0, pivot w, center1={w,g0}: multiply center1 coords by w
r1 = bbmap(r0, [w,g0], w, None)
print(f"  r1 = r0 . blockBlowupMap(center1,w) = {r1}")
print(f"       max w-exp in r1 = {sp.Poly(r1,w,g0,g1,c1,c2,c3).degree(w)}")
# ABSORB g0 (it is cleared into the b-chain): the fold removes g0 as a free residual coord.
# Its w-factor goes into diag(b) (already counted). Model: g0 -> 0 in the *residual* (cleared slot),
# OR g0 -> a fresh next-layer coord. Either way g0 no longer a center2 coord. Take the honest bound:
# the SURVIVING residual entries at boost#2 are the NON-cleared slots. The cleared g0-slot becomes a unit.
# The surviving suffix slot is w*c2*g1 (unchanged by boost#1 since g1 not in center1).
r_survive = w*c2*g1
print(f"  surviving (non-cleared) residual slot into boost#2: {r_survive}")
# BOOST#2 delta=1, pivot w, center2={w,h0}: is r_survive Deg1-on-center2 with w-exp<=1?
center2b=[w,h0]
# r_survive reads g1 (support-only, next-layer) and carries w^1 via b-ratio; h0 not present here.
maxw_surv = sp.Poly(r_survive, w,g1,c2).degree(w)
A2b = (sp.Poly(r_survive, w,h0,g1,c2).degree(w) + sp.Poly(r_survive,w,h0,g1,c2).degree(h0)) <=1 \
      or all(sum(m[:2])<=1 for m in sp.Poly(r_survive,w,h0,g1,c2).monoms())  # joint deg in {w,h0}
print(f"  max w-exp in surviving slot = {maxw_surv}  ; joint deg in center2={{w,h0}} <=1 : {A2b}")
print("  => the delta=0 w-factor lands on the CLEARED slot (absorbed into diag(b)); the SURVIVING")
print("     suffix slot carries w^1 from the b-ratio only.  NO w^2 survives.  (INFERENCE-level model;")
print("     the exact (3,3,2,2) verdict is part (A) above, where max w-exp = 1 is OBSERVED.)")

# ============================================================================
# (C) COUNTERMODELS
# ============================================================================
print("\n"+"="*70)
print("(C1) case11 UNPREPARED-SHEAR countermodel R_bad (banked): full-support Deg1 but NOT boost-ready")
u12b,betab,gammab = sp.symbols('u12 beta gamma')
b00,b01,b10,b11 = sp.symbols('b00 b01 b10 b11'); z00,z01,z10,z11=sp.symbols('z00 z01 z10 z11')
Bm=sp.Matrix([[b00,b01],[b10,b11]]); Zm=sp.Matrix([[z00,z01],[z10,z11]])
C=[u12b,b00,b10]; Sfull=[b00,b01,b10,b11]; allc=(u12b,betab,gammab,b00,b01,b10,b11,z00,z01,z10,z11)
R_bad = sp.expand(Zm*Bm*sp.Matrix([[1,betab],[gammab,u12b]]))   # gamma != 0: UNPREPARED (no Schur)
def degset(f,xs): return set(sum(m) for m in sp.Poly(sp.expand(f),*xs).monoms())
a1_bad = all(sp.expand(f).subs({x:0 for x in C},simultaneous=True)==0 for f in R_bad)
fullsupp_deg1 = all(degset(f,Sfull)=={1} for f in R_bad)
print(f"  R_bad full-support-Deg1 (each entry deg exactly 1 in the B-block): {fullsupp_deg1}")
print(f"  R_bad A1 (vanish at center=0): {a1_bad}   <-- FALSE: gamma*(b01*z00+b11*z01) survives")
print(f"  witness R_bad[0,0]|_(center=0) = {sp.expand(R_bad[0,0]).subs({x:0 for x in C},simultaneous=True)}")
assert fullsupp_deg1 and (a1_bad is False), "R_bad countermodel unexpected"
print("  => full-support-Deg1 does NOT imply boost-ready; the SCHUR-prepared shear (gamma=0 via")
print("     IsRealBranch's shear pin / CanonicalSchurStep) is REQUIRED. matches codex boost-2222.")

print("\n(C2) case12 (SPLIT) exercise: the Schur shear is LIVE (edgeShear=blockShear), new divisor v.")
print("     The residual at a case12 delta=1 clear factors via the Q-hat/weightedCofactor transport;")
print("     divisibility by the NEW pivot v is by blockBlowupMap_center_eq directly (cover route,")
print("     supportAt SUBSET ed.center), so boost-readiness is NOT needed for case12 -- padding only.")
# demonstrate the cover-route triviality: supportAt subset center => Deg1 on support => Deg1 on center by padding
gA,gB,pv = sp.symbols('gA gB v')
r_c12 = c1*gA + c2*gB                          # Deg1 on support {gA,gB}
center_c12 = [gA,gB,pv]                         # center = support U {new pivot v}  (supportAt SUBSET center)
pad_ok = all(sum(m[:2])<=1 for m in sp.Poly(sp.expand(r_c12),gA,gB,pv,c1,c2).monoms())
print(f"  case12: supportAt={{gA,gB}} SUBSET center={{gA,gB,v}}; Deg1-on-center by zero-padding v: {pad_ok}")
assert pad_ok
print("\nSTAGE 3 PASS")

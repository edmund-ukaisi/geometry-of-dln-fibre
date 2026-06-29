import sympy as sp
print("="*70); print("AFFINE-RADIAL DESIGN check on the CONCRETE genBlkFlatLiveR1 (L=2)"); print("="*70)
# (2,2,2) concrete: φ has the fixed-pivot anchor u·1 at A0[1,1]. minAdm=3, so u^{minAdm-1}=u^2.
# Active (corrected): {pivot p} ∪ {E-FREE excl (0,0)} ∪ {leaf}. At (2,2,2): r1=c1=1 ⟹ E-block 1×1 = JUST (0,0)
#   anchor (NO E-free). leaf = Text_2·Wext_2 = 1·2 = 2 coords (minus 1 anchor-reroute? per the pin).
# minAdm-1 = 2 = the scaled directions. Let's identify them concretely.
x = sp.symbols('x0:8', real=True); u = x[0]
# φ (concrete, fixed pivot): A0[1,1] = x5*x1 + u·1 (anchor); leaf carries freed DOF.
A0 = sp.Matrix([[x[4], x[4]*x[1]], [x[5], x[5]*x[1] + x[0]]])           # anchor: +u·1 = +x0
A1 = sp.Matrix([[x[0]-x[1]*x[2], x[0]*x[6]-x[1]*x[3]], [x[2], x[3]]])   # leaf x6 (u-scaled), x7-rerouted
F = [A0[0,0],A0[0,1],A0[1,0],A0[1,1],A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
# ---- AFFINE RADIAL model ----
# R (radial): pivot x0↦x0; multiplicative on active E-free+leaf (x6); the ANCHOR is handled by an
#   ADDITIVE term in B (B reads the anchor output as "+ (radial pivot coord)"). 
# Actually the affine-radial hypothesis: R is AFFINE — R outputs include the anchor as an additive u.
# Cleanest realizable: B = de-radialized chart NOT reading anchor (anchor output = the CONSTANT from B's
#   structure is 0, and R supplies +u). Let me test: is φ = B ∘ R_affine with R_affine the pivotBlowup
#   that ALSO injects the anchor additively?
# Model R_affine: same as pbo on coords, but it's a MAP (Fin8→Fin8); the anchor u·1 is an OUTPUT of φ not
#   a coord. So the split must be at the CHART level: φ = (B reading blown coords) where B's A0[1,1] term
#   that was "+anchor" is now "+ R's pivot-derived value". 
# THE REALIZABLE B (de-radialized, NO anchor read): B's A0[1,1] = x5*x1 + 0 (anchor block ABSENT in B),
#   and the affine radial layer ADDS u at that output position.
# Test the DET of the affine radial layer: D(R_affine) where R_affine = pivotBlowupOn(active) + (additive u
#   into the anchor-output direction). The additive constant has ZERO derivative ⟹ D(R_affine)=D(pbo) ⟹
#   det = u^{minAdm-1} REGARDLESS of the affine shift! (affine map's Jacobian = linear part's Jacobian)
active = {0, 6}   # pivot + the one scaled leaf direction (minAdm-1 = 2 means we need 2 scaled... check card)
print("minAdm=3, minAdm-1=2. active (scaled, excl pivot) should have card 2.")
# Hmm at (2,2,2): the scaled directions (E-free + leaf, minus pivot) must be 2. E-free=0 (1x1 anchor only),
# leaf = 2 coords. So active = {pivot 0} ∪ {2 leaf coords}, card 3 = minAdm ✓. scaled = 2 = minAdm-1 ✓.
# Let leaf coords be x6, x7 (both u-scaled in φ's A1). Re-examine φ's A1: x0*x6 and... x7?
# φ A1[0,1] = x0*x6 - x1*x3 (x6 leaf, u-scaled). Need a 2nd leaf coord. Let A1 carry x7 too:
A1 = sp.Matrix([[x[0]-x[1]*x[2], x[0]*x[6]-x[1]*x[3]], [x[2], x[0]*x[7]+x[3]]])  # x6,x7 both u-scaled leaf
F = [A0[0,0],A0[0,1],A0[1,0],A0[1,1],A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
active = {0,6,7}  # pivot + 2 leaf; card 3 = minAdm; scaled (excl pivot) = {6,7} card 2 = minAdm-1
def pbon(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(8)]
Rlin = pbon(active,0,x)   # the LINEAR (multiplicative) part of the radial; anchor additive handled in B/affine
# det of the radial: the affine shift (anchor +u) has 0 derivative, so det D(radial) = det D(pbon) = u^2.
Jpbon = sp.Matrix(Rlin).jacobian(sp.Matrix(x))
print("det D(pivotBlowupOn active) =", sp.factor(Jpbon.det()), "  (= u^2 = u^{minAdm-1}?)", sp.simplify(Jpbon.det()-u**2)==0)
# Now: realizable B = de-radialized chart where the anchor output gets +x0 from the RADIAL pivot coord.
# B reads blown coords; B's A0[1,1] = (x5,x1 unchanged) + b0  where b0 = R's pivot output = x0. This IS realizable
# if B is "the chart whose anchor block reads the PIVOT coordinate output" — i.e. B reads coord 0 additively there.
# That's NOT genBlkFlatLiveR1 (fixed const). Is it a REALIZABLE decoder? It reads x0 (the pivot) at the anchor.
# det DB (B u-free? the engine): B's Jacobian — does it = engine (det≠0)?
b = sp.symbols('y0:8', real=True)
A0b = sp.Matrix([[b[4], b[4]*b[1]], [b[5], b[5]*b[1] + b[0]]])   # B reads anchor additively from coord b0
A1b = sp.Matrix([[b[0]-b[1]*b[2], b[6]-b[1]*b[3]], [b[2], b[7]+b[3]]])
B = [A0b[0,0],A0b[0,1],A0b[1,0],A0b[1,1],A1b[0,0],A1b[0,1],A1b[1,0],A1b[1,1]]
Brad = [bb.subs({b[i]: Rlin[i] for i in range(8)}) for bb in B]
print("φ == B(pivotBlowupOn)? (B reads anchor additively from pivot coord)", all(sp.simplify(F[i]-Brad[i])==0 for i in range(8)))
JB = sp.Matrix(B).jacobian(sp.Matrix(b))
print("det DB =", sp.factor(JB.det()), "  (u-free, ≠0 generically?)")

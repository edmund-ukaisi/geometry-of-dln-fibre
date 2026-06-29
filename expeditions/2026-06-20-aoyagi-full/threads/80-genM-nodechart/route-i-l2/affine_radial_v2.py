import sympy as sp
print("AFFINE-RADIAL v2: the anchor u lives in the RADIAL layer (additive), B does NOT read it")
x = sp.symbols('x0:8', real=True); u = x[0]
# φ: A0[1,1] = x5*x1 + u·1 (anchor); A1 leaf x6,x7 u-scaled.
A0 = sp.Matrix([[x[4], x[4]*x[1]], [x[5], x[5]*x[1] + x[0]]])
A1 = sp.Matrix([[x[0]-x[1]*x[2], x[0]*x[6]-x[1]*x[3]], [x[2], x[0]*x[7]+x[3]]])
F = [A0[0,0],A0[0,1],A0[1,0],A0[1,1],A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
# Decompose φ = AFFINE_RADIAL ∘ B   where:
#   B (u-FREE, de-radialized, NO anchor): B's A0[1,1] = x5*x1 (NO +anchor); leaf reads x6,x7 (un-scaled).
#   AFFINE_RADIAL: a map (Fin8→Fin8) acting on B's OUTPUT — it must (a) scale the leaf-output directions by u,
#     (b) ADD u at the anchor output position. But AFFINE_RADIAL acts on OUTPUTS (Fin8 of A0,A1 entries),
#     and the leaf-scaling is on B's leaf coords, the anchor-add is on the A0[1,1] output. Different spaces!
# The clean structural truth: φ = B ∘ R is the RIGHT order (R on INPUT coords, B reads R's output).
#   R must produce: scaled actives (mult) AND an extra coordinate carrying u for the anchor.
#   But the anchor is an OUTPUT of φ (A0[1,1]), built by B from B's inputs. For B (u-free) to produce
#   "x5*x1 + u" at A0[1,1], B must READ a coordinate equal to u there. R supplies it: R has an output coord = x0
#   that B reads additively at the anchor. That coord is the PIVOT (x0). So B reads x0 at the anchor → the
#   det-0 problem (x0 read at anchor AND as the pivot-direction). UNLESS B reads a DIFFERENT R-output coord
#   that R sets to x0 — i.e. R DUPLICATES x0 into a fresh slot. But Fin8→Fin8 R can't add dimensions.
# CONCLUSION test: is there ANY u-free B + radial R (det u^2) with φ=B∘R and det DB≠0? 
# The anchor needs a "+u" that B reads from some R-output. If that R-output is x0 (pivot), det DB=0 (shown).
# If R sets some OTHER slot j (currently a spectator/non-active) to x0, then B reads slot j at anchor:
xb = sp.symbols('y0:8', real=True)
# B reads slot 3 (a spectator) at the anchor additively; B u-free elsewhere:
A0b = sp.Matrix([[xb[4], xb[4]*xb[1]], [xb[5], xb[5]*xb[1] + xb[3]]])  # anchor reads slot y3
A1b = sp.Matrix([[xb[0]-xb[1]*xb[2], xb[6]-xb[1]*xb[3]], [xb[2], xb[7]+xb[3]]])  # but y3 ALSO used here (x1*x3)... 
# y3 is used in A1 already (the -x1*x3 terms). So reading y3 at anchor too → still coupled. 
# The deep issue: φ's anchor u·1 has NO free coordinate to carry it — every slot is used. The fixed pivotEIndicator
# is a CONSTANT precisely so it needs NO coordinate. So a u-free B CANNOT produce the anchor's u without
# stealing a coordinate (→ det 0) OR the radial must be AFFINE (carry u·1 as a constant-shift, not via B).
print("Structural: φ's anchor u·1 needs a coord to carry u in a u-free B → steals a DOF → det DB=0.")
print("⟹ B u-free is IMPOSSIBLE as a local iso with the anchor. The anchor u MUST be in the radial layer.")
# AFFINE radial as the RIGHT model: R_affine(x) = pivotBlowup(x) but the chart is φ = B ∘ R where B is
# applied and THEN an affine shift adds u·1 at the anchor OUTPUT. i.e. φ = (shift_u ∘ B ∘ pbo) where
# shift_u adds u at one output. But shift_u depends on u=x0 (the INPUT pivot), not on B's output → it's
# φ = (fun y => B(pbo y) + u·e_anchor). Then Dφ = D(B∘pbo) + (du)·e_anchor ⊗ e_p (rank-1 affine term).
# det Dφ: is it u^2·det(DB)? The rank-1 additive term changes det. TEST:
def pbon(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(8)]
active={0,6,7}; rad=pbon(active,0,x)
# B u-free, NO anchor (A0[1,1]=x5*x1 only):
A0B = sp.Matrix([[xb[4], xb[4]*xb[1]], [xb[5], xb[5]*xb[1]]])
A1B = sp.Matrix([[xb[0]-xb[1]*xb[2], xb[6]-xb[1]*xb[3]], [xb[2], xb[7]+xb[3]]])
BB = [A0B[0,0],A0B[0,1],A0B[1,0],A0B[1,1],A1B[0,0],A1B[0,1],A1B[1,0],A1B[1,1]]
Bpbo = [bb.subs({xb[i]: rad[i] for i in range(8)}) for bb in BB]
# φ = B(pbo) + u at anchor (index 3):
phi_aff = [Bpbo[i] + (u if i==3 else 0) for i in range(8)]
print("φ == B(pbo) + u·e_anchor ?", all(sp.simplify(F[i]-phi_aff[i])==0 for i in range(8)))
# det of φ_aff (the affine-shifted composite):
Jphi = sp.Matrix(F).jacobian(sp.Matrix(x))
print("det Dφ (actual) =", sp.factor(Jphi.det()))
JB = sp.Matrix(BB).jacobian(sp.Matrix(xb))
print("det DB (u-free, no anchor) =", sp.factor(JB.det()), " engine? (expect the K-core/leaf product)")
print("u^2 · det DB =", sp.factor(u**2 * JB.det().subs({xb[i]:rad[i] for i in range(8)})) if False else "see below")

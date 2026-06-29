import sympy as sp
# Diagnose: the full chart det = K^2 u^2 (RANK FULL, det != 0). So the chart IS a local iso generically.
# But B (de-radialized, leaf-only blowup) has det 0. So the leaf-only-blowup split is WRONG.
# The pivot u's DOF must be captured by the RADIAL map (as a genuine blow-up direction), not left to B.
# The E(0,0) output = u*1 = u (depends on the pivot coord u). For B to be a local iso, the radial map 
# must "consume" the u-direction. The CORRECT affine-radial: the radial map should map the pivot coord
# to the E(0,0) OUTPUT direction (additive) AND blow up the leaf. 
#
# KEY: at the achiever center, the codim-minAdm normal directions are: the E(0,0) direction (1, the radial
# pivot's own) + the leaf directions (minAdm-1). The radial blow-up pivotBlowupOn(active, p) with 
# active = {pivot's-own-slot} ∪ {leaf} would need a pivot SLOT distinct from the E(0,0). 
# But the fixed-pivot decoder has NO free coord at E(0,0) -- the pivot u IS a separate coord (structPivot)
# that feeds u*1. So the radial map sends: u -> u (pivot row), and the E(0,0) OUTPUT = u. 
# The leaf coords -> u*leaf. The structPivot coord u is DISTINCT from E(0,0) (which is the literal 1).
#
# So pivotBlowupOn(active={leaf}, p=u) sends u->u, leaf->u*leaf. Its OUTPUT has the pivot u at the u-SLOT.
# But the chart's E(0,0) OUTPUT = u is at a DIFFERENT output position (the E(0,0) matrix entry), NOT the u-slot.
# So B must MOVE the pivot u from the u-input-slot to the E(0,0)-output-slot. That's a PERMUTATION/relabeling
# in B -- which is fine (det ±1) IF B is still a bijection. Let me check: is the issue that B maps the
# u-input to E(0,0)-output, leaving the u-OUTPUT slot unfilled? 
# In the chart, what is at the "u-slot" output? structPivot=x0 is an INPUT coord. Its corresponding OUTPUT?
# The chart output has 8 entries (A0:4, A1:4). The pivot u appears in: E(0,0) of C1 (A0) = u (additive).
# Does u appear ANYWHERE else? Let me check the full chart's u-dependence.
u,K,X,N,W0,W1,lf0,lf1 = sp.symbols('u K X N W0 W1 lf0 lf1', real=True)
allv=[u,K,X,N,W0,W1,lf0,lf1]
Bmat1=sp.Matrix([[K],[X*K]]); qN1=sp.Matrix([[1,N]]); W=sp.Matrix([[W0,W1]]); lf=sp.Matrix([[lf0,lf1]])
R1u=sp.Matrix([[0,0],[0,u]]); C2=u*lf; C1=Bmat1*qN1+R1u; A0=C1; A1=sp.Matrix.vstack(C2-N*W,W)
phi=[sp.expand(e) for A in (A0,A1) for e in A]
print("Full chart outputs (2,2,2) Fix B:")
for i,e in enumerate(phi): print(f"  out[{i}] = {e}")
print()
print("u appears in:", [i for i,e in enumerate(phi) if u in e.free_symbols])
# The full det != 0, so the map IS a local iso. The CORRECT radial: pivotBlowupOn must use a pivot p
# whose OWN output is non-degenerate. The E(0,0) output = u. So treat E(0,0)-output's PREIMAGE: the pivot
# coord u maps to it. The radial map should be: pivotBlowupOn(active={leaf}∪{?}, p=u) where the pivot row
# u->u provides the E(0,0)=u. Then B reads E(0,0) <- u (the pivot slot). That's what I did -> det B =0.
# So the degeneracy is REAL for the leaf-only split. The fix must be a DIFFERENT active or B structure.

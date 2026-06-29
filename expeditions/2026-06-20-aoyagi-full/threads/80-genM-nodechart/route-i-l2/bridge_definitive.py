import sympy as sp
print("="*72); print("DEFINITIVE: does phiFlatLiveR1 M222 (genBlkFlatLiveR1) factor as B ∘ pivotBlowupOn,")
print("with B u-free local-iso (det=engine)? Compute the ACTUAL chart from Cgen/Agen + test."); print("="*72)
# genBlkFlatLiveR1 M222 blocks (slot-reader coords; assign fresh symbols per reader slot):
# Boundary 1 (k=0): K=readK [a] (1x1), X=readX [b] (1x1), N=readN [n] (1x1), W=readW [w0,w1] (1x2),
#   Rmat1 = FIXED rmatPad(pivotEIndicator) = [[0,0],[0,1]], Rfin2 = LIVE [lf0,lf1] (1x2).
# radial u = x_structPivot. The pivot slot p: structPivot — a coordinate. Call it 'u'.
u,a,b,n,w0,w1,lf0,lf1 = sp.symbols('u a b n w0 w1 lf0 lf1')
Bmat1 = sp.Matrix([[a],[b*a]]); qN1 = sp.Matrix([[1,n]])
C1 = Bmat1*qN1 + u*sp.Matrix([[0,0],[0,1]])     # fixed pivot
C2 = u*sp.Matrix([[lf0,lf1]])                    # live leaf
N1 = sp.Matrix([[n]]); W1 = sp.Matrix([[w0,w1]])
A0 = C1                                          # boundary 0 identity: Agen0 = C1
A1 = sp.Matrix.vstack(C2 - N1*W1, W1)            # [C2 - N·W ; W]
# φ flat coords (8 entries; via some pack, but det is pack-invariant so use the 8 A-entries):
F = [A0[0,0],A0[0,1],A0[1,0],A0[1,1], A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
# Map them to coords: pick a coord layout. The 8 free symbols a,b,n,w0,w1,lf0,lf1 + u = 8 coords.
coords = [u,a,b,n,w0,w1,lf0,lf1]
# Jacobian of φ in these 8 coords:
J = sp.Matrix(F).jacobian(sp.Matrix(coords))
detphi = sp.factor(J.det())
print("det Dφ (phiFlatLiveR1 M222) =", detphi)
# Now: radial active = {u} ∪ {the u-scaled coords}. u-scaled in F: lf0,lf1 (in C2=u·leaf). The fixed +u at
# A0[1,1] is the pivot's OWN contribution. So active = {u, lf0, lf1}? card 3 = minAdm(222)=3 ✓. 
# Test: is det Dφ = u^2 · (engine, u-free)? minAdm-1 = 2.
print("  Is det Dφ = ±u^2 · (u-free)?", )
q = sp.simplify(detphi / u**2)
print("  detφ/u^2 =", sp.factor(q), " (u-free?", u not in q.free_symbols, ")")
# If u-free: the engine. And B = the u-free part is a local iso iff that ≠0 generically.

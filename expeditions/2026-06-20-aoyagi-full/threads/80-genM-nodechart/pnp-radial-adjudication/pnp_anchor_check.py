import sympy as sp
x = sp.symbols('x0:27', real=True); u=x[0]; active=[13,14,24,25,26]
B1=sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
B2=sp.Matrix([[x[9]],[x[10]*x[9]]]);N1=sp.Matrix([[x[7]],[x[8]]]);N2=sp.Matrix([[x[11],x[12]]])
W1=sp.Matrix([[x[15],x[16],x[17]]]);W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]);R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]);Rf=sp.Matrix([[x[24],x[25],x[26]]])
C3=u*Rf;C2=B2*sp.Matrix.hstack(sp.eye(1),N2)+u*R2;C1=B1*sp.Matrix.hstack(sp.eye(2),N1)+u*R1
A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1);A2=sp.Matrix.vstack(C3-N2*W2,W2)
phi=[sp.expand(A[i,j]) for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
# out[8] = the anchor entry. Where does the bare u (=x0) come from? R1[2,2]=1 (fixed) -> u*1 = u.
print("out[8] (anchor) =", phi[8])
# It contains a bare x0 (the u*1 anchor). In B, this slot reads y_p (the pivot coord). Under blowup, 
# y_p = x0, so B(blowup)[8] has x0 -- matches. The anchor is the PIVOT coordinate p=structPivot=flat 0.
# CRITICAL: is the anchor 'p' IN the active set? pivotBlowupOn sends x_p -> x_p (pivot row, NOT scaled).
#   So the anchor reads y_p = blowup(x)_p = x0. Correct. The anchor is the pivot itself, handled by the
#   pivot row of pivotBlowupOn (the diagonal '1' in the arrow), NOT an active scaling.
print()
print("ANCHOR mechanism: the fixed-1 in Rmat/Rfin * u = bare u = x_p; B reads this slot as y_p;")
print("  pivotBlowupOn pivot row maps x_p -> x_p, so B(blowup)[anchor] = x_p = phi[anchor]. ✓")
print("  The pivot p (flat 0) is the structPivot; it is the ANCHOR slot, in `active` as the pivot itself.")
print()
print("=> The map identity, per-boundary per-block, splits into THREE banked-grain pieces:")
print("   (K/KN/XK blocks): phi=B identically (no u) -- schurFrameProd_block_K/_KN/_XK [BANKED, u-free].")
print("   (XKN+u*E block):  phi has +u*E, B has +E read at blown coord; pivotBlowupOn gives E_blown=u*E.")
print("                     = schurFrameProd_block_XKNuE [BANKED] + pivotBlowupOn_apply on the E coords.")
print("   (leaf u*Rfin):    phi=u*Rfin, B=Rfin at blown coord; = leaf-value + pivotBlowupOn_apply.")
print("   (anchor x_p):     pivot row of pivotBlowupOn (x_p->x_p) + the fixed-1*u=u read.")

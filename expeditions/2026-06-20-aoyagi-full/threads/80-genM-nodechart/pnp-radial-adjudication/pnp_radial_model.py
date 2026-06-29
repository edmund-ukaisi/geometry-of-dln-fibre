import sympy as sp

print("="*70)
print("Q1: THE RADIAL-COORDINATE MODEL.  Is V 0 = R^{minAdm}, and which coords?")
print("="*70)

# The radial layer is a pivotBlowupOn(active, p=structPivot) with active.card = minAdm.
# Mechanism: the chart's 'u' (=x0) multiplies the FIXED-1 pivots in the Rmat/Rfin blocks.
# Each such 'u*(slot)' is a blown-up coordinate: slot_i -> u * slot_i.
# active = {pivot p} ∪ {the coords that get multiplied by u via R/Rfin}.

# ===================== (2,2,2) =====================
# minAdm = 3, radial active = {0,6,7}.  pivot = 0.
# Where does u (=x0) appear as a multiplier u*coord in the chart?
#   chartA0[1,1] = x5*x1 + x6*x0   -> the u*R term is x6*x0 = u * x6   (Rmat1 = e22, x6 the free E entry)
#   chartA1[0,0] = x0 - x1*x2      -> x0 itself (= u, the pivot leaf C3 = u*Rfin)
#   chartA1[0,1] = x0*x7 - x1*x3   -> x0*x7 = u * x7   (Rfin leaf: C3 = u*[1, x7])
# So the THREE coords multiplied by u (after the shear strips the bilinear -x1*x2, -x1*x3, +x5*x1):
#   coord 0 (the pivot leaf '1'), coord 6 (the E-block free entry), coord 7 (the Rfin leaf free entry).
# => active = {0, 6, 7}, card = 3 = minAdm.  CONFIRMED.
print("\n(2,2,2): u-multiplied coords (post-shear): 0 (pivot leaf), 6 (E block), 7 (Rfin leaf).")
print("         active = {0,6,7}, card 3 = minAdm. radial det = |u0|^2.")

# ===================== (3,3,3,3) =====================
# minAdm = 6, pivot = 0.  Predict radial active.card = 6.
# Build the chart symbolically, then find the u-blow-up structure by examining 
# d(F)/d(x0) structure: the radial coords are those where x0 appears LINEARLY as u*coord.
x = sp.symbols('x0:27', real=True)
u = x[0]
B1 = sp.Matrix([[x[1], x[1]*x[2]],[x[1]*x[3], x[1]*x[2]*x[3] + x[4]],
                [x[1]*x[3]*x[6] + x[1]*x[5], x[1]*x[2]*x[5] + x[6]*(x[1]*x[2]*x[3] + x[4])]])
B2 = sp.Matrix([[x[9]],[x[10]*x[9]]])
N1 = sp.Matrix([[x[7]],[x[8]]]); N2 = sp.Matrix([[x[11], x[12]]])
W1 = sp.Matrix([[x[15], x[16], x[17]]]); W2 = sp.Matrix([[x[18], x[19], x[20]],[x[21], x[22], x[23]]])
R1 = sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]); R2 = sp.Matrix([[0,0,0],[0,x[13],x[14]]])
Rfin3 = sp.Matrix([[x[24], x[25], x[26]]])
chainQ_N1 = sp.Matrix.hstack(sp.eye(2), N1); chainQ_N2 = sp.Matrix.hstack(sp.eye(1), N2)
C3 = u*Rfin3; C2 = B2*chainQ_N2 + u*R2; C1 = B1*chainQ_N1 + u*R1
A0 = C1; A1 = sp.Matrix.vstack(C2 - N1*W1, W1); A2 = sp.Matrix.vstack(C3 - N2*W2, W2)
F=[]
for A in (A0,A1,A2):
    for i in range(A.rows):
        for j in range(A.cols):
            F.append(sp.expand(A[i,j]))

# Find which output entries have a term that is exactly  u * (single coordinate x_k), k != 0,
# i.e. where the radial pivot multiplies a free leaf/E coordinate.
print("\n(3,3,3,3): outputs containing a 'x0 * x_k' (k>0) monomial term (the u*E / u*leaf blow-ups):")
radial_coords = set()
for idx, e in enumerate(F):
    p = sp.Poly(e, *x)
    for mono, coeff in p.terms():
        # mono is exponent tuple; find terms with x0 exponent 1 and exactly one other var exp 1
        if mono[0]==1:
            others = [k for k in range(1,27) if mono[k]>0]
            if len(others)==1 and mono[others[0]]==1 and sum(mono)==2:
                radial_coords.add(others[0])
                #print(f"  out[{idx}] has  x0*x{others[0]}")
print("   u-blown leaf/E coords (k with x0*xk term):", sorted(radial_coords))
print("   plus the pivot itself: 0")
print("   => candidate radial active set:", sorted({0}|radial_coords), " card =", len({0}|radial_coords))
print("   minAdm = 6")

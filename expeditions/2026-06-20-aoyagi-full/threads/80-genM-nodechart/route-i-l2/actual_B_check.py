import sympy as sp
# CRITICAL re-check: is B = phiGen 1 (genBlkFlatLiveR1 ... y) the RIGHT B?
# genBlkFlatLiveR1's pivot Rmat = rmatPad(pivotEIndicator) = CONSTANT (literal 1 at E(0,0), x-INDEPENDENT).
# So phiGen 1 (genBlkFlatLiveR1 ... (pbo x)) reads the pivot E-block as 1·pivotEIndicator = the CONSTANT,
# NOT additively from the pivot coord. Does φ = (phiGen 1 (genBlkFlatLiveR1)) ∘ pbo hold with THIS B?
x = sp.symbols('x0:8', real=True); u = x[0]
# φ (achiever, radial u=x0, fixed pivot): A0[1,1] = x5*x1 + u·1 = x5*x1 + x0
A0_phi = sp.Matrix([[x[4], x[4]*x[1]], [x[5], x[5]*x[1] + x[0]]])
A1_phi = sp.Matrix([[x[0]-x[1]*x[2], x[0]*x[6]-x[1]*x[3]], [x[2], x[3]]])
F = [A0_phi[0,0],A0_phi[0,1],A0_phi[1,0],A0_phi[1,1],A1_phi[0,0],A1_phi[0,1],A1_phi[1,0],A1_phi[1,1]]
# B = phiGen 1 (genBlkFlatLiveR1 ... y): radial=1, pivot E-block = CONSTANT pivotEIndicator (=1), reads y elsewhere.
# A0[1,1] = (read y: x5,x1 unchanged) + 1·1 = x5*x1 + 1  (NOT +y0 — the fixed block is x-independent!)
yb = sp.symbols('b0:8', real=True)
A0_B = sp.Matrix([[yb[4], yb[4]*yb[1]], [yb[5], yb[5]*yb[1] + 1]])        # CONSTANT anchor = 1
A1_B = sp.Matrix([[yb[0]-yb[1]*yb[2], yb[6]-yb[1]*yb[3]], [yb[2], yb[3]]]) # radial=1: leaf y6, NO y0 scaling
B = [A0_B[0,0],A0_B[0,1],A0_B[1,0],A0_B[1,1],A1_B[0,0],A1_B[0,1],A1_B[1,0],A1_B[1,1]]
active = {0, 6}
def pbon(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(8)]
rad = pbon(active,0,x)
Brad = [b.subs({yb[i]: rad[i] for i in range(8)}) for b in B]
print("ACTUAL B=phiGen 1(genBlkFlatLiveR1): φ == B(pbo)?", all(sp.simplify(F[i]-Brad[i])==0 for i in range(8)))
for i in range(8):
    d = sp.simplify(F[i]-Brad[i])
    if d != 0: print(f"  coord {i}: φ={F[i]}  B(pbo)={Brad[i]}  diff={d}")

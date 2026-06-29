import sympy as sp
# Does phi = B ∘ pivotBlowupOn hold for the FIXED-pivot decoder (genBlkFlatLiveR1)?
# Key difference from my earlier check: the pivot boundary's E-block is FIXED to pivotEIndicator (literal 1),
# NOT a free coord. So in φ, that block contributes u·1 = u (u=x_p); in B (radial=1) it's 1·1 = 1.
# Model the (2,2,2)-shape with the pivot E-block FIXED:
# A0[1,1] had x6*x0 (x6 = the E-coord, free in genBlkFlatLive). In genBlkFlatLiveR1 the pivot E-slot is FIXED=1,
# its coord rerouted to leaf. So that entry becomes x0*1 = x0 (NOT x0*x6); x6 reroutes to a leaf coord.
x = sp.symbols('x0:8', real=True); u = x[0]
# genBlkFlatLiveR1 (2,2,2): pivot boundary E fixed to 1 (the x0*1 term), x6's budget → leaf.
# A0[1,1] = x5*x1 + x0*1  (fixed pivot: u·pivotEIndicator(0,0)=u·1=x0), leaf carries the freed DOF (say into A1)
A0 = sp.Matrix([[x[4], x[4]*x[1]], [x[5], x[5]*x[1] + x[0]]])          # x0*x6 -> x0*1 = x0 (FIXED pivot)
A1 = sp.Matrix([[x[0]-x[1]*x[2], x[0]*x[6]-x[1]*x[3]], [x[2], x[3]]])  # leaf now carries x6 (rerouted), via u·Rfin
F = [A0[0,0],A0[0,1],A0[1,0],A0[1,1],A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
# B = radial-1: x0*1 -> 1 (the fixed pivot loses its u!); x0*x6 (leaf) -> x6
xb = sp.symbols('b0:8', real=True)
A0b = sp.Matrix([[xb[4], xb[4]*xb[1]], [xb[5], xb[5]*xb[1] + sp.Integer(1)]])  # radial-1: fixed pivot -> 1
A1b = sp.Matrix([[xb[0]-xb[1]*xb[2], xb[6]-xb[1]*xb[3]], [xb[2], xb[3]]])      # leaf -> x6
B = [A0b[0,0],A0b[0,1],A0b[1,0],A0b[1,1],A1b[0,0],A1b[0,1],A1b[1,0],A1b[1,1]]
# active = {0} ∪ {leaf coord 6}  (the pivot E-slot is FIXED, NOT active; its coord 6 rerouted to leaf, IS active)
active = {0, 6}
def pbon(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(8)]
rad = pbon(active,0,x)
Brad = [b.subs({xb[i]: rad[i] for i in range(8)}) for b in B]
print("FIXED-pivot: phi == B(pbo)?", all(sp.simplify(F[i]-Brad[i])==0 for i in range(8)))
for i in range(8):
    d = sp.simplify(F[i]-Brad[i])
    if d != 0: print(f"  mismatch coord {i}: phi={F[i]}  B(pbo)={Brad[i]}")

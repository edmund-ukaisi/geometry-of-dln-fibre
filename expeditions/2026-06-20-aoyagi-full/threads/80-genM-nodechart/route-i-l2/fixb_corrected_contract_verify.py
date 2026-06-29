import sympy as sp
# Fix B corrected contract: phiFlatLiveR1 = B ∘ pivotBlowupOn(active, p), B = de-radialized chart (radial 1),
# active EXCLUDES the E(0,0) anchor (literal 1, absorbed into B additively).
# (2,2,2) fixed-pivot model: the pivot bd E-block is the FIXED pivotEIndicator (literal 1 at (0,0)).
# φ has the term u·1 (= x0) at the E(0,0) output; B (radial 1) reads E(0,0) ADDITIVELY from the pivot coord.
x = sp.symbols('x0:8', real=True); u = x[0]
# φ (fixed pivot, (2,2,2)): A0[1,1] = x5*x1 + u·1 (the FIXED pivot E(0,0)=1 scaled by u=x0); leaf carries the freed DOF.
# Other E-free slots: at (2,2,2) r1=c1=1 so the E-block is 1x1 = JUST the (0,0) anchor (no E-free slots!).
# So active = {x0 (pivot)} ∪ {} (no E-free) ∪ {leaf slots}. Leaf = the rerouted freed coord, say x6, x7.
A0 = sp.Matrix([[x[4], x[4]*x[1]], [x[5], x[5]*x[1] + x[0]]])           # x0 = u·1 (FIXED pivot E00, additive)
A1 = sp.Matrix([[x[0]-x[1]*x[2], x[0]*x[6]-x[1]*x[3]], [x[2], x[3]]])   # leaf x6 (free, IN active), x7? 
F = [A0[0,0],A0[0,1],A0[1,0],A0[1,1],A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
# B = de-radialized (radial set to 1): the FIXED pivot E00 reads ADDITIVELY → B_{E00} = ... + (the pivot coord b0).
# Key Fix-B claim: B(pbo x)_{E00} = x5*x1 + b0  where b0 = pbo's pivot coord = x0. So B reads E00 as "+ b0" (additive).
xb = sp.symbols('b0:8', real=True)
A0b = sp.Matrix([[xb[4], xb[4]*xb[1]], [xb[5], xb[5]*xb[1] + xb[0]]])    # B reads E00 ADDITIVELY from pivot coord b0
A1b = sp.Matrix([[xb[0]-xb[1]*xb[2], xb[6]-xb[1]*xb[3]], [xb[2], xb[3]]])# leaf reads b6 (the active leaf coord)
B = [A0b[0,0],A0b[0,1],A0b[1,0],A0b[1,1],A1b[0,0],A1b[0,1],A1b[1,0],A1b[1,1]]
# active = {0 (pivot)} ∪ {6 (leaf free)}  (NO E-free at (2,2,2); E00 anchor NOT in active)
active = {0, 6}
def pbon(active,p,vec): return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(8)]
rad = pbon(active,0,x)
Brad = [b.subs({xb[i]: rad[i] for i in range(8)}) for b in B]
print("Fix B (2,2,2): φ == B(pbo)?", all(sp.simplify(F[i]-Brad[i])==0 for i in range(8)))
for i in range(8):
    d = sp.simplify(F[i]-Brad[i])
    if d != 0: print(f"  coord {i}: φ={F[i]}  B(pbo)={Brad[i]}")

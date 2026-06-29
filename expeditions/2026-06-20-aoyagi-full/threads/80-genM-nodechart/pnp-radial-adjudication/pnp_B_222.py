import sympy as sp
# (2,2,2): test whether phi = B ∘ pivotBlowupOn(active={0,6,7}, p=0) holds as MAPS, with B division-free.
# pivotBlowupOn: x0->x0; x6->x0*x6; x7->x0*x7; others fixed.  (active = {0,6,7})
# So in blown coords y: y0=x0, y6=x0*x6, y7=x0*x7, y_i=x_i else.
# B(y) must satisfy B(pivotBlowupOn(x)) = phi(x). I.e. B is phi with x6->y6, x7->y7 (the actives read directly),
# x0->y0 (pivot), x_i->y_i. If phi only ever uses x6,x7 in the combos x0*x6, x0*x7 (which pivotBlowupOn maps to y6,y7),
# then B reads y6,y7 directly => division-free. TEST:
x=sp.symbols('x0:8',real=True)
A0=sp.Matrix([[x[4],x[4]*x[1]],[x[5],x[5]*x[1]+x[6]*x[0]]])
A1=sp.Matrix([[x[0]-x[1]*x[2],x[0]*x[7]-x[1]*x[3]],[x[2],x[3]]])
phi=[A0[0,0],A0[0,1],A0[1,0],A0[1,1],A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
# Does x6 appear ONLY as x0*x6, and x7 ONLY as x0*x7?  (active 6,7). x0 (pivot) may appear bare.
for k in (6,7):
    appears=[sp.expand(e) for e in phi if x[k] in e.free_symbols]
    print(f"x{k} appears in:", appears)

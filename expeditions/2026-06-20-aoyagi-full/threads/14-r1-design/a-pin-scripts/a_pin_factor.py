import sympy as sp
w = sp.symbols('w0:12', real=True)
# res1 leading form:
res1=-w[1]*w[10]+w[1]*w[11]+w[1]*w[8]-w[1]*w[9]-w[10]*w[5]+w[11]*w[5]+w[5]*w[8]-w[5]*w[9]
print("res1 leading form factored:", sp.factor(res1))
# Is it a product of two linear forms (bilinear)?
print("=> bilinear:", "(w1+w5)*(w8-w9-w10+w11) form")
print()
print("=== INTERPRETATION of the residual core at intermediate v (L=3 (2,2,2,2), v in S(1,0,0)) ===")
print("The residual core's leading part = res1^2 (+ higher), res1 = (w1+w5)(w8-w9-w10+w11) BILINEAR.")
print("This IS a smaller matrix-chain-product zero locus: res1 = (a linear combo from C1,C2 block) x")
print("(a linear combo from C2,C3 block) -- the Schur-reduced 1x1 . 1x1 chain. So the residual core IS")
print("of chain-product form (||prod(C')||^2 for the reduced chain), CONSISTENT with #109's strict-transform.")
print()
print("=> The residual core at intermediate v IS a smaller ||prod(C')||^2 (chain-product form).")
print("   So #111's schur_chart_exists COULD apply to it (it's the same object shape, at the core origin).")
print("   BUT D1>= is value-free -- it only needs the core HOMOGENEOUS (the bilinear leading form IS),")
print("   not resolved. So D1>= needs the SPLIT (constant-rank) + the core being chain-shaped+homogeneous,")
print("   NOT #111's resolution of it.")

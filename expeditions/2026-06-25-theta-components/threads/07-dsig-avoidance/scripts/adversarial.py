import sympy as sp

# (3,3,3) r=2: P = A2*A1, 3x3. Top component Sigma^2 = {det P = 0}? 
# Actually rank<=2 of 3x3 = det P=0. The realizer can have product = diag(0,1,1) (rank 2, top-left 2x2 minor = det[[0,0],[0,1]] = 0).
# Build A1, A2 with A2*A1 = diag(0,1,1): take A1 = diag(0,1,1), A2 = I. Then P = diag(0,1,1).
# detDelta = top-left 2x2 minor of P = det([[0,0],[0,1]]) = 0. And det P = 0 (rank 2 <=2). 
# So this point is IN Sigma^2 with detDelta=0 at the point. Question: is it on the (unique? top) component, and does detDelta vanish on the WHOLE component?

a = sp.symbols('a11 a12 a13 a21 a22 a23 a31 a32 a33')
b = sp.symbols('b11 b12 b13 b21 b22 b23 b31 b32 b33')
A1 = sp.Matrix(3,3, a)
A2 = sp.Matrix(3,3, b)
P = A2*A1
detDelta = (P[:2,:2]).det()   # top-left 2x2 minor
# The adversarial realizer point: A1=diag(0,1,1), A2=I  => P=diag(0,1,1)
subs_pt = {a[0]:0,a[1]:0,a[2]:0,a[3]:0,a[4]:1,a[5]:0,a[6]:0,a[7]:0,a[8]:1,
           b[0]:1,b[1]:0,b[2]:0,b[3]:0,b[4]:1,b[5]:0,b[6]:0,b[7]:0,b[8]:1}
Ppt = P.subs(subs_pt)
print("P at adversarial point =", Ppt.tolist())
print("rank P at point =", Ppt.rank())
print("detDelta (top-left 2x2) at point =", detDelta.subs(subs_pt))
print("det P at point =", P.det().subs(subs_pt))

import sympy as sp

# 8 flat coords
x = sp.symbols('x0:8', real=True)

# chartParams222: two 2x2 layers, flattened.
# chartA0 = [[x4, x4*x1],[x5, x5*x1 + x6*x0]]
# chartA1 = [[x0 - x1*x2, x0*x7 - x1*x3],[x2, x3]]
A0 = sp.Matrix([[x[4], x[4]*x[1]],
                [x[5], x[5]*x[1] + x[6]*x[0]]])
A1 = sp.Matrix([[x[0]-x[1]*x[2], x[0]*x[7]-x[1]*x[3]],
                [x[2], x[3]]])

# flatten to 8 outputs (order is immaterial for |det| up to sign; paramsEquivFlat is a fixed bijection, det +-1)
F = [A0[0,0], A0[0,1], A0[1,0], A0[1,1],
     A1[0,0], A1[0,1], A1[1,0], A1[1,1]]
F = sp.Matrix(F)

J = F.jacobian(sp.Matrix(x))
d = sp.simplify(J.det())
print("raw flat det of chartParams222 =", sp.factor(d))
print("|det| should match |x0|^2 * |x4| up to sign")
print("factored:", sp.factor(d))

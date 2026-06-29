import sympy as sp

x = sp.symbols('x0:8', real=True)
xv = sp.Matrix(x)

def pivotBlowupOn(active, p, vec):
    # active: set of indices, p pivot. i==p -> vec[p]; i in active -> vec[p]*vec[i]; else vec[i]
    out = []
    for i in range(8):
        if i == p:
            out.append(vec[p])
        elif i in active:
            out.append(vec[p]*vec[i])
        else:
            out.append(vec[i])
    return sp.Matrix(out)

def shear222(p):
    out = []
    for i in range(8):
        if i == 0:
            out.append(p[0] - p[1]*p[2])
        elif i == 6:
            out.append(p[6] + p[5]*p[1])
        elif i == 7:
            out.append(p[7] - p[1]*p[3])
        else:
            out.append(p[i])
    return sp.Matrix(out)

# T222 = bsubst222 ∘ shear222 ∘ pb222
pb = pivotBlowupOn({0,6,7}, 0, xv)            # radial
sh = shear222(pb)                              # det-1 shear
bs = pivotBlowupOn({1,4}, 4, sh)               # cross-strip spectator
T = bs

print("T222 =", [sp.expand(c) for c in T])

# pack222: A0 = [[w4,w1],[w5,w6]], A1=[[w0,w7],[w2,w3]]
w = T
A0 = sp.Matrix([[w[4], w[1]],[w[5], w[6]]])
A1 = sp.Matrix([[w[0], w[7]],[w[2], w[3]]])

# original chartParams222
A0o = sp.Matrix([[x[4], x[4]*x[1]],[x[5], x[5]*x[1] + x[6]*x[0]]])
A1o = sp.Matrix([[x[0]-x[1]*x[2], x[0]*x[7]-x[1]*x[3]],[x[2], x[3]]])

print("pack(T)==chartParams222 ?  A0:", sp.simplify(A0-A0o)==sp.zeros(2,2),
      " A1:", sp.simplify(A1-A1o)==sp.zeros(2,2))

# per-factor dets
Jpb = pivotBlowupOn({0,6,7},0,xv).jacobian(xv)
print("det D(pb222) =", sp.factor(Jpb.det()), " (expect x0^2)")
Jsh = shear222(xv).jacobian(xv)
print("det D(shear222) =", sp.factor(Jsh.det()), " (expect 1)")
# bsubst at the shear∘pb point
Jbs = pivotBlowupOn({1,4},4,xv).jacobian(xv)
print("det D(bsubst222) =", sp.factor(Jbs.det()), " (= x4, eval at coord4 = (shear pb)4 = x4)")

import sympy as sp

# Exact-algebra verification of E2 at L=2: does the framed read-block energy stay invariant
# under the joint (T1,Y1) Psi, INCLUDING the endpoint conjugation that may leak P11?
# Shapes: r=1, m0=H0-r, m1=Hmid-r? No: at L=2 the per-layer cores are S_s : (H_s.cs - r)x(H_s.succ - r).
# Use H = (H0, Hmid, Hlast) reduced widths m0=H0-r, mmid=Hmid-r, mlast=Hlast-r.
# Layer s0: A0 (rxr), Y0 (r x mmid), Z0 (m0 x r), T0 (m0 x mmid).
# Layer s1: A1 (rxr), Y1 (r x mlast), Z1 (mmid x r), T1 (mmid x mlast).
# Reduced product P = layer0 . layer1 (block r+(.-r)):
#   P00 = A0 A1 + Y0 Z1 (rxr), P01 = A0 Y1 + Y0 T1 (r x mlast),
#   P10 = Z0 A1 + T0 Z1 (m0 x r), P11 = Z0 Y1 + T0 T1 (m0 x mlast).

r, m0, mmid, mlast = 1, 1, 2, 1   # a genuinely rectangular shape, mmid=2 so K can be nonzero/nilpotent
def M(name, rows, cols):
    return sp.Matrix(rows, cols, lambda i,j: sp.Symbol(f"{name}_{i}_{j}"))

X0=M("X0",r,r); X1=M("X1",r,r); Y0=M("Y0",r,mmid); Z0=M("Z0",m0,r); T0=M("T0",m0,mmid)
Z1=M("Z1",mmid,r); Y1=M("Y1",r,mlast); T1=M("T1",mmid,mlast)
A0=sp.eye(r)+X0; A1=sp.eye(r)+X1
A0i=A0.inv(); A1i=A1.inv()
P00f=A0*A1+Y0*Z1; P00fi=P00f.inv()
K=Z1*P00fi*Y0
S1=T1 - Z1*A1i*Y1
S0=T0 - Z0*A0i*Y0
W=sp.eye(mmid)+Z1*A1i*A0i*Y0
Wi=W.inv()
T1p = Wi*((sp.eye(mmid)-K)*S1 + Z1*A1i*Y1 + Z1*A1i*A0i*Y0*T1)
Y1p = Y1 + A0i*Y0*(T1 - T1p)

# E1 check: T1p - Z1 A1i Y1p == (1-K) S1
E1 = sp.simplify((T1p - Z1*A1i*Y1p) - (sp.eye(mmid)-K)*S1)
print("E1 residual (should be 0):", E1.is_zero_matrix if hasattr(E1,'is_zero_matrix') else sp.simplify(E1))

# E2 check (raw P01): A0 Y1p + Y0 T1p == A0 Y1 + Y0 T1
P01  = A0*Y1 + Y0*T1
P01p = A0*Y1p + Y0*T1p
print("E2 raw-P01 residual (should be 0):", sp.simplify(P01p - P01).is_zero_matrix)

# P11 change:
P11  = Z0*Y1 + T0*T1
P11p = Z0*Y1p + T0*T1p
dP11 = sp.simplify(P11p - P11)
print("dP11 == -S0(T1-T1p)?", sp.simplify(dP11 - (-S0*(T1-T1p))).is_zero_matrix)
print("dP11 is zero?", dP11.is_zero_matrix)

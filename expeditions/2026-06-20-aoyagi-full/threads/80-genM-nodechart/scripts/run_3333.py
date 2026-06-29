"""Run the decisive decomposition on the VALIDATED (3,3,3,3) layout (27 coords, det confirmed)."""
import sympy as sp
from sympy import symbols, eye, zeros, Matrix, factor, expand, Poly
from decompose import build_direct, build_factored, shear_block
from perpiece_v2 import chainQ, chainA

NC = 27
def blocks_3333(x):
    i = [1]
    def nx():
        v = x[i[0]]; i[0] += 1; return v
    bl = {}; groups = []
    bl[0] = {'B': eye(3), 'N': zeros(3, 0), 'W': zeros(0, 3), 'R': zeros(3, 3)}
    groups.append(('b0-identity', []))
    a = nx(); b = nx(); c = nx(); d = nx(); e = nx(); f = nx()   # x1..x6
    B1 = Matrix([[a, a*b],
                 [a*c, a*b*c + d],
                 [a*c*e + a*f, a*b*f + e*(a*b*c + d)]])
    n1a = nx(); n1b = nx()                                       # x7,x8
    N1 = Matrix([[n1a], [n1b]])
    W1 = Matrix([[nx(), nx(), nx()]])                            # x9,x10,x11
    R1 = Matrix([[0, 0, 0], [0, 0, 0], [0, 0, 1]])
    bl[1] = {'B': B1, 'N': N1, 'W': W1, 'R': R1}
    groups.append(('b1', [1,2,3,4,5,6,7,8,9,10,11]))
    b2 = nx(); l2 = nx(); B2 = Matrix([[b2], [l2*b2]])           # x12,x13
    N2 = Matrix([[nx(), nx()]])                                  # x14,x15
    W2 = Matrix([[nx(), nx(), nx()], [nx(), nx(), nx()]])        # x16..x21
    R2 = Matrix([[0, 0, 0], [0, nx(), nx()]])                    # x22,x23
    bl[2] = {'B': B2, 'N': N2, 'W': W2, 'R': R2}
    groups.append(('b2', [12,13,14,15,16,17,18,19,20,21,22,23]))
    bl[3] = {'Rfin': Matrix([[nx(), nx(), nx()]])}               # x24,25,26
    groups.append(('leaf', [24,25,26]))
    return bl, i[0], groups

x = symbols('x0:%d' % NC, real=True); u = x[0]
bl, used, groups = blocks_3333(x)
L, M, T = 3, [3,3,3,3], [3,3,2,1]
Ad, Cd = build_direct(L, M, T, bl, u)
Af, Cfull, schur_out, shears = build_factored(L, M, T, bl, u)

print("===== (3,3,3,3) DECISIVE DECOMPOSITION =====")
print("coords used:", used, "need", NC)
# (i) map equality
eqA = all(expand(Ad[k] - Af[k]) == zeros(*Ad[k].shape) for k in range(L))
print("(i) factored chart == fused chart (exact MAP equality):", eqA)
# (ii) chain shears det 1 + unipotent
for k in range(L):
    Sh = shears[k]
    nil = Sh - eye(Sh.rows)
    # strictly upper => nilpotent => unipotent
    print(f"(ii) shear_{k}: shape {Sh.shape}, det={Sh.det()}, (Sh-I) strictly upper-tri={nil.is_strongly_upper_triangular if hasattr(nil,'is_strongly_upper_triangular') else 'n/a'}")
# (iii) per-boundary schur frame det.  schur_out[k] = B_k chainQ(N_k) (the C_{k+1} pre-radial).
# The det-carrying content per boundary is det(K_k)^{r_k+c_k}. Verify via the global det product.
# Build the full J and compare to u^5 * (detK1)^2 * (detK2)^3:
vec = []
for k in range(L):
    for ii in range(Ad[k].rows):
        for jj in range(Ad[k].cols):
            vec.append(Ad[k][ii,jj])
J = Matrix(NC, NC, lambda r,c: sp.diff(vec[r], x[c]))
det = expand(J.det())
print("global det =", factor(det))
detK1 = sp.expand(x[1]*x[4])      # det K_1 = a*d  (a=x1,d=x4) for the 2x2 LDU core
detK2 = sp.expand(x[12])          # det K_2 = b2 = x12
# boundary1: t1=2, r1=T0-T1... NB Text=[3,3,2,1]; boundary1 K core is 2x2, r=Text1-Text2=3-2=1,c=M1-Text2=3-2=1 -> r+c=2
# boundary2: K core 1x1, r=Text2-Text3=2-1=1, c=M2-Text3=3-1=2 -> r+c=3
# LDU factor per boundary: lduCoreDeriv_det = prod_i q_i^{2(t-1-i)}.
# boundary1 t=2: K1 LDU core [[a, a*b],[a*c, a*b*c+d]] = L diag(a, d) U  => pivots q0=a=x1, q1=d=x4.
#   LDU monomial = a^{2(2-1-0)} * d^{2(2-1-1)} = a^2 * d^0 = x1^2.
# boundary2 t=1: K2=[b2], pivot q0=b2=x12 => LDU monomial = b2^{2(1-1-0)} = b2^0 = 1.
ldu1 = sp.expand(x[1]**2)
ldu2 = 1
pred = expand(u**5 * detK1**2 * ldu1 * detK2**3 * ldu2)
print("predicted u^5 * [(detK1)^2 * lduMon1] * [(detK2)^3 * lduMon2]")
print("   = u^5 * [(x1 x4)^2 * x1^2] * [(x12)^3 * 1] =", factor(pred))
print("(iii) per-piece product reproduces global det (up to sign):",
      expand(det-pred)==0 or expand(det+pred)==0)
if not (expand(det-pred)==0 or expand(det+pred)==0):
    print("   residual det/pred =", factor(expand(det)/pred))

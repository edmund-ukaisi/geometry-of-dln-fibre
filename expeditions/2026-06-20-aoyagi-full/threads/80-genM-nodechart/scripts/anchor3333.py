"""
Anchor (3,3,3,3): reproduce the GLOBAL det and study the FUSED Jacobian structure.

M = (3,3,3,3), descent T = (3,2,1,0)  ->  but T_L=0 means dead leaf. The LIVE-leaf chart
(the one whose det is the validated u0^5·x1^4·x4^2·x12^3) uses the B_det3333 family with a
live Rfin pivot. We follow the perpiece_det_2ndM.blocks_3333 layout (proven to match the
Lean Frame3333Deriv_det = z0^5·z9^3·(z1 z4 - z2 z3)^2 after the LDU read).

Goal here: (1) confirm a SQUARE chart with the right global det; (2) expose the layer/boundary
structure of the fused J so we can test the per-piece triangular factorization.
"""
import sympy as sp
from sympy import symbols, Matrix, eye, zeros, factor, expand, Poly
from perpiece_v2 import chainQ, chainA, build, flatten

def blocks_3333(x):
    """Live-leaf (3,3,3,3) layout, mirroring perpiece_det_2ndM.blocks_3333.
       L=3, M=[3,3,3,3], T(=Text)=[3,2,1,?]. Per-boundary:
         k=0: identity boundary (B0=I3, N0/W0 empty, R0=0).      A0 = 3x3
         k=1: T1=3? NO. Text=[3,3,2,1] in that harness. Let me use the harness's Text.
    """
    # The harness uses t_ach=(3,2,1,0) and Text=[3,3,2,1] (Text0=M0=3, Text(k+1)=t_ach k).
    # boundary0: Text0=3, Text1=3 -> c0 = M0-Text1 = 0 (identity). A0 = 3x3.
    # boundary1: Text1=3, Text2=2 -> B1 3x2, c1 = M1-Text2 = 1. A1 = 3x3.
    # boundary2: Text2=2, Text3=1 -> B2 2x1, c2 = M2-Text3 = 2. A2 = 3x3.
    # leaf k=3: Text3=1, W3=3 -> Rfin 1x3.
    i = [1]
    def nx():
        v = x[i[0]]; i[0] += 1; return v
    bl = {}
    bl[0] = {'B': eye(3), 'N': zeros(3, 0), 'W': zeros(0, 3), 'R': zeros(3, 3)}
    # boundary1: B1 3x2 LDU core (the (3,3,3,3) hand det K-core), N1 2x1, W1 1x3, R1 fixed pivot e33
    a = nx(); b = nx(); c = nx(); d = nx(); e = nx(); f = nx()   # x1..x6 (6 K-core coords)
    B1 = Matrix([[a, a*b],
                 [a*c, a*b*c + d],
                 [a*c*e + a*f, a*b*f + e*(a*b*c + d)]])
    n1a = nx(); n1b = nx()                                       # x7,x8  (N1)
    N1 = Matrix([[n1a], [n1b]])
    W1 = Matrix([[nx(), nx(), nx()]])                            # x9,x10,x11 (W1)
    R1 = Matrix([[0, 0, 0], [0, 0, 0], [0, 0, 1]])
    bl[1] = {'B': B1, 'N': N1, 'W': W1, 'R': R1}
    # boundary2: B2 2x1, N2 1x2, W2 2x3, R2 free-eta row
    b2 = nx(); l2 = nx(); B2 = Matrix([[b2], [l2*b2]])           # x12,x13
    N2 = Matrix([[nx(), nx()]])                                  # x14,x15
    W2 = Matrix([[nx(), nx(), nx()], [nx(), nx(), nx()]])        # x16..x21
    R2 = Matrix([[0, 0, 0], [0, nx(), nx()]])                    # x22,x23 free eta
    bl[2] = {'B': B2, 'N': N2, 'W': W2, 'R': R2}
    # leaf
    bl[3] = {'Rfin': Matrix([[nx(), nx(), nx()]])}               # x24,x25,x26
    used = i[0]
    return bl, used

if __name__ == '__main__':
    NC = 27
    x = symbols('x0:%d' % NC, real=True); u = x[0]
    bl, used = blocks_3333(x)
    print("coords used:", used, " (need", NC, ")")
    A, C = build(3, [3, 3, 3, 3], [3, 3, 2, 1], bl, u)
    vec = flatten(A, 3)
    n = len(vec)
    print("output dim:", n, " square:", n == NC)
    J = sp.Matrix(n, NC, lambda r, c: sp.diff(vec[r], x[c]))
    det = sp.expand(J.det())
    fdet = factor(det)
    print("GLOBAL det =", fdet)
    P = Poly(det, u); lo = min(m[0] for m in P.monoms()); hi = P.degree()
    print("u-power range [%d..%d]  separates=%s" % (lo, hi, lo == hi))

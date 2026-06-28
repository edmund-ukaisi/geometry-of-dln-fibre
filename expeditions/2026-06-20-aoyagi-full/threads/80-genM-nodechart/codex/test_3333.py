"""Validate the engine against the banked (3,3,3,3) result: det = u0^5 * u1^4 * u4^2 * u9^3."""
import sys
sys.path.insert(0, '/tmp/radsep')
import sympy as sp
from sympy import symbols, Matrix, eye, zeros
from engine import build_chart, chart_vector, jac_det_analysis

# coords x0..x26
x = symbols('x0:27', real=True)
u = x[0]

# M = (3,3,3,3), t_ach = (3,2,1,0); L = 3
L = 3
M = [3,3,3,3]
t = [3,2,1,0]   # t[0]=3=M0, then 2,1,0
# Text: 0->3, 1->t0=3? wait Text(k+1)=t[k]; Text1=t[0]=3, Text2=t[1]=2, Text3=t[2]=1
# Wext: [3,3,3,3]
# Per the Lean B_det3333:
# Bmat 0 = I3 (identity boundary, c0 = Wext0 - Text1 = 3-3 = 0)
# Bmat 1 = 3x2 LDU core
# Bmat 2 = 2x1
blocks = {}
# k=0 identity boundary: Text0=3, Text1=3, c0 = 0
blocks[0] = {
    'B': eye(3),                                  # Text0 x Text1 = 3x3
    'N': zeros(3,0),                              # Text1 x (Wext0 - Text1) = 3x0
    'W': zeros(0,3),                              # (Wext0-Text1) x Wext1 = 0x3
    'R': zeros(3,3),                              # Rmat 0 = 0
}
# k=1: Text1=3, Text2=2, Wext1=3, c1 = 3-2 = 1
blocks[1] = {
    'B': Matrix([[x[1], x[1]*x[2]],
                 [x[1]*x[3], x[1]*x[2]*x[3]+x[4]],
                 [x[1]*x[3]*x[6]+x[1]*x[5], x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]]),  # 3x2
    'N': Matrix([[x[7]],[x[8]]]),                 # Text2 x c1 = 2x1
    'W': Matrix([[x[15], x[16], x[17]]]),         # c1 x Wext2 = 1x3
    'R': Matrix([[0,0,0],[0,0,0],[0,0,1]]),       # Rmat 1 = e22 (3x3) -- FIXED 1, scaled by u
}
# k=2: Text2=2, Text3=1, Wext2=3, c2 = 3-1 = 2
blocks[2] = {
    'B': Matrix([[x[9]],[x[10]*x[9]]]),           # 2x1
    'N': Matrix([[x[11], x[12]]]),                # Text3 x c2 = 1x2
    'W': Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]]),  # c2 x Wext3 = 2x3
    'R': Matrix([[0,0,0],[0,x[13],x[14]]]),       # Rmat 2 (2x3)
}
# leaf k=3: Text3=1, Wext3=3
blocks[3] = {
    'Rfin': Matrix([[x[24],x[25],x[26]]]),        # 1x3
}

A, C = build_chart(L, M, t, blocks, u)

# Verify the C/A layers match the Lean explicit forms
print("C[1] (should match chartA3333 / C1_eq3333):")
sp.pprint(sp.simplify(C[1]))
print("\nA[2] kept row check (chartC3333):")
sp.pprint(sp.simplify(A[2]))

vec = chart_vector(A, L)
# free coords: x0..x26 (27 coords). chart output = sum of A_k entries = 3*3 + 3*3 + 3*3 = 27. Good.
coords = list(x)
res = jac_det_analysis(vec, coords, u, minAdm=6, label="(3,3,3,3) achiever, t=(3,2,1,0)")
# expected: u0^5 * u1^4 * u4^2 * u9^3
expected = x[0]**5 * x[1]**4 * x[4]**2 * x[9]**3
print("\nexpected = u0^5*u1^4*u4^2*u9^3")
print("det / expected simplified:", sp.simplify(res['det']/expected))

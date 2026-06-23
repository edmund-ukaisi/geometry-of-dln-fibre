"""
(3,2,3) r=1: verify the det-core change collapses entanglement, and identify the universal cross-term
structure for the L=2 general-(H0,1,H2)? No -- middle width is r+1=2 here? H1=2, M1=1. So core middle
width is 1: the core is a (M0, 1, M2)=(2,1,2) r=0 chain = rank-1 outer product C0 C1.

After the unit-pivot solve, the 4 core entries are (verified):
  E11 = (a3 b4 D + (a1 b4 - x1)(a3 b3 - x3))/D
  E12 = (a3 b5 D + (a1 b5 - x2)(a3 b3 - x3))/D
  E21 = (a5 b4 D + (a1 b4 - x1)(a5 b3 - x4))/D
  E22 = (a5 b5 D + (a1 b5 - x2)(a5 b3 - x4))/D    with D = 1 - a1 b3 + x0.

Det-core variables (generalize Codex's U,V): we want core entry Eij = Ui * Vj + cross/D where
Ui, Vj are det-core coords s.t. on x=0, Ui Vj = a_{i} b_{j} (the (2,1,2) products) up to unit.
Try: row-vars for the W0 core (a3,a5) and col-vars for the W1 core (b4,b5).
"""
import sympy as sp
a0,a1,a2,a3,a4,a5 = sp.symbols('a0 a1 a2 a3 a4 a5', real=True)
b0,b1,b2,b3,b4,b5 = sp.symbols('b0 b1 b2 b3 b4 b5', real=True)
x0,x1,x2,x3,x4 = sp.symbols('x0 x1 x2 x3 x4', real=True)
D = 1 - a1*b3 + x0
E11 = (a3*b4*D + (a1*b4 - x1)*(a3*b3 - x3))/D
E12 = (a3*b5*D + (a1*b5 - x2)*(a3*b3 - x3))/D
E21 = (a5*b4*D + (a1*b4 - x1)*(a5*b3 - x4))/D
E22 = (a5*b5*D + (a1*b5 - x2)*(a5*b3 - x4))/D

# Generalize Codex's det-core change. For the corner pivot structure, define:
#   U_i = (a_{3 or 5}*(...) - ...)/D    [det-core row coords]
#   V_j = b_{4 or 5} - (q-type)*x/(...)  [det-core col coords]
# The pattern from (2,2,2): U=(u(1+x1)-p x3)/D, V = v - q x2/(1+x1) with p=a01->a1, q=b10->b3, u=a11->a3, v=b11->b4.
# Generalize: rows i in {3,5} (W0 core rows), cols j in {4,5} (W1 core cols).
# Hmm the 2x2 core: row index from W0 (a3 for first core row, a5 for second), col from W1 (b4 first, b5 second).
# The 'p' (a1) couples row-0 of W1 to W0 core; 'q' (b3) couples col-0 of W0 to W1 core.
# By symmetry of the (2,2,2) solution, define:
U3 = (a3*(1+x0) - a1*x3)/D   # uses a1 (the p), x3 (the W0 col-0 pivot residual for row containing a3)
U5 = (a5*(1+x0) - a1*x4)/D   # x4 is the residual for the row containing a5
V4 = b4 - b3*x1/(1+x0)       # uses b3 (the q), x1 (the W1 row-0 pivot residual for col containing b4)
V5 = b5 - b3*x2/(1+x0)       # x2 for col containing b5
h = 1/(1+x0)
# Conjecture: E_ij = U_i V_j + h * x_{row-resid} * x_{col-resid}? Let's test each.
print("Test E11 = U3 V4 + h * x1 * x3 :", sp.simplify(E11 - (U3*V4 + h*x1*x3)))
print("Test E12 = U3 V5 + h * x2 * x3 :", sp.simplify(E12 - (U3*V5 + h*x2*x3)))
print("Test E21 = U5 V4 + h * x1 * x4 :", sp.simplify(E21 - (U5*V4 + h*x1*x4)))
print("Test E22 = U5 V5 + h * x2 * x4 :", sp.simplify(E22 - (U5*V5 + h*x2*x4)))
print("""
If all 0: the (2,1,2) core entries become E_ij = U_i V_j + h * x_{1 or 2} * x_{3 or 4}.
The cross-terms are PRODUCTS OF TWO REGULAR COORDS (x1,x2 from row-0 residuals; x3,x4 from col-0 residuals).
These are EXACTLY the same 'reg*reg' universal form as (2,2,2). The core ||E||^2 = sum_ij (U_i V_j + h x_? x_?)^2.
The regular block has x1^2,x2^2,x3^2,x4^2 (plus x0^2). Completion of squares on the (x1,x2,x3,x4) block
absorbs the cross-terms (same mechanism, now a 4-var completion). VALUE unaffected (squeeze).
""")

import sympy as sp
# DeepestGaugeChart construction (sub-lemma 3+4), exact algebra. At a rank-r-EXACT deepest point w0
# (IsDeepLayers: w0 ∈ optimalSet, ∀s rank(w0 s)=r), construct the gauge chart.
#
# Setup: 2-factor block-mult lemma (folded over L). Take ONE layer C_s : H_{s} × H_{s+1}, rank exactly r.
# Near the deepest point, gauge-slice: by block_elimination there are units P_s, Q_s with
# P_s C_s Q_s = [[I_r, 0],[0,0]] AT w0. Near w0, in the gauge coords, C_s = [[I_r + X, Y],[Z, T]] where
# (X,Y,Z,T) are the local deviation blocks (X: r×r, Y: r×(H_{s+1}-r), Z: (H_s-r)×r, T: (H_s-r)×(H_{s+1}-r)).
# The DEEPEST condition (product = B, rank-exact) pins the relation. The REGULAR coords are the residual
# blocks that the gauge fixes; the REDUCED core is ‖∏ C'_s‖² on the (H_s - r) reduced widths M_s = H_s - r.
#
# Verify on a SINGLE rank-r layer first: the gauge slice + the loss decomposition.
# Concrete: (2,2,2) r=1. Layers A1, A2 each 2×2, product A1·A2 = B (here B=0 at the core, so the deepest
# point has rank-1 layers with rank-1 product... actually for the CORE r is the deepest product rank.
# Let me model ONE rank-r layer's gauge slice + the block-product loss.
r, m, n = 1, 2, 2   # rank r, layer H_s=m × H_{s+1}=n. (2,2,2) r=1: m=n=2.
# gauge coords for C : the deviation from [[I_r,0],[0,0]]:
X = sp.Matrix(r, r, sp.symbols(f'X0:{r*r}'))           # r×r
Y = sp.Matrix(r, n-r, sp.symbols(f'Y0:{r*(n-r)}'))     # r×(n-r)
Z = sp.Matrix(m-r, r, sp.symbols(f'Z0:{(m-r)*r}'))     # (m-r)×r
T = sp.Matrix(m-r, n-r, sp.symbols(f'T0:{(m-r)*(n-r)}'))# (m-r)×(n-r) = the REDUCED block
Ir = sp.eye(r)
# C in gauge coords = [[I_r + X, Y],[Z, T]]:
C = sp.Matrix(sp.BlockMatrix([[Ir + X, Y],[Z, T]]))
print("=== gauge slice C = [[I_r+X, Y],[Z, T]] (2,2,2) r=1 ===")
sp.pprint(C)
print("\nRegular (gauge) coords = X, Y, Z (the blocks the gauge fixes / regular directions).")
print("Reduced block = T (the (m-r)×(n-r) = the reduced-width M_s = H_s - r block).")
print()
# THE KEY: a 2-factor block-product. Two rank-r layers C1 = [[I+X1,Y1],[Z1,T1]], C2 = [[I+X2,Y2],[Z2,T2]].
# product C1·C2 — the (reduced) lower-right block of the product, modulo the regular blocks. Verify the
# loss ‖C1 C2 - B‖² separates as ∑(regular residuals)² + ‖(reduced product)‖² near w0.
X2 = sp.Matrix(r, r, sp.symbols(f'XX0:{r*r}')); Y2 = sp.Matrix(r, n-r, sp.symbols(f'YY0:{r*(n-r)}'))
Z2 = sp.Matrix(m-r, r, sp.symbols(f'ZZ0:{(m-r)*r}')); T2 = sp.Matrix(m-r, n-r, sp.symbols(f'TT0:{(m-r)*(n-r)}'))
C2 = sp.Matrix(sp.BlockMatrix([[Ir + X2, Y2],[Z2, T2]]))
P = sp.expand(C * C2)
print("=== product C1·C2 (2×2, the deepest product has rank r=1; B=0 at the core) ===")
sp.pprint(P)
# The loss at the core (B=0): ‖C1 C2‖². The (0,0) block = (I+X1)(I+X2)+Y1 Z2 = I + (regular: X1+X2+...);
# the REDUCED (1,1) entry = Z1 Y2 + T1 T2 (the reduced product on the (m-r) block). Decompose:
print("\nProduct blocks:")
print("  (0,0) [r×r] =", sp.expand(P[0:r,0:r]).tolist(), " — REGULAR (= I_r + regular deviations)")
print("  (0,1) [r×(n-r)] =", sp.expand(P[0:r,r:]).tolist(), " — REGULAR")
print("  (1,0) [(m-r)×r] =", sp.expand(P[r:,0:r]).tolist(), " — REGULAR")
print("  (1,1) [(m-r)×(n-r)] =", sp.expand(P[r:,r:]).tolist(), " — the REDUCED block (Z1 Y2 + T1 T2)")

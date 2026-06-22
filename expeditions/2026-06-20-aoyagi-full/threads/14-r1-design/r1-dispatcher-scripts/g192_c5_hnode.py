import sympy as sp
# EXERCISE the C5 (mixed partial-drop) node: M=(3,3,2), stratum T=(2,0) [t_0=3>t_1=2>0, partial drop at s=1].
# The chain: C1 : 3x3, C2 : 3x2 (reduced widths M=(3,3,2), B=0 core). At T=(2,0): rank(C1)=2 (partial,
# from 3 down to 2 — NOT full rank 3, NOT 0), then rank(C1 C2)=0.
# C5 claim (cert §1.3/§4): C5 = block-column split — C1's image = survivor (rank t_1=2) ⊕ complement
# (rank t_0-t_1 = 1). The complement (rank-1 drop) resolves via C1 (main Schur), the survivor (rank 2)
# passes through C2 (which kills it, since t_2=0). crux2's Q: does the COMPLEMENT's C1 residual present
# as the clean main-Schur hnode: flatCore = ∑Erow² + ‖b·Erow + S·Γ‖²,  G² = ‖S·Γ‖²?
#
# Set up the deepest point of this stratum + local coords, and check the complement-C1 presentation.
# At T=(2,0): C1 has rank 2 at the basepoint (a partial-rank matrix), C2 generic with C1 C2 = 0.
# Deepest representative: C1_0 = [[1,0,0],[0,1,0],[0,0,0]] (rank 2), C2_0 such that C1_0 C2_0 = 0 ⟹ C2_0's
# rows 0,1 = 0 (the image of C1_0 is span{e0,e1}, C2_0 must kill it on the left... wait C1 C2: (3x3)(3x2).
# C1_0 C2_0 = 0 means C2_0's first two rows (hit by C1_0's rank-2 part) must be 0. So C2_0 = [[0,0],[0,0],[*,*]].
# Take C2_0 = 0 (the deepest). Local: C1 = C1_0 + perturbation, C2 = perturbation.
print("C5 node EXERCISED: M=(3,3,2), stratum T=(2,0) [t_0=3 > t_1=2 > 0, GENUINE partial drop at s=1].")
print("  C1: 3x3 rank-2 at basepoint; C2: 3x2; C1 C2 = 0 core. Complement = rank-1 drop (3→2), survivor = rank-2.")
print()
# Block per the partial drop: C1's rank-2 survivor block + rank-1 complement (the 3rd row/col defect).
# Use the gauge slice: C1 = [[I_2 + X, y],[z, t]] where the (2,2) survivor block ~ I_2, and the rank-1
# complement is the (t : 1x1) corner with its couplings (y:2x1, z:1x2). C2 = [[U],[v]] (U:2x2, v:1x2)... 
# Actually let me just do the block-column split crux2 names and check the complement C1 presents clean.
a = sp.symbols('a0:9', real=True)  # C1 perturbation (3x3)
b = sp.symbols('b0:6', real=True)  # C2 perturbation (3x2)
C1 = sp.Matrix([[1+a[0],a[1],a[2]],[a[3],1+a[4],a[5]],[a[6],a[7],a[8]]])  # rank-2 base diag(1,1,0)
C2 = sp.Matrix([[b[0],b[1]],[b[2],b[3]],[b[4],b[5]]])  # C2 base 0
P = sp.expand(C1*C2)  # 3x2, the core ‖P‖²
F = sp.expand(sum(P[i,j]**2 for i in range(3) for j in range(2)))
# The COMPLEMENT is the rank-1 defect: C1's 3rd row/col (a6,a7,a8 ~ the t-block) coupling. The SURVIVOR
# is the (2,2) block ~ I_2. C2's rows 0,1 (b0..b3) are hit by the survivor; row 2 (b4,b5) by the complement.
# Block-column split of P: P = C1 C2. Column j of P = C1 · (col j of C2). 
# The C5 reduction: survivor (rows 0,1 of C1, ~I_2) passes C2's rows 0,1 through (full rank → C2 step);
# the complement (row 2 of C1, the rank-defect) couples to give the Schur residual.
# crux2's main-Schur hnode shape: flatCore = ∑Erow² + ‖b·Erow + S·Γ‖². Let me identify the pieces.
# The regular block E = the survivor's contribution (rows 0,1 full-rank → smooth gens). The reduced core
# = the complement's Schur residual. Check P's rows:
print("P (the core = C1 C2), 3 rows × 2 cols:")
for i in range(3):
    print(f"  P_{i} = [{sp.expand(P[i,0])}, {sp.expand(P[i,1])}]")
print()
# Rows 0,1 (survivor, C1 ~ I_2 there): P_0 ≈ b0+.., P_1 ≈ b2+.. — LINEAR in b (smooth, the E regular gens).
# Row 2 (complement, C1 row = (a6,a7,a8)): P_2 = a6 b0 + a7 b2 + a8 b4 (+ a8 b5 col2) — the COUPLED part.
for i in range(3):
    row_lin_b = [sp.expand(sum(sp.diff(P[i,j],bb).subs({x:0 for x in list(a)+list(b)})*bb for bb in b)) for j in range(2)]
    print(f"  row {i} leading (linear in b): col0={row_lin_b[0]}, col1={row_lin_b[1]}")

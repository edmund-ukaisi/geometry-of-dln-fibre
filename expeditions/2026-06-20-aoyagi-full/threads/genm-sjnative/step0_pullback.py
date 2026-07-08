import sympy as sp
print("="*80)
print("STEP-0 (B)+(D): (3,3,3,4) t=(1,0,0) native R-BLOWUP sequential pullback")
print("  Front A0:3x3 (rank-1 pivot, corank 2x2), deeper Z = A1*A2 (3x4 product).")
print("  Loss F = ||A0 . Z||^2.  Boundaries: (1) layer-1 corank-2 block; (2) deeper Z rank-drop.")
print("="*80)

# ---- deeper product Z = A1 * A2 (the SHARED deeper factor; a GENUINE product) ----
A1 = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'p{i}{j}', real=True))   # 3x3
A2 = sp.Matrix(3,4, lambda i,j: sp.Symbol(f'q{i}{j}', real=True))   # 3x4
Z  = A1*A2                                                          # 3x4
print(f"\nZ = A1(3x3).A2(3x4) is {Z.shape}, a genuine product (deeper factor).")

# ---- BOUNDARY 1: A0 in rank-1 pivot incidence chart (pivot (0,0)=1) ----
# A0 = [[1, a^T],[b, M]], corank block M (2x2). Schur: A0 = L . diag(1, Delta0) . R,
#   L=[[1,0],[b,I]] (row unipotent), R=[[1,a^T],[0,I]] (col unipotent), Delta0 = M - b a^T.
a1,a2,b1,b2 = sp.symbols('a1 a2 b1 b2', real=True)
m11,m12,m21,m22 = sp.symbols('m11 m12 m21 m22', real=True)
aT = sp.Matrix([[a1,a2]]); bcol = sp.Matrix([[b1],[b2]])
Mblk = sp.Matrix([[m11,m12],[m21,m22]])
A0 = sp.Matrix(3,3, lambda i,j: (1 if (i,j)==(0,0) else (aT[0,j-1] if i==0 else (bcol[i-1,0] if j==0 else Mblk[i-1,j-1]))))
L = sp.eye(3); L[1,0]=b1; L[2,0]=b2
R = sp.eye(3); R[0,1]=a1; R[0,2]=a2
Delta0 = Mblk - bcol*aT
mid = sp.zeros(3,3); mid[0,0]=1; mid[1:,1:]=Delta0
resid = sp.simplify(A0 - L*mid*R)
print("\n[B1] A0 = L . diag(1,Delta0) . R exact:", resid == sp.zeros(3,3),
      " ; det L =", sp.simplify(L.det()), ", det R =", sp.simplify(R.det()),
      " (unit-triangular, det 1).")
print("     L,R depend ONLY on A0 entries (a,b) -> Z-INDEPENDENT.")

# ---- radial blow-up of the corank-2 block Delta0 = u1 * Delta0' (ONE radial, charge=4) ----
u1 = sp.Symbol('u1', positive=True)
d11,d12,d21,d22 = sp.symbols('d11 d12 d21 d22', real=True)
Delta0p = sp.Matrix([[d11,d12],[d21,d22]])   # reduced 2x2 block
# corank-2 -> corank-1 reduction: unit transforms (functions of Delta0' ONLY) put Delta0' -> diag(1, delta')
# pivot the (0,0) entry of Delta0' (=d11, a unit on the chart); row/col clears:
L2 = sp.Matrix([[1,0],[-d21/d11,1]])          # row clear (function of Delta0' only)
R2 = sp.Matrix([[1,-d12/d11],[0,1]])          # col clear (function of Delta0' only)
reduced = sp.simplify(L2*Delta0p*R2)
print("\n[B1-reduce] corank-2 -> corank-1: L2.Delta0'.R2 =")
sp.pprint(sp.simplify(reduced/d11) if False else reduced)
deltp = sp.simplify(reduced[1,1])
print("     -> diag(d11, delta') with delta' =", deltp, " ; det L2 =", sp.simplify(L2.det()),
      ", det R2 =", sp.simplify(R2.det()), "(unit, det 1); functions of Delta0' ONLY (Z-independent).")

# ---- the coupled loss after boundary 1 (probe step-3 form) ----
# F = ||A0 Z||^2. In the chart, row1 (pivot) is a Morse direction; rows 2,3 = Delta0 . (Z rows 2,3-ish)
# After radial: Delta0 = u1 * Delta0'. So rows 2,3 contribution = u1^2 * ||Delta0' . (deeper)||^2.
# corank-2 reduce: = u1^2 * ( ||pivot-row . deeper||^2  +  delta'^2 * ||(deeper coupling)||^2 ).
# KEY (relative invariant): u1 appears ONLY as an overall scalar prefactor u1^2 on the deeper term;
# the deeper term (the layer-2 object) is u1-FREE and (a,b)-FREE. Verify:
print("\n[D] Relative-invariant / prefactor-independence check:")
# Model the deeper coupled term T_deep = delta' * (row of Delta0'-reduced) . Z  -- check u1-free & a,b,m-free
# Build the actual rows-2,3 block of A0.Z and factor u1:
A0Z = A0*Z
# substitute the corank block M by u1*Delta0' + b a^T (so Delta0 = M - b a^T = u1*Delta0'):
subs_radial = {m11: u1*d11 + b1*a1, m12: u1*d12 + b1*a2, m21: u1*d21 + b2*a1, m22: u1*d22 + b2*a2}
A0Z_r = A0Z.subs(subs_radial)
rows23 = A0Z_r[1:,:] - sp.Matrix(2,4, lambda i,j: (b1 if i==0 else b2)*A0Z_r[0,j])  # subtract b*(pivot row)
rows23 = sp.simplify(rows23)
# rows23 should be u1 * (Delta0' . [Z rows 2,3 minus a-combination]) -- factor u1:
fac = sp.simplify(rows23 / u1)
u1_free = all(u1 not in sp.simplify(fac[i,j]).free_symbols for i in range(2) for j in range(4))
print("     rows(2,3) of A0.Z, minus b*(pivot row), factor EXACTLY as u1 * (residual):", 
      sp.simplify(rows23 - u1*fac) == sp.zeros(2,4))
print("     the residual (rows23/u1) is u1-FREE:", u1_free, 
      " -> u1 is a PASSIVE overall prefactor on the deeper term (relative invariant holds).")
# and the residual depends on Delta0'(d), a, and Z -- NOT on b (the row-clear absorbed b):
b_free = all({b1,b2}.isdisjoint(sp.simplify(fac[i,j]).free_symbols) for i in range(2) for j in range(4))
print("     the residual is b-FREE (row-clear absorbed b):", b_free)

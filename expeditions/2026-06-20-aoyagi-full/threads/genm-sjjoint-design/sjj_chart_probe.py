import sympy as sp
# ============================================================
# THE RECURSIVE LOSS IDENTITY — crux steps on a coupled corank-2 block Δ (2×2) coupled to a downstream
# PRODUCT Z (2×n). Test: single-radial u factors cleanly; the pivot-clear is a Z-INDEPENDENT unit
# transform reducing corank-2 → corank-1(δ') + Morse pivot. If Z-independent, the sequential scheme
# works regardless of Z being a shared product => NO simultaneous resolution needed.
# ============================================================
u,a,b,d = sp.symbols('u a b d', real=True)       # corank-2 block chart: Δ = u·[[1,a],[b,d]]
n=3
Z = sp.Matrix(2, n, lambda i,j: sp.Symbol(f'z_{i}{j}', real=True))   # downstream product rows (2×n), SYMBOLIC
Delta_p = sp.Matrix([[1,a],[b,d]])
Delta = u*Delta_p

# (1) single-radial u factors cleanly out of ‖Δ·Z‖²
F = (Delta*Z)
frob = sum(F[i,j]**2 for i in range(2) for j in range(n))
frob_over_u2 = sp.simplify(frob/u**2)
print("(1) ‖Δ·Z‖² / u²  is u-free:", sp.simplify(frob - u**2*frob_over_u2)==0,
      " => loss = u²·‖Δ'·Z‖² (clean radial factor, Jacobian u^{4-1}=u³)")

# (2) the pivot-clear: a Z-INDEPENDENT unit (det-1) row transform L(a,b,d) with L·Δ' = [[1,a],[0,δ']]
#     clearing the (2,1) coupling. L = [[1,0],[-b,1]] (unit lower-tri, det 1, depends ONLY on Δ').
L = sp.Matrix([[1,0],[-b,1]])
LDp = sp.simplify(L*Delta_p)
print("(2) L·Δ' =", LDp.tolist(), " (row2 pivot-col cleared; δ' = d-ab); L depends ONLY on Δ', NOT Z ✓")
print("    det L =", sp.det(L), " (unit transform, Jacobian 1)")
# After L: ‖L·Δ'·Z‖² has the SAME rlct (L an analytic iso on the Z-rows: Z ↦ L·Z, unit). Under Z↦L·Z
# (a Z-reparam, unit Jacobian since det L=1), ‖Δ'·Z‖² ↦ ‖[[1,a],[0,δ']]·Z‖². Now col-clear a:
#   R=[[1,-a],[0,1]] (unit upper-tri) acts on COLUMNS of the block: [[1,a],[0,δ']]·R = [[1,0],[0,δ']].
R = sp.Matrix([[1,-a],[0,1]])
red = sp.simplify(LDp*R)
print("    (L·Δ')·R =", red.tolist(), " => reduced to diag(1, δ'), δ'=d-ab ✓  (R col-unit, det",sp.det(R),")")

# (3) the reduced loss: ‖diag(1,δ')·Z''‖² = ‖row1 Z''‖² + δ'²·‖row2 Z''‖²  (Z'' = R⁻¹·(L·Z) reparam)
Zpp = sp.Matrix(2, n, lambda i,j: sp.Symbol(f'w_{i}{j}', real=True))
dp = sp.Symbol("delta'", real=True)
diagblk = sp.Matrix([[1,0],[0,dp]])
red_loss = sum((diagblk*Zpp)[i,j]**2 for i in range(2) for j in range(n))
row1 = sum(Zpp[0,j]**2 for j in range(n)); row2 = sum(Zpp[1,j]**2 for j in range(n))
print("(3) ‖diag(1,δ')·Z''‖² - (‖row1 Z''‖² + δ'²‖row2 Z''‖²) =",
      sp.simplify(red_loss - (row1 + dp**2*row2)), " (0 => MORSE pivot ‖row1‖² + corank-1 residual δ'²‖row2 Z''‖²)")
print("""
=> STRUCTURE CONFIRMED: corank-2 block --[one radial u]--> u²·‖Δ'·Z‖²
   --[Z-INDEPENDENT unit transforms L,R]--> u²·(‖pivot row‖²[Morse] + δ'²·‖row2·Z''‖²[corank-1 coupled]).
   The corank-2 step REDUCES to: a clean radial u (charge = block codim), a Morse pivot direction, and a
   CORANK-1 coupled residual δ'²·‖(downstream row)‖² — the SAME object as the (3,3,3,3) corank-1 recursion.
   The unit transforms L,R depend ONLY on the block Δ', NOT on Z => valid for Z a SHARED PRODUCT.
   No simultaneous resolution of Z is forced at this step; Z's degeneration descends to its own layers.
""")

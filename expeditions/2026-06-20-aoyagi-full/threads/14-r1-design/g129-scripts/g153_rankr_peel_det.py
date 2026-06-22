import sympy as sp
# VERIFY the rank-r triangular peel is det=1 (not just rank-1). The peel: D-block coords → S-coords,
# S = D − b·a, where for a rank-r reduced node: a = Â[0:r, r:] (r×(k-r)), b = Â[r:, 0:r] ((m-r)×r),
# D = Â[r:, r:] ((m-r)×(k-r)). The change of variables: W := D − b·a (the (m-r)×(k-r) Schur block),
# keeping a, b (and the rest) fixed. Is this det=1 (a block shear)?
#
# The map on the D-block entries: W_ij = D_ij − (b·a)_ij. Since (b·a)_ij depends ONLY on a,b (NOT on D),
# the Jacobian ∂(W,a,b)/∂(D,a,b) is block-lower-triangular:
#   ∂W/∂D = I (identity on the (m-r)(k-r) D-entries, since W = D − f(a,b))
#   ∂W/∂a, ∂W/∂b = some blocks (−b·, −·a)
#   ∂a/∂D=0, ∂b/∂D=0 (a,b unchanged)
# ⟹ block-triangular with I on the diagonal ⟹ det = 1. Verify for r=2, m=3, k=3 (general rank-2):
r,m,k = 2,3,3
a = sp.Matrix(r, k-r, sp.symbols(f'a0:{r*(k-r)}'))      # r×(k-r)
b = sp.Matrix(m-r, r, sp.symbols(f'b0:{(m-r)*r}'))      # (m-r)×r
D = sp.Matrix(m-r, k-r, sp.symbols(f'D0:{(m-r)*(k-r)}'))# (m-r)×(k-r)
ba = sp.expand(b*a)                                      # (m-r)×(k-r)
W = sp.Matrix(m-r, k-r, lambda i,j: D[i,j] - ba[i,j])   # W = D − b·a
# the full coordinate vector (D-entries, a-entries, b-entries) → (W-entries, a, b):
Dvars = list(D); avars = list(a); bvars = list(b)
allvars = Dvars + avars + bvars
Wexprs = list(W) + avars + bvars   # (W, a, b) as functions of (D, a, b)
J = sp.Matrix([[sp.diff(we, v) for v in allvars] for we in Wexprs])
print(f"=== rank-r triangular peel W := D − b·a, r={r}, m={m}, k={k} ===")
print(f"  D-block: {m-r}×{k-r} = {(m-r)*(k-r)} entries; a: {r}×{k-r}; b: {m-r}×{r}")
print(f"  Jacobian ∂(W,a,b)/∂(D,a,b): {J.rows}×{J.cols}, det = {J.det()}  (=1 ⟹ det-1 MP shear)")
print()
# Confirm the structure: ∂W/∂D block = identity (W = D − f(a,b), f indep of D):
nD = len(Dvars)
JWD = J[:nD, :nD]  # ∂W/∂D
print("  ∂W/∂D block = identity?", JWD == sp.eye(nD))
print("  ∂a/∂D, ∂b/∂D blocks = 0?", J[nD:, :nD] == sp.zeros(len(avars)+len(bvars), nD))
print()
print("⟹ det = 1 at ANY rank r (block-lower-triangular, I on the D-block diagonal, a/b fixed).")
print("The peel W:=D−b·a is a BLOCK SHEAR (W shifts D by the bilinear b·a, fixing a,b) — unipotent,")
print("det 1 identically. So nodeC1's triangular peel rides measurePreserving_lemma2 (det=1 MP) at any")
print("rank — NO bounded-unit lemma, NO rank-dependent unit. Confirms the rank-1 g152 + extends to rank-r.")
# also r=3 sanity:
for (rr,mm,kk) in [(1,2,2),(3,4,4),(2,4,3)]:
    a=sp.Matrix(rr,kk-rr,sp.symbols(f'aa0:{rr*(kk-rr)}')); b=sp.Matrix(mm-rr,rr,sp.symbols(f'bb0:{(mm-rr)*rr}'))
    D=sp.Matrix(mm-rr,kk-rr,sp.symbols(f'DD0:{(mm-rr)*(kk-rr)}')); ba=sp.expand(b*a)
    W=sp.Matrix(mm-rr,kk-rr,lambda i,j: D[i,j]-ba[i,j])
    av=list(a);bv=list(b);Dv=list(D)
    J=sp.Matrix([[sp.diff(we,v) for v in Dv+av+bv] for we in list(W)+av+bv])
    print(f"  r={rr},m={mm},k={kk}: det = {J.det()}")

import sympy as sp
# FAITHFUL C5 model via the actual Schur mechanism (the g131 hard-pivot step), NOT a clean column blow-up.
#
# The rank condition at a partial-drop node: the active factor A (3x3, prefix→image) has rank exactly 2
# at the deepest point (the drop 3->2). Generically, rank-2 means: A = full rank MINUS a rank-1 defect.
# Near the deepest point, A is a PERTURBATION of a rank-2 matrix. The g131 chart picks a 2x2 pivot
# (the survivor) and writes A in Schur form:
#    A = [[p (2x2, unit), q (2x1)],[ r (1x2), s (1x1)]]
# rank(A)=2 at deepest ⟺ Schur complement s - r·p⁻¹·q = 0 (the defect = the rank-1 drop).
# The blow-up/chart resolves this: the SINGULAR direction is the Schur complement (s - r p⁻¹ q).
#
# The node loss ‖Cnext · A‖² where Cnext kills A's image downstream. At the deepest point A·prefix=...,
# the FULL product = 0. The reduced core = the survivor's continued chain.
#
# Let me set the deepest point: A0 = rank 2 (Schur complement 0), and perturb. Variables = the chart
# coords near A0. The Schur complement δ := s - r p⁻¹ q is the SINGULAR coordinate (the defect, →0).

p = sp.Matrix(2,2, sp.symbols('p0:4', real=True))   # survivor pivot (unit, det≠0 at deepest)
q = sp.Matrix(2,1, sp.symbols('q0:2', real=True))
r = sp.Matrix(1,2, sp.symbols('r0:2', real=True))
s = sp.Symbol('s', real=True)
A = sp.Matrix(sp.BlockMatrix([[p, q],[r, sp.Matrix([[s]])]]))
# Schur complement (the defect coordinate):
pinv = p.inv()
delta = sp.simplify((s - (r*pinv*q)[0,0]))
# Cnext: downstream, kills the image. At deepest the survivor (rank 2) is killed by Cnext downstream.
# Model Cnext as (o x 3). The reduced chain on the survivor = Cnext acting on the rank-2 survivor image.
o = 2
Cnext = sp.Matrix(o,3, sp.symbols('n0:6', real=True))
P = Cnext * A
loss = sp.expand(sum(P[i,j]**2 for i in range(o) for j in range(3)))

# The hnode question: after the chart that makes delta the exceptional coordinate, does
# loss = Σreg² + Σ(b·E + SΓ)²? The Schur DECOMPOSITION of A: factor out the pivot.
# A = [[I,0],[r p⁻¹, 1]] · [[p, q],[0, delta]]   (block LU). So
# Cnext·A = Cnext · L · U where L=[[I,0],[rp⁻¹,1]] (unit lower-tri), U=[[p,q],[0,delta]].
L = sp.Matrix(sp.BlockMatrix([[sp.eye(2), sp.zeros(2,1)],[r*pinv, sp.Matrix([[1]])]]))
U = sp.Matrix(sp.BlockMatrix([[p, q],[sp.zeros(1,2), sp.Matrix([[delta]])]]))
print("A = L·U (block-LU) check:", sp.simplify(A - L*U) == sp.zeros(3,3))
# So Cnext·A = (Cnext·L)·U. Let Ctil = Cnext·L (absorb the unit lower-tri into the downstream gauge).
# Then loss = ‖Ctil·U‖². U = [[p,q],[0,delta]]: the last COLUMN of U is [q; delta]^T... no, U columns:
# U = [p_col0, p_col1, [q;delta]]. Cols 0,1 = [p;0] (survivor pivot, full rank), col 2 = [q;delta].
# ‖Ctil·U‖²: col2 of Ctil·U = Ctil·[q;delta]. The delta (defect) enters ONLY col 2, coupled with q.
print()
print("Block-LU: Cnext·A = (Cnext·L)·U, U=[[p,q],[0,δ]], δ=Schur complement (the rank-1 defect →0).")
print("  δ enters ONLY the last column of U, COUPLED with q (the off-diagonal survivor-complement block).")
print("  ⟹ This IS the coupled structure: the defect δ multiplies into a column shared with q.")
print("  The bilinear (b·E) coupling = δ's interaction with the survivor pivot via Ctil.")
print()
# Confirm the loss as a function of δ near δ=0: it's NOT a clean Frobenius-orthogonal monomial.
# The survivor pivot cols (full rank) contribute the dominant smooth block; δ is the singular dir.
# Substitute generic numeric p,q,r,Cnext, vary delta via s, check the singular structure:
import random
random.seed(1)
subs0 = {sym: random.uniform(0.5,1.5) for sym in (list(p)+list(q)+list(r)+list(Cnext))}
# at deepest: choose s so delta=0
s_deepest = sp.solve(delta.subs(subs0), s)[0]
subs_deep = dict(subs0); subs_deep[s]=s_deepest
loss_deep = float(loss.subs(subs_deep))
print(f"loss at deepest (δ=0): {loss_deep:.6f}  [the survivor cols are full-rank, so this is NOT 0!]")
print("  ⟹ the SURVIVOR does NOT vanish at this node's deepest point — only the DEFECT δ does.")
print("  The node's 'deepest point' for the RECURSION is where the SURVIVOR's downstream chain =0 too.")

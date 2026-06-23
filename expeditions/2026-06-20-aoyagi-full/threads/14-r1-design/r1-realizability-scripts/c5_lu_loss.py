import sympy as sp
# Work the block-LU loss through. Cnext·A = Ctil·U, Ctil = Cnext·L (L unit lower-tri, det 1 ⟹ gauge).
# U = [[p, q],[0, δ]]. So Ctil·U columns:
#   cols 0,1 (survivor): Ctil · [p_col; 0] = (Ctil restricted to first 2 rows-of-input) · p_cols
#   col 2 (complement+coupling): Ctil · [q; δ]
# Write Ctil = [G | e] where G = Ctil[:, 0:2] (o x 2), e = Ctil[:, 2] (o x 1).
# Then: survivor block = G·p (o x 2). complement col = G·q + δ·e (o x 1).
# loss = ‖G·p‖²(survivor) + ‖G·q + δ·e‖²(coupled complement).
#
# At the node's deepest point: δ=0 (defect resolved) AND we are at the deepest of the WHOLE thing.
# But the survivor G·p must ALSO → its own deepest (downstream). In the RECURSION, the reduced chain
# is the survivor's continued product = ‖G · (survivor factor)‖² — δ is peeled HERE, survivor recurses.
#
# hnode form check: we need flatCore = Σreg² + Σ(b·E + SΓ)², G²=‖SΓ‖² the reduced chain, ‖b‖²→0.
# Map: the survivor block ‖G·p‖² is the SΓ part? And the coupled complement ‖G·q + δ·e‖² is the
# reg + (b·E) part? Let's see the structure.
o = 3
G = sp.Matrix(o,2, sp.symbols('g0:6', real=True))
e = sp.Matrix(o,1, sp.symbols('e0:3', real=True))
p = sp.Matrix(2,2, sp.symbols('p0:4', real=True))
q = sp.Matrix(2,1, sp.symbols('q0:2', real=True))
delta = sp.Symbol('delta', real=True)
surv = G*p                    # o x 2  survivor block
comp = G*q + delta*e          # o x 1  complement col
loss = sum(surv[i,j]**2 for i in range(o) for j in range(2)) + sum(comp[i,0]**2 for i in range(o))
loss = sp.expand(loss)

# Now: the hnode wants the SINGULAR coordinate (δ→0) as the pivot b, and the reduced chain SΓ.
# Here δ is the ONLY coordinate that →0 at this node's resolved defect. But ‖G·q + δ·e‖² at δ=0 is
# ‖G·q‖² ≠ 0 generically. So the complement col does NOT vanish at δ=0 either!
# This means: the singular locus of THIS node is NOT just {δ=0}. The full deepest point needs the
# WHOLE product = 0, i.e. G·p = 0 AND G·q = 0 (and δ=0), i.e. G·[p|q]=0 i.e. G·(survivor factor)=0.
# So the reduced core = ‖G·(full survivor+coupling)‖² = the survivor chain (rank 2), and δ is a
# SEPARATE smooth direction (the defect) — NOT the binding singular direction at this node.
print("loss = ‖G·p‖² + ‖G·q + δ·e‖²  (survivor block + coupled complement)")
print()
print("At δ=0: loss = ‖G·p‖² + ‖G·q‖² = ‖G·[p|q]‖² = ‖G·(survivor full factor)‖² ≠ 0.")
print("  ⟹ {δ=0} is NOT this node's singular locus. The reduced core is ‖G·survivor‖² (rank-2 chain).")
print()
# So what does δ contribute? δ appears in loss as: 2δ·(G·q)·e + δ²‖e‖². The cross term 2δ(Gq·e) is
# the BILINEAR coupling — δ plays the role of the pivot 'b' coupling the complement to e (downstream).
# Let me extract the δ-structure:
loss_d0 = loss.subs(delta,0)
dloss = sp.expand(loss - loss_d0)
print("δ-dependent part of loss:", sp.collect(dloss, delta))
print()
print("⟹ δ enters as: 2δ·(Gq·e) + δ²‖e‖² — a LINEAR (bilinear) coupling + quadratic.")
print("  This is the (b·E + SΓ) structure with b~δ·e, E~the survivor, SΓ~G·survivor. δ is the pivot →0.")
print("  BUT the reduced core that vanishes at the deepest point is the SURVIVOR chain ‖G·survivor‖²,")
print("  and δ is bounded (→0) ⟹ it IS the hnode pivot column. The single Schur step peels δ, the")
print("  survivor (rank 2) recurses. CONSISTENT with the single-reduced-chain hnode IF the chart makes")
print("  the survivor block the SΓ and δ the b. The coupling Gq·e is absorbed into the (b·E+SΓ) cross term.")

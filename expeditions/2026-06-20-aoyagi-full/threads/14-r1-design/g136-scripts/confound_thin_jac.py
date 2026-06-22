# (4,3,2) first factor C1 is 4x3 (codim {C1=0} = 12). Blow up {C1=0}: pivot c00=u, all 12 entries
# scale by u. Jacobian of (c_ij) -> (u, u v_ij for 11 others): |det| = u^{12-1} = u^11 => h=11.
# core∘φ: ‖C1 C2‖^2 with C1=u·Chat => = u^2·‖Chat C2‖^2 => k=1. ratio (11+1)/(2·1)=12/2=6=Mval(0,0)/2. ✓
import sympy as sp
u=sp.Symbol('u',positive=True)
# Chat 4x3 (pivot 1), C2 3x2
Chat=sp.Matrix(4,3, lambda i,j: 1 if (i,j)==(0,0) else sp.Symbol(f'h{i}_{j}'))
C2=sp.Matrix(3,2, lambda i,j: sp.Symbol(f'd{i}_{j}'))
C1=u*Chat
P=C1*C2
f=sp.expand(sum(P[i,j]**2 for i in range(4) for j in range(2)))
orders=[m[0] for m in sp.Poly(f,u).monoms()]
print(f"(4,3,2) blow up {{C1=0}}: core∘φ u-order min={min(orders)} (k_E={min(orders)//2})")
# Jacobian exponent: blowing up {C1=0} codim 12 => the affine chart map (12 vars -> u + 11 v's) has
# |det D| = u^{11} (standard coordinate-subspace blow-up of codim c => u^{c-1}).
print("  Jacobian |det Dφ| = u^{12-1} = u^11 => h=11 (codim-12 blow-up). ratio=(11+1)/2=6=Mval(0,0)/2 ✓")
print()
# Now the THIN worry head-on: does {C1=0} have codim 12 in the WHOLE chain space? Yes -- it's 12 entry
# equations on C1. But is {C1=0} the DEEPEST stratum, or is the deepest stratum {prod=0} bigger?
# {C1=0} ⊂ {prod=0} (if C1=0 then product=0). codim{C1=0}=12. The deepest ADMISSIBLE stratum t=(0,0)
# means rank(C1)=0 AND rank(C1C2)=0; rank(C1)=0 <=> C1=0. So deepest stratum = {C1=0}, codim 12 = Mval(0,0).✓
# The generator-Jacobian rank 8 < 12 is the LOSS HESSIAN rank, a DIFFERENT object (the loss is
# ‖prod‖^2, its 2-jet at origin sees only the bilinear part). Geometric codim of {C1=0} = 12. No conflict.
print("CONFIRM: deepest stratum t=(0,0) = {C1=0}, geometric codim 12 = Mval(0,0). The gen-Jac/Hessian")
print("rank 8 is the loss 2-jet rank (a different object), NOT the geometric codim. No undershoot.")
print()
# The ONE thing to double check: is {C1=0} really codim 12 and not less due to the chain? C1 is a free
# 4x3 matrix block in Params, so {C1=0} is exactly 12 coordinate equations => codim 12 EXACTLY. Solid.

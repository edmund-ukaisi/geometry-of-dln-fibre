import sympy as sp
# VERIFY fm3's split claim: the residual Schur core ‖S·Γ‖²'s next-blow-up center = {S=0} ∪ {Γ=0},
# where {Γ=0} is a coordinate subspace (pivotBlowupOn direct, a) but {S=0}={d=ab} is BILINEAR
# (NOT a coordinate subspace, needs the triangular peel w:=d−ab first, b).
# fm3's model (rank-1 reduced, the smallest nontrivial): S = d − a·b (1×1 Schur), Γ = (Γ0, Γ1) row.
# residual core = ‖S·Γ‖² = (S·Γ0)² + (S·Γ1)² = (d−ab)²(Γ0²+Γ1²).
a,b,d,G0,G1 = sp.symbols('a b d G0 G1', real=True)
S = d - a*b
core = sp.expand(S**2 * (G0**2 + G1**2))
print("residual Schur core ‖S·Γ‖² =", core)
print("  = (d−ab)²·(Γ0²+Γ1²), S = d−ab (1×1 Schur), Γ=(Γ0,Γ1).")
print()
# The ZERO-SET {core = 0} = {S=0} ∪ {Γ=0} (a product of two sum-of-squares-ish factors):
print("=== center {core=0} = {S=0} ∪ {Γ=0} ===")
print("  {Γ=0} = {Γ0=0 ∧ Γ1=0}: a COORDINATE subspace (the coords Γ0,Γ1 set to 0). pivotBlowupOn fires")
print("    DIRECTLY on it (option a) — blow up the {Γ=0} coordinate center, regular pivot row spectator.")
print("  {S=0} = {d−ab=0} = {d=ab}: BILINEAR (a quadric in d,a,b), NOT a coordinate subspace.")
# Confirm {S=0} is NOT a coordinate subspace: it's {d=ab}, a non-linear (bilinear) hypersurface.
print("    {d=ab}: is it a coordinate subspace {some coords = 0}? NO — it's the graph d=ab, a bilinear")
print("    quadric. pivotBlowupOn (which blows up {active coords = 0}) CANNOT fire on {d=ab} directly.")
print()
# THE TRIANGULAR PEEL w := d − ab makes {S=0} a coordinate subspace {w=0}:
w = sp.Symbol('w', real=True)
print("=== the triangular peel w := d − ab (the #37 mechanism) ===")
print("  Change coords (d, a, b) → (w, a, b) with w = d − ab (d = w + ab). This is TRIANGULAR (d depends")
print("  on the others + w; a,b unchanged), det-1 (∂w/∂d = 1, lower-triangular Jacobian, det = 1).")
J = sp.Matrix([[sp.diff(w_expr, v) for v in (d,a,b)] for w_expr in (d-a*b, a, b)])
print("  Jacobian of (w,a,b)=(d−ab,a,b) wrt (d,a,b):"); sp.pprint(J); print("  det =", J.det(), " (=1, det-1 MP)")
core_w = sp.expand(core.subs(d, w + a*b))
print("\n  core in (w,a,b,Γ) coords =", core_w, " = w²·(Γ0²+Γ1²).")
print("  ⟹ {S=0} becomes {w=0}, a COORDINATE subspace. NOW pivotBlowupOn fires on {w=0}.")
print()
print("=== VERDICT: fm3 is RIGHT, and it matches my #131/g142 triangular D↔S+ba ===")
print("""
The peel w := d − ab IS the triangular D↔S+ba change (#37/#36): d = D-block, ab = the b·a outer product,
S = D − ba the Schur complement. The change (D-coords) → (S-coords, with S = D − ba) is exactly this
triangular det-1 peel. It is NEEDED because:
 - pivotBlowupOn blows up COORDINATE subspaces {active=0};
 - {S=0}={D=ba} is BILINEAR, not a coordinate subspace;
 - the peel w:=D−ba makes it {w=0}, a coordinate subspace pivotBlowupOn can hit.
So C1 = blow-up (x_p² weight) + TRIANGULAR det-1 peel (w:=D−ba, the ΣM−2 Schur reduction, makes the
center a coordinate subspace) + recurse. NOT pure blow-up; NOT the squeeze; NOT lemma2Fwd. The peel is a
LIGHT det-1 straightening = the #37 mechanism. fm3's "(b)-with-nuance" is correct.
""")

import sympy as sp, random
# RE-TEST the squeeze near the deepest point (Φ→0). The deepest point of the recursion is where the
# SURVIVOR's downstream product → 0, i.e. G·survivor → 0, i.e. Φ → 0. The defect δ is a SEPARATE
# coordinate. The question: is the loss ‖Gp‖²+‖Gq+δe‖² comparable to a SINGLE reduced core Φ near
# the deepest point, OR does δ's coupling to the (vanishing) survivor break it?
#
# Critical: what IS the reduced chain S.red for the C5 node, and what is its deepest point?
# The C5 step peels the rank-1 defect δ. The reduced chain = the survivor (rank 2) continuing. Its
# loss = ‖G·survivor‖² = ‖G[p|q]‖² = Φ. The deepest point of S.red is where G·survivor=0 (Φ=0).
# At THAT point, the FULL C5 loss = 0 + ‖0 + δe‖² = δ²‖e‖². So the full loss at the reduced-deepest
# is δ²‖e‖² ≠ 0 unless δ=0.
#
# This means: the C5 node's "deepest point" (full loss=0) requires BOTH Φ=0 AND δ=0. These are
# INDEPENDENT directions. So the node loss is, near the deepest point, ≈ Φ + δ²‖e‖² + cross.
# The hnode form G²=‖SΓ‖² requires the reduced core SΓ to be the FULL singular content, with the
# pivot b→0 as a SEPARATE bounded direction. But δ is NOT bounded-relative-to-Φ — it's an
# INDEPENDENT singular direction (the loss vanishes to 2nd order in δ too).
#
# So the honest structure is: loss ≈ Φ(survivor core) + δ²‖e‖²(a SECOND singular direction) + cross.
# This is TWO singular scales, not one core + a bounded pivot. Let me confirm by checking the
# multiplicity/RLCT: the C5 node loss has rlct contributions from BOTH δ and the survivor.
print("=== C5 node: TWO independent singular directions (δ defect + survivor core) ===")
print()
# At the reduced-chain deepest point (Φ=0): loss = δ²‖e‖² + 2δ(0)·e = δ²‖e‖² (Gq=0 there).
# So along the δ-axis (survivor at its deepest), loss = δ²‖e‖² ~ a smooth Morse direction (rlct of
# δ²: contributes 1/2 per the standard ½). The δ-defect gives a CLEAN regular ½ — like a regular gen!
# So δ is NOT an "exceptional blow-up coordinate with k=1,h=codim-1"; it's a REGULAR (smooth, ½) dir
# at the reduced-deepest. The hnode pivot b should →0 FASTER than √loss; here δ is ½-Morse, same scale.
#
# Reconsider: maybe δ IS a regular generator (the rank-1 defect contributes ONE regular square δ²‖e‖²
# ~ one smooth coord). Then the C5 node is: [reduced survivor core Φ] + [ONE regular square from δ].
# That fits the hnode with the regular block Σ E_j² INCLUDING the δ-direction! Let me re-map:
#   regular block Σ E_j²: includes δ·‖e‖ (one regular gen) + the survivor's full-rank smooth parts.
#   reduced core SΓ: the survivor's TRULY singular continuation (after its own full-rank peeled).
# The cross term 2δ(Gq·e): does it obstruct treating δ as regular? In a regular sequence, cross terms
# with the singular core are ALLOWED if the regular gens form a regular sequence transverse to the core.
print("KEY REALIZATION: δ²‖e‖² at the reduced-deepest is a ½-Morse (REGULAR) direction, NOT an")
print("exceptional blow-up coordinate. So the rank-1 defect δ contributes a REGULAR generator, and")
print("the C5 node = [survivor reduced core] + [regular gen from δ] + cross.")
print()
# So the hnode form: flatCore = Σreg²(incl. δ-gen) + Σ(b E + SΓ)². But then where's the pivot b?
# For a PURE regular defect (δ smooth, no blow-up needed), there is NO pivot b — it's just Fubini:
# rlct(survivor core + δ²) = rlct(survivor core) + rlct(δ²) = rlct(core) + 1/2. That's C2/C4-like
# (pass-through / Fubini), NOT a C1 blow-up with a pivot!
print("⟹ HYPOTHESIS SHIFT: the C5 partial-drop defect (rank 1) may resolve as a REGULAR/Fubini")
print("   direction (½ each), NOT a C1 blow-up. The node = survivor-core ⊞ regular-defect (Fubini).")
print("   Test: is the loss exactly [survivor core] + [smooth Σx²] in SUITABLE coords (Fubini-split)?")
print()
# Test Fubini-separability: can we change coords so loss = f(survivor coords) + g(defect coords),
# DISJOINT? The cross term 2δ(Gq·e) couples them. Complete the square in δ:
#   ‖Gq + δe‖² = ‖e‖²(δ + (Gq·e)/‖e‖²)² + ‖Gq‖² - (Gq·e)²/‖e‖².
# Substitute δ' = δ + (Gq·e)/‖e‖² (a SHEAR, smooth invertible since ‖e‖²≠0 — e is the bounded gauge).
#   = ‖e‖²δ'² + [‖Gq‖² - (Gq·e)²/‖e‖²].
# So loss = ‖Gp‖² + ‖e‖²δ'² + ‖Gq‖² - (Gq·e)²/‖e‖²
#         = ‖e‖²δ'²  +  [‖Gp‖² + ‖Gq‖² - (Gq·e)²/‖e‖²].
# The first term ‖e‖²δ'² = a REGULAR square (e bounded ≠0). The bracket = the PROJECTED survivor core
# (survivor minus its e-component) = the reduced chain after peeling the δ'-direction. CLEAN SPLIT!
print("EXACT FUBINI SPLIT via δ-shear δ' = δ + (Gq·e)/‖e‖²  (smooth, ‖e‖²≠0 since e bounded gauge):")
print("  loss = ‖e‖²·δ'²  +  [‖Gp‖² + ‖Gq‖² - (Gq·e)²/‖e‖²]")
print("       = [regular square: ‖e‖²δ'²]  ⊞  [reduced survivor core, DISJOINT in δ']")
print("  ⟹ the C5 defect resolves by a SHEAR + Fubini (regular ½), NOT a blow-up pivot. CLEAN.")
# Verify the split is exact:
o=3
G=sp.Matrix(o,2,sp.symbols('g0:6',real=True)); e=sp.Matrix(o,1,sp.symbols('e0:3',real=True))
p=sp.Matrix(2,2,sp.symbols('p0:4',real=True)); q=sp.Matrix(2,1,sp.symbols('q0:2',real=True))
d=sp.Symbol('d',real=True)
Gp=G*p; Gq=G*q
loss=sum(Gp[i,j]**2 for i in range(o) for j in range(2))+sum((Gq[i,0]+d*e[i,0])**2 for i in range(o))
enorm2=sum(e[i,0]**2 for i in range(o)); Gqe=sum(Gq[i,0]*e[i,0] for i in range(o))
dp=d+Gqe/enorm2
split=enorm2*dp**2+(sum(Gp[i,j]**2 for i in range(o) for j in range(2))+sum(Gq[i,0]**2 for i in range(o))-Gqe**2/enorm2)
print("\n  EXACT split check (loss - shear-split):", sp.simplify(loss-split))

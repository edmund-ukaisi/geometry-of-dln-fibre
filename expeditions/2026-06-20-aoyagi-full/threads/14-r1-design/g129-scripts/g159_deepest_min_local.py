import sympy as sp
# CAREFUL re-examination: D1 (a) compares the LOCAL rlct of the SAME loss dlnLoss H B at deepest vs v
# (same H, same B). My M-monotonicity test was WRONG (it compared different ambient problems). The real
# question: is the LOCAL rlct of dlnLoss H B at the deepest point ≤ at any other fibre point v?
# Concrete fibre: (2,2,2), B=0 (r=0... no, take r=1). Actually simplest: L=1, H=(2,2), B rank 1.
# dlnLoss = ‖A − B‖², A the single 2×2 layer, B fixed rank-1. optimalSet = {A : A = B} (single point!).
# Too trivial. Take L=2, H=(2,2,2), B=0 (r=0 deepest = origin). optimalSet = {(A1,A2): A1 A2 = 0}.
A1=sp.Matrix(2,2,sp.symbols('a0:4')); A2=sp.Matrix(2,2,sp.symbols('b0:4'))
P=sp.expand(A1*A2); loss=sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
# deepest point: A1=A2=0 (origin, the most degenerate). a general v ∈ optimalSet: A1 A2=0, e.g.
# A1 = [[1,0],[0,0]] (rank1), A2 = [[0,0],[0,1]] (rank1), A1 A2 = 0. v = this point (NOT origin).
print("=== D1 (a) concrete: (2,2,2) B=0, deepest=origin vs a general fibre point v ===")
# local rlct at the ORIGIN: loss = ‖A1 A2‖², all bilinear, deepest. Known rlct (the headline) = ... for
# r=0, M=H=(2,2,2), rlct = lambdaCore(2,2,2)=3/2? No — r=0 means B=0, deepest=origin, rlct=3/2 is the
# r=0 headline. At a GENERAL v (A1 rank1, A2 rank1, off origin): the loss near v is LESS degenerate.
# Verify the local rlct at v is LARGER (deepest=origin is the min):
print("""
The local rlct of ‖A1 A2‖² at the ORIGIN (deepest, all factors 0) is the MOST degenerate — every
direction is a zero of the bilinear product. At a general v ∈ {A1 A2=0} with A1,A2 ≠ 0 (e.g. A1 rank1,
A2 rank1, off origin), the loss is LESS degenerate (fewer vanishing directions — the nonzero entries of
A1,A2 are regular). So rlct(origin) ≤ rlct(v). This IS Aoyagi Thm 2 (deepest = min local rlct).

THE L1-SEPARABILITY QUESTION (the critical one): can we PROVE rlct(origin) ≤ rlct(v) WITHOUT the
resolution value, from block_elimination + the homogeneous structure ALONE?
""")
# The KEY structural fact (value-independent): ‖A1 A2‖² is HOMOGENEOUS (degree 4, scaling A1,A2 by t
# scales loss by t⁴ — well, by the product). At the ORIGIN it's the FULL homogeneous polynomial. At a
# general v, the loss is loss(v + w) = the SHIFTED polynomial — and its LEADING (lowest-degree) part at
# v is a LOWER-degree truncation (the deepest's homogeneous part dominates). Concretely:
t = sp.Symbol('t', positive=True)
# loss(t·A1, t·A2) = t⁴ ‖A1 A2‖²... no, ‖(tA1)(tA2)‖² = t⁴‖A1A2‖². Homogeneous degree 4 in the joint scale.
loss_scaled = sp.expand(loss.subs({s: t*s for s in list(A1)+list(A2)}))
deg_t = sp.Poly(loss_scaled, t).degree()
print(f"  ‖A1 A2‖²(t·params) = t^{deg_t}·‖A1 A2‖² — homogeneous degree {deg_t} at the origin.")
print("""
THE L1-SEPARABLE ARGUMENT (value-independent, the prove-or-surface answer):
At the origin (deepest), dlnLoss = ‖∏C‖² is HOMOGENEOUS (the joint-scaling degree, here 4 for L=2).
At a general fibre point v, dlnLoss(v + w) (Taylor at v) has LEADING part = the lowest-degree form in w,
and since v is a ZERO of dlnLoss (v ∈ optimalSet), the leading part is a NONTRIVIAL form whose degree is
≤ the homogeneous degree at the origin. The origin's loss = the FULL homogeneous form (no lower-degree
part, since the origin is the most degenerate zero). The standard RLCT fact: a function's rlct at a point
is determined by its leading (Newton-polytope) behavior; the MORE degenerate point (lower-order vanishing
... wait, HIGHER-order vanishing = MORE degenerate = SMALLER rlct). The origin vanishes to the FULL
homogeneous order (degree 4 here, ALL low-order terms zero); v vanishes to a LOWER order (some
linear/quadratic terms in w nonzero, since v's regular directions). HIGHER vanishing order at origin ⟹
smaller rlct at origin. THIS is value-independent (the vanishing order is read off the Taylor expansion,
block_elimination gives the regular directions at v) — BUT making it a CLEAN rlctAtOn_mono needs the
deepest loss to pointwise-DOMINATE the v loss near a common frame, which is NOT automatic from
vanishing-order alone (x⁴ vs x²: x⁴ ≤ x² near 0 ✓, but the multivariate version needs care).
""")
print("VERDICT (prove-or-surface): the deepest=min-rlct is MORALLY L1-separable (homogeneity + higher")
print("vanishing order at the deepest, value-independent via block_elimination + the homogeneous core),")
print("BUT the clean rlctAtOn_mono pointwise-domination |deepest-loss| ≤ |v-loss| near a common frame is")
print("NOT a one-line consequence — it needs the homogeneous-domination lemma (deepest = leading form,")
print("dominates the shifted v-loss). NEEDS A REAL PROOF, not a citation — and it is L1 (no resolution")
print("value), BUT it is NOT trivial. FLAG: this is a genuine sub-lemma, provable L1, but heavier than")
print("'cite Aoyagi Thm 2'. Confirm with a Codex decorrelated check before asserting L1-separable.")

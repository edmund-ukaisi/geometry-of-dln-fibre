import sympy as sp
# The load-bearing multivariate step: is the deepest loss POINTWISE-DOMINATED by the v loss near a
# COMMON frame, so rlctAtOn_mono gives rlctAt(deepest) ≤ rlctAt(v)? The honest difficulty (g159):
# the two losses are at DIFFERENT basepoints; rlctAtOn_mono needs them at ONE point with |G|≤|F|.
#
# THE BRIDGE that makes it work (the homogeneous-domination, value-independent): the deepest loss
# F_deep(w) = ‖∏C(w)‖² (homogeneous, basepoint 0). The v loss F_v(w) = ‖∏C(v+w)‖² (basepoint 0 in
# w-coords, v's regular dirs nonzero). CLAIM: F_deep(w) ≤ F_v(w) near 0 ... NO, that's false in general
# (different functions). The RIGHT bridge: a CHANGE OF VARIABLES φ near v with φ(0)=v, under which
# F_v ∘ φ ≥ F_deep (the deepest is the most-degenerate, dominated). This φ is the gauge chart at v —
# which for non-rank-exact v is the broader split. So we're BACK to charting v OR a global argument.
#
# CLEANEST value-independent route (test it): the deepest point is the LIMIT of v under the scaling
# v_t = t·v (t→0): as t→0, v_t → 0 = deepest (B=0 core case). The loss F(t·v + w) interpolates. The rlct
# is LOWER-SEMICONTINUOUS under such degeneration? rlct(limit) ≤ liminf rlct — i.e. the rlct can only
# DROP in the limit. The deepest = the t→0 limit ⟹ rlct(deepest) ≤ rlct(v). Is rlct lower-semicontinuous
# under this scaling-degeneration, value-independently?
print("=== The bridge: is rlct lower-semicontinuous under deepest = scaling-limit of v? ===")
print("""
The deepest point (B=0 core) is the t→0 limit of v_t = t·v (v ∈ optimalSet, ∏(t·v) = t^L ∏v → 0). The
local rlct as a function of the basepoint is LOWER-SEMICONTINUOUS (a standard RLCT fact: the rlct can
only drop at more-degenerate/limit points — Watanabe; the most singular point of a family has the min
rlct). So rlct(deepest) = rlct(t→0 limit) ≤ liminf_{t→0} rlct(v_t). If rlct(v_t) is constant in t
(scaling-invariance of the local rlct under v↦t·v — TRUE for homogeneous loss: rlct(F at t·v) = rlct(F
at v) since t·v and v are on the same scaling ray and F is homogeneous), then rlct(deepest) ≤ rlct(v).
⟹ D1 (a) via: (1) lower-semicontinuity of local rlct under degeneration [a GENERAL RLCT fact, NOT the
resolution value]; (2) scaling-invariance of rlct along the ray v↦t·v [from F homogeneous, L1].
""")
# Is this clean? Lower-semicontinuity of the RLCT is a real theorem (Varchenko/semicontinuity of lct),
# value-independent. BUT: is it BANKED in Mathlib / the harness? Almost certainly NOT. So it would be a
# NEW analytic primitive (heavier than rlctAtOn_mono). And scaling-invariance: rlct(F, t·v) = rlct(F, v)?
# F at basepoint t·v vs v — F(t·v + w) vs F(v + w'). For HOMOGENEOUS F these are related by w-scaling,
# but the local rlct at t·v is NOT obviously = at v (different neighborhoods). Let me check on the (1,1,1)
# core (c1 c2)²: rlct at a point (a,b) with a·b=0 (optimalSet).
c1,c2 = sp.symbols('c1 c2', real=True)
F = (c1*c2)**2
# at the deepest (0,0): F = (c1 c2)², rlct = 1/2 (computed before). at v=(a,0) a≠0 (a·0=0, in optimalSet):
# F(a+w1, 0+w2) = ((a+w1)w2)² = (a+w1)² w2². Near (a,0): a+w1 ≈ a (unit, ≠0), so F ≈ a²·w2² = unit·w2².
# rlct of unit·w2² at w2=0 = 1/2 (single smooth square). SAME as deepest! So rlct(deepest)=rlct(v)=1/2 here.
print("(1,1,1) core (c1 c2)²: rlct at deepest (0,0) = 1/2; at v=(a,0) a≠0: F≈a²w2² (unit·square), rlct=1/2.")
print("  ⟹ EQUAL here (1/2 ≤ 1/2 ✓, D1 (a) holds with equality). Consistent.")
print()
# Try a case where v gives STRICTLY larger rlct: (2,2,2) B=0. deepest=origin rlct=3/2. v with A1,A2 rank-1
# off-origin: the loss near v is LESS degenerate. Hard to compute rlct directly, but the structure:
print("=== VERDICT (my exact-algebra read, pre-Codex) ===")
print("""
D1 (a) IS provable value-independently, via TWO general RLCT facts:
 (L1-a) SCALING-INVARIANCE: the local rlct of a homogeneous F is constant along the scaling ray v↦t·v
        (F homogeneous ⟹ the germ at t·v is a rescaling of the germ at v). [L1, from homogeneity.]
 (L1-b) LOWER-SEMICONTINUITY of the local rlct under degeneration (deepest = t→0 limit of v_t=t·v):
        rlct(deepest) ≤ liminf rlct(v_t) = rlct(v). [A GENERAL analytic fact — Varchenko/lct
        semicontinuity — NOT the resolution value, NOT Aoyagi Thm 2.]
So it is L1-SEPARABLE (no resolution value, no 2nd citation of Aoyagi Thm 2) — BUT (L1-b) lower-
semicontinuity of the RLCT is a NONTRIVIAL analytic primitive that is almost certainly NOT banked in
the harness/Mathlib. So the HONEST flag: D1 (a) is L1-separable IN PRINCIPLE (semicontinuity +
homogeneity, value-independent), but it needs the RLCT-lower-semicontinuity primitive, which is a NEW
heavy analytic lemma (comparable to S1.1's weightedThreshold_transport). It is NOT 'cite Aoyagi Thm 2'
(good — no 2nd citation), but it is NOT free either. SURFACE THIS: D1 ≥ needs RLCT-semicontinuity (new,
provable, value-independent) OR a more elementary homogeneous-domination if one exists. Codex check
pending to confirm semicontinuity is the right primitive + whether a lighter route exists.
""")

import sympy as sp
# VERIFY (adversarially) the scaling-invariance claim L1-a: is rlct(F at t·v) = rlct(F at v) for
# homogeneous F? The local rlct at basepoint p depends on the germ of F at p. For t·v vs v:
#   germ of F at t·v: F(t·v + w), w near 0.
#   germ of F at v:   F(v + w'), w' near 0.
# F homogeneous of degree D: F(t·v + w) = ? There's NO clean relation F(t·v+w) ↔ F(v+w') unless we scale
# w too. The map w ↦ t·w': F(t·v + t·w') = t^D F(v + w') (homogeneity). So F at t·v, under the LINEAR
# c-o-v w = t·w' (scaling, det = t^(dim), a MP-up-to-constant change), equals t^D · F(v + w'). The rlct
# is invariant under (a) the linear c-o-v w=t·w' (it's a diffeo, scaling — rlct invariant under diffeo)
# and (b) the constant factor t^D (a unit, rlct-invariant). So rlct(F at t·v) = rlct(F at v). ✓
print("=== Scaling-invariance L1-a: rlct(F at t·v) = rlct(F at v), F homogeneous deg D ===")
print("""
F homogeneous degree D. The germ of F at t·v: F(t·v + w). Substitute w = t·w' (linear c-o-v, scaling by
t, a diffeo for t≠0): F(t·v + t·w') = F(t·(v+w')) = t^D · F(v + w') (homogeneity). So:
  F(· at basepoint t·v) ∘ (w=t·w')  =  t^D · F(· at basepoint v).
rlct is invariant under (a) the diffeo w=t·w' [scaling, a change of variables — rlct diffeo-invariant]
+ (b) the constant t^D [a positive unit — rlct unit-invariant]. ⟹ rlct(F, t·v) = rlct(F, v). ✓ L1-a HOLDS.
""")
# verify concretely: (c1 c2)² at v=(a,b) vs t·v=(ta,tb).
c1,c2 = sp.symbols('c1 c2', real=True); a,b,t = sp.symbols('a b t', real=True)
F = (c1*c2)**2  # degree 4 homogeneous
# germ at v=(a,b): F(a+w1, b+w2) = ((a+w1)(b+w2))². germ at t·v: F(ta+w1,tb+w2)=((ta+w1)(tb+w2))².
# under w=t·w': ((ta+tw1')(tb+tw2'))² = (t²(a+w1')(b+w2'))² = t⁴((a+w1')(b+w2'))² = t⁴·[germ at v]. ✓
germ_v = ((a+sp.Symbol('w1'))*(b+sp.Symbol('w2')))**2
germ_tv_scaled = sp.expand(((t*a+t*sp.Symbol('w1'))*(t*b+t*sp.Symbol('w2')))**2)
check = sp.expand(germ_tv_scaled - t**4*germ_v)
print(f"germ(t·v) under w=t·w'  −  t⁴·germ(v) = {check}  (0 ⟹ scaling-invariance confirmed concretely)")
print()
print("So L1-a (scaling-invariance) is SOLID and elementary (diffeo + unit invariance of rlct, both")
print("banked-ish: rlctAtOn_comp_homeomorph for the scaling diffeo + rlctAtOn_unit_invariant for t^D).")
print("The ONLY heavy piece is L1-b (lower-semicontinuity of rlct under v_t→deepest). THAT is the")
print("new primitive to surface.")
print()
# But wait — is L1-b (semicontinuity) even NEEDED, or can scaling-invariance + a direct limit give it?
# rlct(deepest) vs rlct(v): deepest = lim_{t→0} t·v. By L1-a, rlct(t·v) = rlct(v) for ALL t>0 (constant!).
# So rlct is CONSTANT (=rlct(v)) along the punctured ray t∈(0,1]. At t=0 (deepest), rlct(deepest) = ?
# Semicontinuity: rlct(deepest) ≤ liminf_{t→0} rlct(t·v) = rlct(v). So rlct(deepest) ≤ rlct(v). The
# semicontinuity gives the ≤ at the limit point. Without it, we'd only know rlct const on the open ray.
print("=== Is L1-b (semicontinuity) avoidable? ===")
print("""
By L1-a, rlct(F, t·v) = rlct(F, v) CONSTANT for all t ∈ (0,1] (the punctured ray). The deepest is t=0.
rlct(deepest) = rlct(F, 0). We need rlct(0) ≤ rlct(v) = the ray-constant. This is EXACTLY lower-
semicontinuity at the limit point t=0 (rlct(limit) ≤ liminf along the ray). It is NOT avoidable by
L1-a alone (which only gives the open-ray constancy). So L1-b (RLCT lower-semicontinuity) IS the needed
primitive. It's value-independent (a general analytic fact, NOT the resolution) but NOT banked.
""")

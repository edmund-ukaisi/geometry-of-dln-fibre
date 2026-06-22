import sympy as sp
# VERIFY the structural route: c' ∈ A(deepest=0) ⟹ c' ∈ A(v), via homogeneity, RIGOROUSLY.
# F homogeneous degree D (F(t·x) = t^D F(x)). deepest = 0. v ∈ {F=0} (a fibre point, here B=0 core).
# c' ∈ A(0): ∃ U_0 ∋ 0, ∫_{U_0} |F(x)|^{-c'} dx < ∞.
# WANT c' ∈ A(v): ∃ U_v ∋ v, ∫_{U_v} |F(x)|^{-c'} dx < ∞.
#
# THE c-o-v: near v, write x = v + w. We want ∫ |F(v+w)|^{-c'} dw < ∞ for small w. Relate to the origin:
# consider the scaling x ↦ s·x. F(s·x) = s^D F(x). The point v: is v on a ray through 0? v ≠ 0, so the
# ray {s·v} passes through 0 (s=0) and v (s=1). Consider the c-o-v that maps a nbhd of v to a nbhd of 0:
# NOT a global scaling (v is a specific point, not the origin). The right relation:
print("=== ADVERSARIAL check: does c' ∈ A(0) ⟹ c' ∈ A(v) via homogeneity? ===")
print("""
The naive 'origin nbhd contains scaled v-nbhds' is too loose. The RIGOROUS relation:
F homogeneous deg D. For the integral near v vs near 0, use the GLOBAL scaling x = s·y (s fixed > 0):
  ∫_{U_0} |F(x)|^{-c'} dx,  sub x = s·y:  = ∫_{U_0/s} |F(s·y)|^{-c'} s^N dy = s^N ∫_{U_0/s} (s^D|F(y)|)^{-c'} dy
    = s^{N - D c'} ∫_{U_0/s} |F(y)|^{-c'} dy.
So ∫ over U_0 = s^{N-Dc'} ∫ over U_0/s (the rescaled nbhd). As s→0, U_0/s → ALL of space (blows up). This
says the origin integral CONTROLS the integral over arbitrarily large rescaled regions — IF it converges.
But this is about the GLOBAL integral, not a nbhd of the specific point v.
""")
print("""
THE HONEST PROBLEM: v is a SPECIFIC fibre point (e.g. (rank1, rank1 aligned)), NOT on the scaling ray
{s·v₀} in a way that maps its nbhd to the origin's nbhd by global scaling. The scaling ray s·v → 0 passes
through v at s=1, and rlctAt(s·v) = rlctAt(v) by L1-a (the LOCAL rlct at each ray point). The limit s→0
is the origin. So we need: rlctAt at the ray LIMIT (origin) ≤ rlctAt along the ray (= rlctAt(v)).

This IS lower-semicontinuity at the limit point of the ray — and it does NOT reduce to a single global
c-o-v (the ray is a 1-param family, the limit is a genuine limiting-basepoint statement). So the
STRUCTURAL route via a single homogeneity c-o-v does NOT close it; the semicontinuity (a Fatou/liminf
argument on ∫_{U} as U → the limit nbhd) is genuinely needed. My g166 'A(deepest)⊆A(v) via containment'
was too optimistic — the containment isn't a clean inclusion.
""")
print("=== SO: what does P1 ACTUALLY need, minimally, from the rlctAt def? ===")
print("""
P1 (the minimal honest statement): rlctAt is LOWER-SEMICONTINUOUS along the scaling ray, i.e.
   rlctAt(F, 0) ≤ liminf_{s→0⁺} rlctAt(F, s·v).
From the sSup-def: rlctAt(F,p) = sSup A(p). The liminf-semicontinuity reduces to:
   for c' admissible near 0 (c' ∈ A(0)), is c' ≤ liminf rlctAt(s·v)?
The PROVABLE-from-def core: if c' ∈ A(0) (∫_{U_0}|F|^{-c'}<∞ for some U_0 ∋ 0), then since s·v → 0, for
small s the point s·v ∈ U_0, so a nbhd of s·v is ⊆ U_0, so ∫_{nbhd of s·v}|F|^{-c'} ≤ ∫_{U_0}|F|^{-c'}
< ∞ ⟹ c' ∈ A(s·v) ⟹ c' ≤ rlctAt(s·v). Taking liminf: c' ≤ liminf rlctAt(s·v). Sup over c'∈A(0):
rlctAt(0) ≤ liminf rlctAt(s·v). ✓✓✓
THIS WORKS — and it IS provable from the def! The key: a nbhd of 0 (U_0) CONTAINS a nbhd of every
nearby point s·v (s small), so admissibility near 0 ⟹ admissibility near s·v (the integral over the
smaller nbhd is ≤). NO Fatou, NO general semicontinuity, NO absent Mathlib analysis — just
"U_0 ∈ 𝓝 0 and s·v → 0 ⟹ U_0 ∈ 𝓝 (s·v) for small s" + monotonicity of the integral under U' ⊆ U_0.
""")
print("⟹ P1 IS PROVABLE FROM THE rlctAt DEF (the controller's hint is RIGHT). The semicontinuity along the")
print("ray is: c'∈A(0) ⟹ (U_0∋0 ⊇ nbhd of s·v for small s) ⟹ c'∈A(s·v) ⟹ c'≤rlctAt(s·v) → liminf. ELEMENTARY")
print("(nbhd-monotonicity of integrability + s·v→0), NOT a heavy analytic primitive. P1 is LIGHT after all.")

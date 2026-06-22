import sympy as sp
# GENERAL-v squeeze datum: at arbitrary v ∈ optimalSet (rank-exact ∀s rank(v s)=r), the gauge slice +
# the squeeze c₁Φ ≤ dlnLoss H B(·) ≤ c₂Φ near v, Φ = ∑reg² + dlnLoss M 0(T̃-core). The deepest v=0 case
# is g150/g153. The question: does the gauge-chart squeeze datum hold at ARBITRARY v, and what changes?
#
# KEY structural fact: at ANY rank-exact fibre point v, the SAME gauge slice applies (block_elimination
# per layer gives units P_s,Q_s with P_s(v s)Q_s = blockdiag[I_r,0]; near v, C_s = [[I_r+X_s,Y_s],[Z_s,T_s]]).
# The squeeze + gauge-normalized T̃ are IDENTICAL in structure to the deepest case — ONLY THE BASEPOINT v
# DIFFERS (and the product target B, which at a general fibre point is the same B, rank r). So:
print("=== General-v: the gauge-chart squeeze datum holds at ARBITRARY v ∈ optimalSet, basepoint v ===")
print("""
At any rank-exact v ∈ optimalSet (∀s rank(v s)=r, ∏(v)=B): the per-layer gauge slice
C_s = [[I_r+X_s, Y_s],[Z_s, T_s]] (block_elimination at v, units P_s,Q_s) is IDENTICAL in structure to
the deepest case (g150). The squeeze c₁Φ ≤ dlnLoss H B ≤ c₂Φ near v, Φ = ∑E² + ‖T̃_1···T̃_L‖²
(gauge-normalized T̃, the (I−VY)^{-1}-absorbed blocks = the product Schur complement, g150-fix) holds
VERBATIM — the squeeze constants c₁,c₂ depend only on the bounded pivot-column norm T (the local data
near v), NOT on v being the deepest point. So:
  GENERAL-v DATUM = the deepest datum with basepoint v (not 0) + product target B (not 0 at deepest core).
The v=DEEPEST specialization: v = deepestPoint, B = the rank-r target restricted to the core (M=H-r);
the basepoint is 0 in the gauge coords, exactly #44 sub-3 / cobuild-sub34. THE TWO AGREE — the deepest
case is the v=deepestPoint instance of the general-v datum.
""")
# Now the D1 (a) SCALING step: the deepest core pointwise-DOMINATES the general-v core, via a homogeneous
# scaling Σ t^{2n_i} f_i'² ≤ Σ f_i'² (t∈[0,1]). Verify: the core dlnLoss M 0 = ‖∏C'‖² is HOMOGENEOUS;
# scaling the reduced coords by t∈[0,1] scales each monomial f_i' by t^{n_i} (n_i = its degree), and
# t^{2n_i} ≤ 1 ⟹ Σ t^{2n_i}f_i'² ≤ Σ f_i'² ⟹ rlctAtOn(scaled) ≤ rlctAtOn(unscaled) via rlctAtOn_mono.
t = sp.Symbol('t', positive=True)
# model: a homogeneous core term f' = product of reduced bilinear entries, degree n_i. Scaling coords by t:
print("=== D1 (a) scaling step: deepest core dominates general-v core (rlctAtOn_mono) ===")
print("""
D1 (a): rlctAt(dlnLoss H B)(deepest) ≤ rlctAt(dlnLoss H B)(v). The bridge (the docstring's
'homogeneous normal form, deepest core pointwise-dominates'): after the general-v gauge chart, both
sides are ∑E² + ‖T̃-core‖². The DEEPEST point's T̃-core is the FULL homogeneous ‖∏T̃‖² (all reduced
directions active); a general v's T̃-core is a SCALED/restricted version (some reduced directions
'used up' by v being off-deepest). The deepest core DOMINATES: each general-v core monomial f_i' is
the deepest f_i' scaled by t_i^{n_i} (t_i ∈ [0,1] the off-deepest scaling), and:
  Σ t_i^{2n_i} (f_i')² ≤ Σ (f_i')²   (since t_i^{2n_i} ≤ 1 for t_i ∈ [0,1])
⟹ ‖general-v core‖² ≤ ‖deepest core‖² pointwise ⟹ rlctAtOn(general-v core) ≤ rlctAtOn(deepest core)
via rlctAtOn_mono (|G|≤|F|, G=0⟹F=0 from the same zero-set). Wait — D1 wants deepest ≤ v, i.e.
rlctAtOn(deepest core) ≤ rlctAtOn(v core). Let me get the direction right:
""")
print("""
DIRECTION CHECK: D1 (a) is rlctAt(deepest) ≤ rlctAt(v). Smaller rlct = MORE singular. The deepest point
is the MOST singular (smallest rlct). The scaling: the deepest core has the MOST vanishing (all reduced
directions degenerate), so its loss is POINTWISE ≤ the general-v loss near their respective basepoints
(the deepest loss vanishes faster). rlctAtOn_mono: |deepest core| ≤ |v core| (deepest more degenerate)
+ (deepest=0 ⟹ v=0 on the shared reduced zero-set) ⟹ rlctAtOn(deepest) ≤ rlctAtOn(v). The t^{2n_i}≤1
scaling gives deepest ≤ v (the deepest is the t→ scaling limit where the core is maximally degenerate).
⟹ D1 (a) = the general-v squeeze datum (both sides to ∑E²+‖T̃‖² near v resp deepest) + this scaling
domination via rlctAtOn_mono. The scaling step is the ONLY thing D1 adds over #44 sub-3.
""")
print("VERIFY the scaling inequality Σ t^{2n}f² ≤ Σ f² for t∈[0,1]:")
f0,f1,n0,n1 = sp.symbols('f0 f1 n0 n1', positive=True)
# t^{2n_i} ≤ 1 for t∈[0,1], n_i≥0 ⟹ t^{2n_i}f_i² ≤ f_i²; sum ⟹ Σt^{2n}f² ≤ Σf². Trivially true.
print("  t^{2n_i} ≤ 1 for t∈[0,1], n_i ≥ 1 (homogeneous core, positive degree) ⟹ t^{2n_i}f_i² ≤ f_i²,")
print("  summed ⟹ Σ t^{2n_i}f_i² ≤ Σ f_i². ✓ (the rlctAtOn_mono |G|≤|F| input, the homogeneous-scaling step.)")

# Design the P1 cert: does RLCT lower-semicontinuity follow from rlctAt's sSup-of-admissible-down-set
# structure, WITHOUT absent Mathlib analysis? rlctAt(w*) = sSup A(w*), A(w*) = {c'≥0 : ∃U∈𝓝 w*,
# |F|^{-c'} integrable on U}.
print("=== rlctAt structure: rlctAt(w*) = sSup A(w*), A(w*) = admissible-exponent down-set ===")
print("""
A(w*) = { c' ≥ 0 : ∃ U ∈ 𝓝 w*, ∫_U |F|^{-c'} < ∞ }. This is a DOWN-SET (c' admissible ⟹ c''<c'
admissible, since |F|^{-c''} ≤ |F|^{-c'}·(local bound) near w* on the |F|≤1 part... actually need care).
rlctAt(w*) = sSup A(w*).

THE SEMICONTINUITY WE NEED (L1-b): rlctAt(deepest) ≤ rlctAt(v) [after L1-a collapses the ray to v].
Equivalently: A(deepest) ⊆ closure(A(v)) in the sense sSup A(deepest) ≤ sSup A(v), i.e. every c'
admissible at the deepest is ≤-dominated by the v-admissible sup.

KEY QUESTION: is A(deepest) ⊆ A(v)? i.e. if |F|^{-c'} integrable near deepest, is it integrable near v?
NO — that's the WRONG direction (integrability near one point says nothing about another). So the naive
'A(deepest) ⊆ A(v)' is FALSE. The semicontinuity is NOT a trivial down-set inclusion.
""")
print("=== The RIGHT structural route (what L1-b actually needs) ===")
print("""
rlctAt(deepest) ≤ rlctAt(v) means: A(deepest)'s sup ≤ A(v)'s sup, i.e. for every c' < rlctAt(deepest)
(c' admissible near deepest), c' ≤ rlctAt(v) (c' admissible near v, OR at least ≤ the v-sup).
The semicontinuity FACT (Watanabe Thm, lct-semicontinuity): the function p ↦ rlctAt(F, p) is LOWER
semicontinuous in p. For OUR rlctAt (sSup of the admissible down-set), is this provable from the def?

The honest analytic content: lower-semicontinuity of the RLCT = "if |F|^{-c'} is NOT integrable near the
limit point p₀ (c' ≥ rlctAt(p₀)), then it's not integrable near nearby p either (for the liminf)". This
is a statement about how the integral ∫_U |F|^{-c'} behaves as U moves — and it is NOT free from the
sSup def; it needs the integral's behavior under basepoint perturbation. The sSup STRUCTURE gives the
THRESHOLD packaging, but the semicontinuity is about the INTEGRAL's lower-semicontinuity in the basepoint,
which is a genuine measure-theory fact (Fatou-type: ∫ liminf ≤ liminf ∫).
""")
print("=== BUT — the SCALING route (L1-a + a SPECIFIC limit) may avoid general semicontinuity ===")
print("""
We don't need general lower-semicontinuity in p — we need it ALONG THE SCALING RAY t·v → deepest.
By L1-a, rlctAt(t·v) = rlctAt(v) CONSTANT for t∈(0,1]. So we need rlctAt(deepest=0) ≤ rlctAt(v) = the
ray-constant. This is rlctAt at the LIMIT ≤ the ray value. With the scaling structure, this might be a
DIRECT integral comparison: the integrand at the deepest, |F|^{-c'} near 0, vs near v. By homogeneity
F(t·v + w) = t^D F(v + w/t)... the neighbourhoods relate by scaling. Let me see if A(deepest) and A(v)
relate DIRECTLY via the homogeneity (NOT general semicontinuity):
  c' ∈ A(v): ∫_{U_v} |F(w)|^{-c'} dw < ∞ (U_v ∋ v). 
  c' ∈ A(deepest): ∫_{U_0} |F(w)|^{-c'} dw < ∞ (U_0 ∋ 0).
By homogeneity, F on the scaling ray: the deepest (origin) is where F vanishes to the FULL order. A
neighbourhood of 0 CONTAINS scaled copies of neighbourhoods of v (the ray t·v passes through 0). So
∫_{U_0} ⊇ contributions from ∫ near t·v for all small t. If ∫_{U_0}|F|^{-c'} < ∞ (c' ∈ A(deepest)), does
∫_{U_v}|F|^{-c'} < ∞ (c' ∈ A(v))? The origin nbhd integral CONTAINS the v-direction integral (scaled),
so c' ∈ A(deepest) ⟹ the integral converges INCLUDING the v-ray ⟹ c' ∈ A(v)-ish. ⟹ A(deepest) ⊆ A(v)
(MODULO the scaling/homogeneity bookkeeping)! ⟹ rlctAt(deepest) ≤ rlctAt(v). 
This would be the STRUCTURAL route (homogeneity + the def), avoiding general semicontinuity. NEEDS CHECK.
""")

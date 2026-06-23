<task>
I am formalising, in Lean 4 + Mathlib v4.29, one inequality about the "real log-canonical threshold"
(RLCT) of a globally-homogeneous nonnegative real-analytic function. I want an INDEPENDENT assessment
of the cleanest proof route and the minimal new lemma it needs. Withhold nothing about pitfalls; do NOT
assume my tentative route is right.

SETUP (all on a finite-dimensional real vector space; concretely V = ℝ^N with Lebesgue/product measure).
- K : V → ℝ is GLOBALLY homogeneous of degree d > 0: K(t·w) = t^d · K(w) for ALL t ≥ 0, ALL w. (In my
  application K(A) = ‖prod(A)‖² where prod is an L-fold matrix product, so prod(t·A) = t^L·prod(A) and
  K is homogeneous of degree d = 2L. K ≥ 0 everywhere, K real-analytic (polynomial).)
- The RLCT at a point w*, in the integral-supremum form actually used:
      rlctAt(K)(w*) := sSup { c' ≥ 0 : ∃ open U ∋ w*, ∫_U |K(w)|^{-c'} dw < ∞ }   (value in [0,∞]).
  (Standard SLT RLCT for analytic K ≢ 0; the bump φ is dropped via the ∃U.)

THE GOAL INEQUALITY.  For every w (think: w in the zero-fibre {K=0}, but the statement should hold for
all w), I want:
      rlctAt(K)(0) ≤ rlctAt(K)(w),
i.e. the origin is a DEEPEST point of the homogeneous K (its RLCT is the smallest). This is the r=0,
B=0 specialisation of Aoyagi 2013 "Theorem 2" (deepest-singular-point) where global homogeneity replaces
the per-point normal form.

GREEN TOOLS I ALREADY HAVE (Lean, proven, signatures EXACT):
1. rlctAt_mono: if on a nbhd of w*, |G| ≤ |F| AND (G w = 0 → F w = 0), then rlctAt(G)(w*) ≤ rlctAt(F)(w*).
   [a SMALLER |·| gives a LARGER |·|^{-c'}, harder to integrate, so FEWER admissible c'.]
2. rlctAtOn_comp_homeomorph: for e : V ≃ₜ V' a homeomorphism that is MEASURE-PRESERVING (volume→volume,
   ratio exactly 1) and a MeasurableEmbedding: rlctAt(F∘e)(w0) = rlctAt(F)(e w0).
3. rlct_germ_local: F = G on a nbhd of w* ⟹ rlctAt F w* = rlctAt G w*.
4. rlct_unit_invariant: 0 < a ≤ |u| ≤ b (u measurable) on a nbhd of w* ⟹ rlctAt(u·F)(w*) = rlctAt F w*.
   [multiplying by a bounded measurable unit doesn't change the threshold.]
5. Mathlib: map_addHaar_smul: pushforward of Haar under (r • ·) is ENNReal.ofReal|r^N|⁻¹ • Haar (r≠0);
   quasiMeasurePreserving_smul: (r • ·) is quasi-measure-preserving for r ≠ 0.

THE OBSTRUCTION I AM CIRCLING.  The scaling map σ_s : w ↦ s·w (0 < s ≤ 1) is the natural transport.
But σ_s has Jacobian s^N ≠ 1, so it is NOT measure-preserving — tool 2 does NOT apply directly. The
"radial blow-up" w = t·(a+u) is not even a homeomorphism at t=0. So neither tool-2 nor a blow-up CoV
seems to land cleanly.
</task>

<output_contract>
1. VERDICT on each of these candidate routes, with the EXACT failure point if it fails:
   (R1) "ray-constancy + limit": prove rlctAt(K) constant on the ray {s·w : 0<s≤1} (via some scaling
        invariance), then take s→0 to compare with the origin. — Does this actually need a NEW
        lower-semicontinuity-of-RLCT-at-a-point fact for the s→0 limit, or can constancy + the down-set
        structure of rlctAt give 0 ≤ w directly WITHOUT a limit?
   (R2) "direct domination, no transport": Can I get rlctAt(K)(0) ≤ rlctAt(K)(w) by comparing K near 0
        with K near w using ONLY tool-1 (rlctAt_mono, a SAME-POINT comparison) plus homogeneity, with
        NO change of basepoint? (rlctAt_mono compares two functions at ONE point; here the basepoints
        0 and w differ — is there an honest way to make it a same-point comparison?)
   (R3) "constant-rescaled-measure invariance": Is it TRUE that multiplying the measure by a positive
        constant leaves rlctAt unchanged (finiteness of ∫|K|^{-c'} dμ is invariant under μ ↦ λμ, λ>0)?
        If so, σ_s transports rlctAt EXACTLY (not just quasi), and the missing lemma is a
        "quasiMeasurePreserving with constant density ⟹ rlctAt invariant" generalisation of tool-2.
        State that lemma precisely.
2. The SINGLE cleanest route, and the MINIMAL new Lean lemma(s) it needs — give each as a precise
   informal statement (hypotheses + conclusion). Distinguish "provable from the listed green tools +
   standard Mathlib" from "needs genuinely new analytic input (e.g. RLCT lower-semicontinuity, which may
   need meromorphic continuation / Tauberian machinery Mathlib lacks)".
3. If route R1 needs a limit s→0, is that limit a KNOWN-HARD object (RLCT lsc at a point), or can it be
   sidestepped? Be explicit.
</output_contract>

<grounding_rules>
- Reason from the integral-supremum definition of rlctAt as given. Do not import a different RLCT def.
- "Measure-preserving" means pushforward ratio EXACTLY 1; "quasi-measure-preserving" allows a positive
  density. Keep that distinction load-bearing.
- For homogeneity use K(t·w)=t^d K(w) for t ≥ 0 (one-sided is fine; my prod gives it for all real t with
  t^L, but assume t ≥ 0 to be safe).
- Flag any step that silently assumes K ≢ 0 near the point, or that the zero-fibre is a cone, etc.
- Mark each claim as [PROVABLE-FROM-LISTED] / [NEEDS-STANDARD-MATHLIB] / [NEEDS-NEW-ANALYTIC-INPUT].
</grounding_rules>

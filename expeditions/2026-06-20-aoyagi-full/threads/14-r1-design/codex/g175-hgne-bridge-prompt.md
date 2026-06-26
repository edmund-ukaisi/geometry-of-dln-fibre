<task>
Lean 4 + Mathlib v4.29 (toolchain leanprover/lean4:v4.29.0). I need the LIGHTEST proof route for a
measure-zero / ae-ne-zero fact, to discharge a hypothesis (`hGne`) in an RLCT proof.

THE TARGET (informal): Let M : Fin (L+1) → ℕ be layer widths with every M_s ≥ 1. Let
`prod M A` be the matrix product of the layer matrices (A : ∀ s : Fin L, Matrix (Fin (M s.castSucc))
(Fin (M s.succ)) ℝ), an (M_0 × M_L) matrix whose entries are POLYNOMIALS in the entries of A. Define
`dlnLoss M 0 A = ∑_{i,j} (prod M A i j)²` (the squared Frobenius norm of the product). I have a
measure-preserving flattening `paramsEquivFlat M : Params M ≃ᵐ (Fin N → ℝ)` (N = Σ_s M_{s.castSucc}·M_{s.succ}).

GOAL LEMMA:
  ∃ U ∈ 𝓝 (0 : Fin N → ℝ), ∀ᵐ z ∂(volume.restrict U),
    dlnLoss M 0 ((paramsEquivFlat M).symm z) ≠ 0.
i.e. dlnLoss M 0 (a sum of squares of polynomial entries) is ≠ 0 ALMOST EVERYWHERE on some
neighborhood of the origin. Equivalently: the polynomial map `prod M` is not identically zero (TRUE
when all M_s ≥ 1 — there's an explicit nonzero-product witness), so its zero set {prod M A = 0} is
measure-zero, so dlnLoss M 0 ≠ 0 a.e.

CONTEXT / what I found:
- Mathlib v4.29 has NO multivariate "nonzero real-analytic / polynomial ⟹ ae ne zero" lemma. The
  IsolatedZeros machinery (AnalyticAt.eventually_eq_zero_or_eventually_ne_zero) is 1-D (𝕜) only.
- dlnLoss M 0 = 0 ⟺ prod M A = 0 ⟺ ALL entries (prod M A) i j = 0. So it suffices that ONE entry
  (say (0,0)) is a nonzero polynomial with measure-zero zero set, OR that the whole sum-of-squares is.
- `prod M A i j` is a multivariate polynomial (a sum over paths of products of one entry per layer).
- I have measure-preserving flattening + continuity of dlnLoss already proven.

What I'm weighing: (a) general "nonzero MvPolynomial over ℝ^n has measure-zero zero set" (induct on
#vars + Fubini + univariate finite-roots Polynomial.setOf_isRoot — heavy, ~150-250 LoC); (b) a
DIRECT argument exploiting the product structure (e.g. a single generic line/ray where the product is
a nonzero univariate polynomial in t, so finitely many bad t); (c) some Mathlib lemma I'm missing
(MeasureTheory / analytic / polynomial) that gives ae-ne-zero or measure-zero zero-set more cheaply.
</task>

<output_contract>
Terse, decisive. Exactly:
1. THE LIGHTEST ROUTE: (a) general MvPolynomial measure-zero, (b) direct line/ray argument, or (c) a
   specific Mathlib lemma. Pick ONE + one-sentence why it's lightest at v4.29.
2. The KEY Mathlib lemma names (v4.29) the chosen route hangs on — measure-zero of zero-set, Fubini /
   Measure.prod, univariate finite-roots, AnalyticOnNhd, whatever. Flag any you're UNSURE exists at
   v4.29 (vs inferring from a later Mathlib).
3. The SUBLEMMA DECOMPOSITION for the chosen route (the 3-6 named intermediate steps), in dependency
   order. Line-count estimate per step (NOT wall-clock).
4. THE ONE BIGGEST RISK / where this walls in Lean (the cast/Fubini-restrict/measure-zero-of-graph
   friction), and the cheapest mitigation.
5. Is there a route that AVOIDS measure-zero entirely — e.g. an OPEN set near 0 where prod M ≠ 0
   EVERYWHERE (not just a.e.)? If so, that turns ∀ᵐ into ∀-on-an-open-set (much lighter). Does an
   explicit small-perturbation-of-a-nonzero-witness open set work, given the basepoint is 0 (where
   prod M 0 = 0, so the witness must be AT a nonzero point)? yes/no + why.
</output_contract>

<grounding_rules>
Distinguish Mathlib lemmas you're CONFIDENT exist at v4.29 from ones you're INFERRING. If you propose
a lemma name, mark it [confident] or [infer]. The goal is the cheapest HONEST route — if (a) is
genuinely the only sound route, say so even if heavy. Do not invent a one-line tactic.
</grounding_rules>

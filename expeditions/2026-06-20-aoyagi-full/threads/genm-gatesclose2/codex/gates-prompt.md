<task>
I am formalising in Lean 4 (Mathlib) the L=2 case of the RLCT (real log-canonical
threshold) headline for deep linear networks. The last open leaf reduces to TWO
"gates" that I must prove. I want a decorrelated verdict on WHETHER each gate is
TRUE as literally stated, and if so the MINIMAL missing analytic lemma(s), or a
counterexample if false. Do NOT write Lean; reason mathematically.

SETUP (real-analysis / RLCT, all local at a point):
- `rlctAtOn f p` = the real log-canonical threshold of `f` at point `p`:
  the supremum of c>0 such that ∫_{nbhd of p} |f|^{-c} < ∞. (Larger = milder singularity.)
- `m := nRegL2 H r` is a fixed natural number ("regular block dimension").
- `q : (Fin m → ℝ) × Y → ℝ^n` is a residual vector field (Y a finite-dim real space),
  and the "peel" function is
      f(s,z) = (∑_{i<m} s_i²) + (∑_{j<n} q(s,z)_j²)   ≥ 0.
- `v` ranges over `optimalSet H B` = the zero-fibre {A : prod(A) = B} (a real
  algebraic variety); `rlctAt v` is the local RLCT of the DLN loss at `v`.

GATE 1 (hRne, "slice non-vanishing"), stated ∀ q:
  For every `v ∈ optimalSet`, every `q : (Fin m→ℝ)×Y → ℝ^n` with
    (i) q is C² (ContDiff ℝ 2),  (ii) q(0, t0) = 0,
    (iii) rlctAt v = rlctAtOn f (0,t0)     [the "chart transfer" equation],
  THEN: ∃ nbhd U of t0 such that the slice R(z) := ∑_j q(0,z)_j²  is ≠ 0 for
  a.e. z ∈ U (Lebesgue).

GATE 2 (hInterface, "degraded core"), stated ∀ q (same hyps (i)-(iii)):
  THEN for the SECOND-peel residual q₂ built from q (there is a fixed count
  `e := extraCountRect (H0-r) (H2-r) a b`, a,b = layer-rank rises at v), whenever
    rlctAtOn (z ↦ R(z)) t0 = rlctAtOn (p ↦ ∑ p.1² + ∑ q₂(p)²) (0, t0₂),
  we have BOTH: (a) q₂'s slice ∑ q₂(0,·)² is a.e.-nonzero near t0₂, AND
  (b) rlctAtOn (t ↦ ∑ q₂(0,t)²) t0₂ = ofReal(lambdaCore(M')) where M' is a fixed
  reduced-width vector (the "degraded core" value from the R1 resolution).

WHAT I KNOW / ALREADY TRIED:
- The CONCRETE q that arises (from an Implicit Function Theorem chart of the DLN
  loss) is only tracked as C² in the formalization — NO analyticity is carried.
- The a.e.-positivity machinery available is for POLYNOMIAL functions only
  (nonzero polynomial ⟹ zero-set has measure zero). It does NOT apply to a
  general C² q.
- The R1 resolution `r1_resolution_general` computes rlctAtOn of the POLYNOMIAL
  DLN model core `dlnLoss M' 0` at the origin = ofReal(lambdaCore M'). It is NOT
  a statement about an arbitrary C² residual q₂.
- My analysis of GATE 1: if the slice zero-set {R=0} has positive Lebesgue
  measure in every nbhd of t0, then (since q(0,z)=0 there and q is C², so
  q(s,z)=O(|s|) ⟹ ∑q(s,z)²=O(|s|²) there) f(s,z) ≍ ∑ s_i² on that positive-measure
  z-set, forcing ∫|f|^{-c} = ∞ for c ≥ m/2, hence rlctAtOn f (0,t0) ≤ m/2. So GATE 1
  holds PROVIDED rlctAt v > m/2. But rlctAt v > m/2 is NOT among the gate hypotheses.
  Counterexample when rlctAt v = m/2 (degenerate core): take q ≡ 0; then f = ∑s²,
  rlctAtOn f = m/2 = rlctAt v satisfies (i)-(iii), but R ≡ 0, so the conclusion fails.
- So my tentative verdict: GATE 1 as literally stated (∀ C² q, only hyps (i)-(iii))
  is FALSE in general; it becomes TRUE if we additionally know rlctAt v > m/2 (which
  for `v ∈ optimalSet` at a nondegenerate reduced core `M'=H-r` follows from
  lambdaCore(M') > 0), AND requires a new "capping lemma": positive-measure slice
  zero-set ⟹ rlctAtOn f ≤ m/2.
</task>

<output_contract>
Respond in EXACTLY these sections, terse:

1. GATE 1 VERDICT — one of {TRUE-as-stated, FALSE-as-stated, TRUE-only-with-extra-hyp}.
   If FALSE or needs-extra-hyp: state the exact missing hypothesis and confirm/refute
   my q≡0 counterexample. If TRUE-only-with-extra-hyp: give the MINIMAL set of extra
   facts + the single new analytic lemma needed, and rate its difficulty
   (bounded-bookkeeping / moderate / hard-new-analysis).

2. THE CAPPING LEMMA — is my claim correct that "R:=∑q(0,·)² has positive-measure
   zero-set in every nbhd of t0 ⟹ rlctAtOn(∑s²+∑q²)(0,t0) ≤ m/2" is true for C² q?
   Give the cleanest proof sketch OR a counterexample. Rate formalization difficulty.

3. GATE 2 VERDICT — same schema. In particular: can part (b) (identify the C² residual
   q₂'s slice-RLCT with the POLYNOMIAL model lambdaCore(M')) be obtained from the R1
   polynomial resolution alone, or does it require an extra chart-invariance /
   "the C² residual IS the polynomial model up to a bounded unit" identification that
   is NOT currently available? Rate difficulty.

4. BOTTOM LINE — is closing these two gates "a mechanical plug + banked machinery"
   (as an optimistic project note claims), or genuine multi-lemma new analytic work?
   If the latter, list the 2-4 named lemmas a next hand must build, shortest first.
</output_contract>

<grounding_rules>
- Distinguish clearly what you can PROVE from what you CONJECTURE. Flag every
  inference as inference.
- If a gate is true only under an extra hypothesis, SAY the exact hypothesis; do
  not hand-wave "generically true".
- Assume the reduced core M'=H-r is nondegenerate (all widths > 0) UNLESS that
  changes your verdict — if it does, say so.
- It is completely acceptable to conclude "this is genuine hard analysis, not a
  plug" — I need the honest verdict, not reassurance.
</grounding_rules>

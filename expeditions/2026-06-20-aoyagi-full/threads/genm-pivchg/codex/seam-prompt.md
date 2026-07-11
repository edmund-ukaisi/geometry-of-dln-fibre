<task>
A finite chart-cover finiteness question ("seam" question) in a resolution-of-singularities / RLCT
computation. Adjudicate whether a divergence can hide at the chart boundaries. Work it out yourself.

SETUP (self-contained; real matrices, unit boxes).
- P is an m1 x mL real matrix (or a product of free matrices, same conclusion asked separately).
- g(P) := ∫_{A0 in [-1,1]^{m0 x m1}} frobSq(A0 · P)^{-c'} dA0, the "front integral" (c'>0).
- Fix corank q. The rank-≥q locus is covered by pivot charts, one per q x q minor B=P[rows,cols]:
  chart_(ρ,κ) = { that minor is invertible }. A refined cover uses the DOMINANT-minor charts
  chart^dom_(ρ,κ) = { |det P[ρ,κ]| ≥ |det P[ρ',κ']| for all other q-minors } (an a.e. partition;
  ties {|det B_i| = |det B_j|} are the "SEAMS", a measure-zero union of hypersurfaces).
- On each chart a block Schur/shear normal form is used to bound the local integral; the assembly is
  ∫_{box} g(P) dP ≤ Σ_charts ∫_{chart} (bound). It is already established (assume) that the per-chart
  BULK bound is finite for c' < ½·minAdm(M) (a coupled, non-factorized estimate).

THE QUESTION: does a divergence hide at the SEAMS? Concretely:
  1. Is g(P) a function of the singular values of P only, or does it depend on which minor is large?
     Is g(P) bounded (O(1)) on the region {σ_q(P) ≥ ε}?  (σ_q = q-th singular value.)
  2. Where do the seams {|det B_i| = |det B_j|} sit relative to {σ_q → 0}? Are they generically at
     σ_q = O(1) (rank exactly q), or do they concentrate on the deeper stratum {rank P ≤ q-1}?
  3. At the deep corner {rank P ≤ q-1} (σ_q→0), do the competing minors |det B_i| vanish at the SAME
     rate, or can one chart's pivot vanish faster (⟹ that chart over-charges)? Express |det B| in
     terms of the singular values of P.
  4. Given a FINITE cover with an a.e. partition into dominant-minor charts, and per-chart bulk
     finiteness, can the subadditive assembly Σ_charts ∫_chart introduce a divergent BOUNDARY term at
     the seams, or is the assembly automatically finite? Is the dominant-minor restriction
     load-bearing, and if so for WHAT (finiteness of the integral, vs conditioning of the shear CoV)?
  5. For a PRODUCT tail P = X1···X_{L-1}: does anything about the seam analysis change (the measure on
     P is the pushforward, not Lebesgue)?
</task>

<output_contract>
Q1–Q5 each: exact statement + one-line reason, marked [exact]/[heuristic]. Then BOTTOM LINE: can a
Beta/boundary divergence hide at the cover seams, yes or no, and what (if anything) the Lean
cover-assembly must ensure (chart definition, per-chart bound form) to be finite. Distinguish
"divergence of the integral" from "divergence of a particular bound".
</output_contract>

<grounding_rules>
- g(P) depends on P only through PP^T (spectrum) — verify and use this.
- σ_q(P) ≍ dist(P, {rank ≤ q-1}); |det B| for a q-minor ≍ product of q singular values along that
  minor's row/col directions.
- A finite sum of finite terms is finite — so identify precisely what could make a per-term integral
  infinite (a non-integrable singularity sitting ON a seam), and whether that occurs.
- Use m0=2, m1=2, mL=3, q=2 as a concrete case if helpful.
</grounding_rules>

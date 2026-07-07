<task>
Adjudicate ONE question about two ways to prove a finiteness result; they may compute the same value by
different routes. Judge independently. I withhold both leanings I have heard.
</task>

<setup>
Goal: finiteness of I = ∫_{box} F^{-c'} for c' < RLCT(F), F = ‖C¹·C²···C^L‖² (product of matrices), at 0.
The singularity is resolved at 0. Two routes to the finiteness:

ROUTE-ATOM: at the top layer, INTEGRATE OUT the corank block Γ of C¹ (a Gaussian-type block integral,
closed form), producing a residual weight det(Q_b Q_bᵀ)^{-p/2}·core^{-(c'-a/2)} where Q_b = (non-pivot
rows of) the downstream product C²···C^L. Then integrate the OUTER integral over the downstream params.
As the downstream product degenerates (rank-drops), det(Q_b Q_bᵀ)^{-p/2} → ∞; the {det=0} locus is
NULL in the downstream params but the pointwise-in-downstream inner integral is non-integrable there, and
the outer integral of the Gram-det weight couples to the core through the shared deeper factors.

ROUTE-BLOWUP: do NOT integrate Γ out. Treat Γ AND all downstream matrix entries as coordinates; blow up
ONE radial coordinate per corank block sequentially (layer by layer, INCLUDING the downstream layers),
reaching a normal-crossing form F = (monomial)²·(unit≥1) on a finite chart cover; then apply the monomial
endpoint (∫∏|y_i|^{α_i}·unit^{-c'} dy < ∞ iff each α_i>-1) on each chart.
</setup>

<facts>
- A scalar caricature of the coupling: F = α² + γ²·(β·s)²  (α = core/pivot, γ = top corank, β·s = a
  degenerate downstream PRODUCT). ROUTE-ATOM integrates γ out: ∫dγ(α²+γ²(βs)²)^{-c'} ∝ |βs|^{-1}·
  α^{-(2c'-1)}; then ∫|βs|^{-1} dβ ds DIVERGES — a coupling "wall". But F = α²+γ²β²s² is a SUM OF MONOMIALS
  whose log-canonical threshold (toric) is finite.
- In a resolution to normal crossing, on each chart one monomial b_j divides all others, so
  ∑ b_i² = b_j²·(1+∑(b_i/b_j)²) = (monomial)²·(unit≥1), and the integral is a finite product of 1-D
  monomial integrals — no coupling remains.
</facts>

<the_questions>
Q1. Is ROUTE-ATOM's Gram-determinant coupling ("wall") a GENUINE obstruction to the finiteness, or an
   ARTIFACT of integrating Γ out at a fixed (degenerating) downstream — i.e. a pointwise-inner-integral
   divergence on a NULL locus that the true (joint) integral does not have? Decide using the caricature
   F = α²+γ²(βs)²: compute its exact RLCT (toric), and compare to ROUTE-ATOM's divergent |βs|^{-1}.
Q2. Does ROUTE-BLOWUP (resolve ALL layers' radials to normal crossing, monomial endpoint at the end)
   AVOID the coupling — i.e. is the outer integral, after full radial resolution, a finite PRODUCT of
   monomial integrals with NO surviving Gram-determinant / no coupling? Or does the downstream product
   structure obstruct reaching normal crossing, so a coupling survives even after full blow-up?
Q3. Do the two routes compute the SAME finiteness threshold (the true RLCT)? If ROUTE-ATOM "walls" while
   ROUTE-BLOWUP is finite for the same c', what exactly is the atom route mishandling?
</the_questions>

<grounding_rules>
- Distinguish PROVE / argue / heuristic. Use the caricature for an exact computation where you can.
- The true RLCT is a well-defined finite number; the question is which route reaches it cleanly.
- Do NOT assume either leaning I have heard.
</grounding_rules>

<output_contract>
1. Q1: genuine-wall | atom-artifact — with the exact RLCT of the caricature and the comparison.
2. Q2: does ROUTE-BLOWUP reach a coupling-free monomial product? Why / why not.
3. Q3: same threshold? what ROUTE-ATOM mishandles if it walls.
</output_contract>

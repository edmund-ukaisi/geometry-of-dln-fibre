<task>
Compass question for a Lean 4 / Mathlib formalisation of a DLN-fibre RLCT integrability sub-result. All integrals are finite-dimensional real Lebesgue integrals. We must prove a PER-CHART integral is FINITE.

On a "dominant-minor" chart, the integrand on the deeper stratum reduces to
    det(Q_b Q_bᵀ)^{-a/2},   Q_b = Y · A_{≥2},
with Y a b×M₂ real matrix (free/integrated) and A_{≥2} an M₂×q real matrix. Concretely b=2, M₂=3, q=4, so A_{≥2} is 3×4 (NON-square, M₂ < q) and the map Y ↦ Y·A_{≥2} sends ℝ^{2×3} → ℝ^{2×4}.

The classical pen-and-paper proof does a change of variables Y ↦ Q = Y·A_{≥2} with Jacobian the corank-Gram weight J = det⁺(A_{≥2}ᵀ A_{≥2})^{-b/2}, i.e. a NON-square coarea CoV. Mathlib v4.29 has the SQUARE linear-map Haar rescaling (map_linearMap_addHaar_eq_smul_addHaar) but NO coarea formula.

An alternative "front-first box bound" was proved on paper: integrating the collapsing direction FIRST keeps it O(1) — e.g. ∫_{-1}^{1} (σ²z²+w)^{-c'} dz → 2·w^{-c'} as σ→0 (NO σ^{-1} blowup). This suggests bounding the integrand pointwise by a coupled majorant σ_q(P)^{-α} with α = max{0, 2c' - m₀(q-1)}, where σ_q(P) is the smallest singular value of the relevant product matrix P, and then integrating that majorant against the rank-tube, whose codimension is D_prod with a tube-volume estimate vol{σ_q(P) ≤ t} ≲ t^{D_prod}.

THE QUESTION (both answers are genuinely open; do NOT anchor to either):
Can the per-chart FINITENESS be obtained WITHOUT the non-square coarea/Gram-Jacobian CoV, by the σ_q-majorant-then-tube-integral route — reducing to an elementary radial/tube integral ∫ σ_q^{-α} over {σ_q small}? OR does obtaining (i) the σ_q-majorant pointwise bound, or (ii) the tube-volume estimate vol{σ_q ≤ t} ≲ t^{D_prod} for a PRODUCT matrix P, STILL require the non-square coarea / Gram-determinant Jacobian (no honest elementary route)?

Be concrete and decisive about the crux: is vol{σ_q(P) ≤ t} ≲ t^{D} for a PRODUCT matrix P itself a coarea/Jacobian fact, or can it be obtained elementarily (e.g. by a polynomial/Cauchy-Binet sublevel bound, a covering argument, or an induction on the number of factors)?
</task>

<output_contract>
1. VERDICT (one line): SIDESTEPS coarea | DOES NOT sidestep (coarea/Jacobian irreducible).
2. The crux argument (<= 12 lines): specifically whether the σ_q-majorant bound and the tube-volume estimate each need coarea, treating the two separately.
3. IF SIDESTEPS: the minimal lemma chain a formaliser would prove — (a) the pointwise majorant lemma (statement), (b) the tube-volume/measure estimate (statement + how obtained elementarily), (c) the radial integrability endpoint (∫_0 t^{D-α-1} dt < ∞ ⟺ α < D). Note which are plausibly in Mathlib.
4. IF DOES NOT sidestep: the SINGLE minimal analytic statement to cite/assume as a named axiom (exact statement), and why nothing weaker suffices.
5. Confidence (0-1) + the one fact that would flip the verdict.
</output_contract>

<grounding_rules>
Distinguish clearly what is a THEOREM you are certain of vs. an INFERENCE/heuristic. If you invoke a Mathlib lemma name, mark it as "believed to exist — verify". Do not fabricate lemma names. The b=2,M₂=3,q=4 numbers are exact; reason about that concrete case first, then say whether it generalizes.
</grounding_rules>

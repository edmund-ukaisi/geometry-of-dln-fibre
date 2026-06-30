<task>
Lean 4 + Mathlib v4.29 formalisation. I am building a smooth chart Φ : ℝ^N → ℝ^N (N = flatDim, a Fintype index Fin N) for a deep-linear-network loss, to feed an IFT chart-transfer. I have, ALREADY PROVEN sorry-free:

- jacFlatL2 : Matrix (Fin H0 × Fin H2) (Fin N) ℝ — the flat Jacobian of the loss entries g_ij; row (i,j) is ∇g_ij(0).
- exists_jacFlatL2_minor: ∃ er : Fin nReg → Fin H0 × Fin H2, ec : Fin nReg → Fin N, both injective, det (jacFlatL2.submatrix er ec) ≠ 0.  (nReg = r(H0+H2−r).)
- jacFlatL2_apply_eq_lossEntryDeriv: jacFlatL2 (i,j) c = (the analytic strict-derivative functional prodAuxEntryDeriv … 2 i j) (Pi.single c 1) — i.e. the entry IS ∇g_ij(0) evaluated on the c-th basis tangent.
- I have hasStrictFDerivAt_lossEntry: HasStrictFDerivAt (fun w => (prod(gmapAt v w) − B) i j) (prodAuxEntryDeriv … 2 i j) w₀ — the per-loss-entry gradient as a CLM (Fin N → ℝ) →L[ℝ] ℝ, at any w₀.
- lossFlatShift v = fun w => dlnLoss B (gmapAt v w) = ∑_ij (g_ij(w))², C^∞, with g_ij(0)=0 at the optimal v.

I want to CONSTRUCT, with the EXISTENTIALLY-CHOSEN ec (the minor's columns), NEVER a fixed coordinate complement:
  Φ(w) c = if c ∈ Set.range ec then (g_{er k}(w) − g_{er k}(0))  [k the unique index with ec k = c]  else w c
and produce:
  (a) f' : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) with HasFDerivAt Φ (f' : _ →L _) 0, via ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero applied to DΦ(0), using det DΦ(0) ≠ 0;
  (b) det DΦ(0) ≠ 0 via Matrix.twoBlockTriangular_det with predicate p c := c ∈ range ec (the complement rows are e_c, so M i j = 0 when ¬p i ∧ p j), reducing to det(selected block)·det(identity block) = ±det(minor)·1;
  (c) ContDiff ℝ 2 Φ (each component is either a coordinate w↦w c or an entrywise polynomial g_{er k} − const);
  (d) Φ 0 = 0 (g_ij(0)=0).

Known traps: Params is NOT normed (work entrywise into ℝ); the if c ∈ range ec branch needs the unique-index extraction; DΦ(0) as a CLM must have its ContinuousLinearMap.det tie to the matrix det.
</task>

<output_contract>
Concrete and Lean-flavoured (mention exact Mathlib v4.29 lemma names where you can). Sections:
1. The cleanest way to DEFINE Φ avoiding the awkward "unique k with ec k = c" dependent extraction — is there a slicker formulation (e.g. sum over k of indicator, or define the selected-output map via ec and the complement via id, then glue)? Rank the 2-3 options.
2. The cleanest fderiv route: how to get HasFDerivAt Φ M' 0 where M' is the CLM of DΦ(0), given I have per-entry HasStrictFDerivAt for the g's and the identity for the w-coords. Which Mathlib combinator assembles a Pi-valued fderiv from per-coordinate fderivs (hasFDerivAt_pi / HasFDerivAt.pi)? 
3. The det≠0: the exact chain from twoBlockTriangular_det to ±det(minor)≠0, and how ContinuousLinearMap.det of the assembled M' ties to the Matrix.det (LinearMap.det_toContinuousLinearMap? ContinuousLinearMap.det? Matrix.det of toLin'?). Flag the most likely friction.
4. Biggest risk / where to put the 3-attempt-then-surface watch.
</output_contract>

<grounding_rules>
Flag any lemma name you are not sure exists in v4.29 as "verify". Distinguish a clean known path from a guess.
</grounding_rules>

<task>
Lean 4 + Mathlib v4.29 formalisation. I must prove, sorry-free, a determinantal
integrability bound (the "Category I good-stratum" obligation of a DLN/RLCT project):

  GOAL:  ∫⁻_{Q ∈ box} ENNReal.ofReal (det (Q * Qᵀ) ^ (-a/2))  < ⊤
         for a real `a` with `a < q - b + 1`,
         where Q : Matrix (Fin b) (Fin q) ℝ,  b ≤ q,
         and `box` is a bounded measurable set (a product cube: each entry in [-T,T]);
         `^` is Real.rpow; the integral is Lebesgue `∫⁻` (ENNReal) over the matrix
         entries (volume on Matrix (Fin b)(Fin q) ℝ ≅ (Fin b → Fin q → ℝ)).

The result is mathematically certain (Gram–Schur / SVD: det(QQᵀ) ≍ ‖residual‖²,
threshold a < q−b+1, sharp). I need the CHEAPEST-in-Lean route to a sorry-free proof.

ALREADY LANDED (sorry-free, axiom-clean):
  integrableOn_norm_rpow_neg_ball {n} (hn : 1 ≤ n) {a} (ha : a < n) (R) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖ ^ (-a)) (Metric.ball 0 R)
  (via MeasureTheory.integrable_fun_norm_addHaar coarea + intervalIntegral.integrableOn_Ioo_rpow_iff)
  and its ∫⁻ corollary  ∫⁻ x in ball 0 R, ofReal(‖x‖^(-a)) < ⊤.

PLANNED ROUTE (row-residual recursion, ∫⁻ / Tonelli throughout so no integrability side goals):
  Split Q rows = (Q' ; w), Q' = first b−1 rows, w = last row ∈ ℝ^q.
  P3 (Gram–Schur det recursion): if G' := Q'Q'ᵀ invertible then
       det(QQᵀ) = det(G') · S(w),  S(w) := ‖w‖² − (Q'w)ᵀ G'⁻¹ (Q'w)
       and S(w) = dist(w, rowspan Q')² = ‖P_{V⊥} w‖², V = rowspan Q', dim V ≤ b−1.
  P2 (uniform radial bound): ∫⁻_{w∈cube_q} ofReal(S(w)^(−a/2)) ≤ C, C finite (a<q−b+1),
       via S(w)=‖P_{V⊥}w‖² ≥ ‖P_W w‖² for W⊆V⊥, dimW = q−b+1, then reduce to my landed radial lemma.
  P4 (Tonelli): F(Q') := ∫⁻_w ofReal(det(QQᵀ)^(−a/2)); show F(Q') ≤ ofReal(det(G')^(−a/2))·C
       (det(G')=0 case gives det(QQᵀ)=0 so F=0); then ∫⁻_{Q'} F ≤ C·∫⁻_{Q'} ofReal(det(G')^(−a/2)),
       recurse on b (base b=1: det=‖row‖², my radial lemma with n=q).

WHAT MATHLIB HAS (confirmed): Matrix.det_fromBlocks₁₁ (Schur, det A * det(D − C⅟A B), [Invertible A]);
  Matrix.gram / posDef_gram_iff_linearIndependent / posSemidef_gram; Submodule.orthogonalProjection
  + orthogonalProjectionFn_norm_sq (‖v‖² = ‖proj‖² + ‖v−proj‖²); gramSchmidt / gramSchmidtOrthonormalBasis_det;
  EuclideanSpace volume + measurePreserving_measurableEquiv (Euclidean↔Pi); volume_preserving of linear isometry.
  NOT found: packaged Gram-det=distance formula; Cauchy–Binet; rank-normal-form / "M projection ⇒ diagonalizable by orthogonal CoV".
</task>

<output_contract>
Be concrete and Lean-tactic-level. Sections, in order:

1. ROUTE VERDICT: Is the row-residual Schur recursion the cheapest sorry-free route, or is
   there a materially cheaper one (e.g. gramSchmidt-based det=∏‖g_i‖² avoiding det_fromBlocks₁₁,
   or an SVD/orthogonal-CoV global argument)? Pick ONE and justify in ≤6 lines.

2. P3 (det recursion) — the single hardest sub-step is identifying the Schur scalar
   S(w) = ‖w‖² − (Q'w)ᵀG'⁻¹(Q'w) with ‖P_{V⊥}w‖². Give the CLEANEST Lean path:
   (a) do it via Matrix (projection matrix M = I − Q'ᵀG'⁻¹Q', show M²=M, Mᵀ=M, S(w)=wᵀMw=‖Mw‖²), or
   (b) via Mathlib Submodule.orthogonalProjection + gram, or
   (c) avoid the identity entirely (only need a LOWER bound S(w) ≥ ‖P_W w‖² for integrability — is
       there a variational/Rayleigh route that skips G'⁻¹?). Name the specific Mathlib lemmas.

3. P2 (uniform projection radial bound): cleanest Lean route to
   ∫⁻_{cube} ofReal(‖P w‖^(−a)) ≤ C (finite, a<r) for P an orthogonal projection of rank r,
   UNIFORM over P. Must the orthogonal change-of-variables be a measurable family (bad), or can
   I get a uniform bound via a single fixed coordinate subspace + monotonicity ‖P_{V⊥}w‖≥‖P_W w‖
   and reduce to my landed radial lemma? Give the measure-preserving-CoV lemma names.

4. RISK RANKING: rank P2/P3/P4 by Lean-friction/wall-risk; for the riskiest, the single
   fallback that still yields a sorry-free (possibly weaker-but-sufficient, a<q−b+1) result.

5. SCOPE CALL: is this realistically ONE tide (~few hundred lines) or should P2 and P3 be
   separate bricks? If the latter, the minimal clean interface between them.
</output_contract>

<grounding_rules>
Flag any Mathlib lemma name you are not sure exists in v4.29 as "VERIFY" — I will grep before use.
Distinguish "standard, definitely in Mathlib" from "likely needs a local build". Do not invent
lemma signatures; if unsure of the exact name, describe the statement so I can search.
</grounding_rules>

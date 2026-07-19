<task>
Decorrelated fidelity check on a change-of-variables in a resolution construction (Aoyagi 2023,
"learning efficiency of deep linear networks", Section 5, pp.16-21). Reason from the transcription;
exact algebra. Do NOT look anything up.

SETUP. At a node the paper applies, to the factored product `diag(b) · D_J · C^{(S+1)}` (after a monomial
blow-up factors a scalar u), TWO regular (unipotent) matrices and one matrix-relabel:
  * Q — UPPER-unipotent, its only non-identity entries are in ROW 1: Q = I with Q_{1,j} = -d'_{J+1,j}
    (j>1) [entries are residual VARIABLES]. It acts on the D-block by RIGHT multiplication: D'' = D' Q,
    and simultaneously on the NEXT-layer matrix by LEFT multiplication of the inverse: C'^{(S+1)} =
    Q^{-1} C^{(S+1)}.  (So Q Q^{-1} is "inserted" between D and C^{(S+1)} — ideal-preserving.)
  * P — LOWER-unipotent, its only non-identity entries are in COLUMN 1: P = I with
    P_{i,1} = -(b'_i/b'_{J+1}) d''_{i,J+1} (i>1) [entries are VARIABLES / monomial ratios]. It acts by
    LEFT multiplication: P · diag(b') · D'' = diag(b') · D'''  with  D''' = [[1,0],[0, D_{J+1}]].
  * the corner entry (J+1,J+1) is normalized to a unit (divide by it).
The net effect is a coordinate change-of-variables ("the gauge ψ") on the residual/next-layer
coordinates, composed after the monomial blow-up β; per-leaf chartMap = ψ ∘ β. Q is a single elementary
COLUMN-shear (rank-1, clears row 1 via column ops); P is a single elementary ROW-shear (rank-1, clears
column 1 via row ops); P is applied AFTER Q and its entries depend on D'' (= Q's output).

THE QUESTION (Q1b). The downstream coverage lane wants to fill each node's chart-slot with the gauge.
Can the per-node gauge be faithfully represented as a SINGLE variable-dependent shear ψ (one elementary
transvection / one triangular unipotent substitution), or does it IRREDUCIBLY require a COMPOSITION of
≥2 shears (a column-shear then a row-shear, in different directions)?

Concretely, please:
Q1. For a minimal non-trivial residual block (2x2, and 3x3), write Q and P explicitly, form the
    coordinate CoV (old residual/next-layer coords -> new), and determine: is the composite a SINGLE
    elementary shear (I + rank-1 nilpotent; equivalently triangular in ONE variable ordering), or the
    product P·(...)·Q of two shears in different directions that does NOT collapse to one elementary
    shear? Give the composite matrix / substitution explicitly and its determinant.
Q2. Is the composite unipotent (all eigenvalues 1)? Recall the product of an upper- and a lower-unipotent
    is generally NOT unipotent. State whether the per-node gauge is (a) a single elementary shear, (b) a
    single unipotent map, (c) a single unimodular (det = unit) map that is NOT unipotent, or (d) only
    representable as a composition. Pick the SHARPEST true classification.
Q3. Does the answer change the chart-slot design: must the slot hold a COMPOSITION (ordered pair of
    shears), or does a single (general variable-dependent unimodular) map suffice? Distinguish "one MAP"
    (a composition is still one function) from "one elementary SHEAR".
</task>

<output_contract>
Q1: explicit Q, P, the composite CoV + determinant, for 2x2 (and note 3x3). Q2: the sharpest
classification (a)/(b)/(c)/(d) with the eigenvalue/unipotency check. Q3: chart-slot verdict —
"single elementary shear SUFFICES" or "COMPOSITION required" or "single general unimodular map suffices
(but not a single elementary shear)". End with a one-line verdict. Then 3 lines MOST LIKELY WRONG.
Exact; flag inference vs computation.
</output_contract>

<grounding_rules>
Reason only from the transcription + exact linear algebra. Flag INFER vs COMPUTE. If a detail (e.g. the
exact P-entry ratios, or whether Q and P act on disjoint coordinate blocks) is ambiguous, state your
reading. Do not assume the single-shear form is faithful — actively check whether P∘Q collapses.
</grounding_rules>

<task>
I am elaborating the recursive blow-up in Miki Aoyagi (2023), "Consideration on the learning
efficiency of multiple-layered neural networks with linear units" (pp.14-22), into a fully worked
template a formaliser can render definitions from without guessing. I need an INDEPENDENT reading of
three ambiguous points in her displays. Do NOT rederive the whole proof; adjudicate the readings.

SETUP (her notation). L matrices C^(1),...,C^(L), C^(s) of size M^(s) x M^(s+1). M(S)=min{M^(s):1<=s<=S}.
The inductive invariant (p.15) is:
  < prod_{s=1}^L C^(s) > = < diag(b_1,...,b_{M(S)}) [[E_J, O],[O, D_J]] prod_{s=S+1}^L C^(s) >
with D_J of size (M(S)-J) x (M^(S+1)-J), and b_0=1, b_i = (prod_{tilde t_{s,k}=i-1} u_{s,k}) b_{i-1}.
The paper says "The above is obvious for S=0 and J=0."

THE THREE POINTS (verbatim structure from the displays):

(1) START CONVENTION. At S=0, J=0 the invariant should reduce to the tautology
    < prod C^(s) > = < prod C^(s) >. What are diag(b_1,...,b_{M(0)}), E_J, D_0 at S=0,J=0 concretely
    (sizes and contents), so that the RHS literally equals the LHS? In particular: is M(0) defined,
    what is D_0 (identity? the first factor C^(1)? the whole product?), and does the FIRST genuine
    blow-up step act on C^(1) as D_0, or on something else? Give the concrete matrices.

(2) CASE 1(2) vs CASE 2, the b'-update range. In Case 1 the equal run is b_{J+1}=...=b_{J+J_1} with
    b_{J+J_1+1} != b_{J+J_1} (J_1 < M(S)-J, a PARTIAL block). The blow-up center (p.16) is
    { d_ij=0 (i=J+1..J+J_1, j=J+1..M^(S+1)), u_{s,k}=0 }. In the Case 1(1) chart (p.16) the b-update is
    ONLY  b'_{J+1}=u_{s,k}b_{J+1}, ..., b'_{J+J_1}=u_{s,k}b_{J+J_1}   (the PARTIAL block J+1..J+J_1).
    But in the Case 1(2) chart (p.17) the b-update is
    b'_{J+1}=u_{S,J+1}b_{J+1}, ..., b'_{M(S)}=u_{S,J+1}b_{M(S)}       (the WHOLE tail J+1..M(S)).
    Why does Case 1(2) multiply the WHOLE tail b_{J+1..M(S)} by the new coordinate u_{S,J+1}, while
    Case 1(1) touches only the partial block b_{J+1..J+J_1}? What is the mechanism (in terms of the
    substitution u_{s,k}=u_{S,J+1} u'_{s,k} and d_ij=u_{S,J+1} d'_ij) that makes the tail rows
    beyond J+J_1 also acquire the factor u_{S,J+1}?

(3) THE Q AND P CLEARING. On pp.17-21, after the blow-up chart normalizes the pivot d'_{J+1,J+1}=1,
    two regular matrices are applied:
      Q (p.17): first row (1, -d'_{J+1,J+2}, ..., -d'_{J+1,M^(S+1)}), identity below. Applied so that
                D''_J = D'_matrix . Q, AND the next-layer matrix is recoordinatized C'^(S+1)_J = Q^{-1} C^(S+1)_J.
      P (p.18): lower-triangular, first-column entries -(b'_i/b'_{J+1}) d''_{i,J+1}, identity elsewhere.
    The net effect claimed: P diag(b') D''_J C'^(S+1)_J = diag(b') D'''_J C'^(S+1)_J with
    D'''_J = [[1,O],[O, D_{J+1}]].
    Question: describe EXACTLY which coordinates the Q-step and the P-step READ and which they WRITE.
    Specifically: (a) does the residual block D_{J+1} equal the Schur complement of the pivot, and if
    so with respect to which pivot and which sub-block? (b) The recoordinatization C^(S+1) -> Q^{-1}C^(S+1)
    -- does it change the deeper layers C^(S+2),...,C^(L), or only C^(S+1)? (c) Is the b'-ratio
    b'_i/b'_{J+1} a genuine polynomial (so P is regular), and what property of the b-sequence guarantees it?
</task>

<output_contract>
Three numbered sections (1),(2),(3), each <= 200 words. For each: give the concrete reading (matrices/
sizes/index sets), then one line "CONFIDENCE: high|medium|low" + the single strongest reason. If a point
is genuinely ambiguous in the paper (multiple consistent readings), say so and give both. End with a
1-line "SHARPEST DISAGREEMENT-RISK" naming the single reading most likely to be mis-transcribed.
</output_contract>

<grounding_rules>
Reason from the displayed structure only; you do not have the PDF, so treat my transcription of the
displays as the ground truth and reason about their internal consistency. Flag any place where my
transcription would be internally inconsistent (that is itself the finding). Distinguish "the paper
forces this" (fact) from "the natural reading is" (inference). Do not invent notation not above.
</grounding_rules>

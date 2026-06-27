<task>
I am adjudicating a determinant problem in a formalisation of an algebraic-geometry resolution chart.
Help me by independently working the exact algebra and the design choice; do NOT rubber-stamp.

SETTING. For a deep linear network with width vector M=(M_0,...,M_L), the loss is F(A) = ||A_0 A_1 ... A_{L-1}||^2
(Frobenius squared of a product of matrices A_k : M_k x M_{k+1}). The parameter space has dimension N = sum_k M_k M_{k+1}.
An "achiever" resolution chart is a map phi : R^N -> R^N (flat coords) such that, off the pivot hyperplane {x_p=0}:
  (RATE)  F(phi(x)) = (x_p)^2 * U(x)      [U a unit, positive a.e., x_p = the radial pivot coordinate]
  (DET)   |det D phi(x)| = |x_p|^{m-1} * (spectator monomials)
where m = the codimension of the achiever center being resolved (call it minAdm), and m >= 1.

CONCRETE TEMPLATE that WORKS (validated): for M=(4,4,2,2), minAdm=m=4. The chart is a PURE radial blow-up:
  A_2 (the deepest 2x2 factor) = x_p * [[1, x_1],[x_2, x_3]]   (the (0,0) entry is a FIXED 1 scaled by x_p)
  A_0, A_1 = free spectator coords (identity in the flat map).
Then F(phi) = (x_p)^2 * U (since A_0 A_1 A_2 = x_p * (A_0 A_1 Mbar), one power of x_p), and
|det Dphi| = |x_p|^{m-1} = |x_p|^3. The blow-up is "pivotBlowupOn active p": coord p -> x_p (identity),
each active coord j != p -> x_p * x_j, spectators -> x_j. Its Jacobian det = (x_p)^{|active|-1}, and here
|active| = m = 4, the (0,0) FIXED-1 slot being one of the active coords. KEY: the pivot scales a FIXED residual
entry equal to 1, and there are exactly m active coords (m-1 free + the pivot), giving det = x_p^{m-1}.

THE PROBLEM CHART (general, layered case). A "structured decoder" builds the layered product via a chain
recursion. It reads N free coords from a flat vector x via disjoint role-slots (Schur-frame entries K,X,N,E
per layer + lift W), assembles block matrices, and forms A_k by a chaining recursion
  C_{k+1} = [[K, K N],[X K, X K N + u E]]  (the Schur frame; u = x_p the radial scalar)
  A_k = chainA(N_k, W_k, C_{k+1}).
The pivot is defined as flat coordinate 0 (structPivot := <0>). The radial scalar u = x_0 enters ONLY linearly
as "u * E" across the residual E-blocks. The leaf residual is set to ZERO (Rfin := 0). There is NO designated
pivot slot that scales a FIXED 1-entry; the pivot x_0 is just whatever role-coordinate happens to live at flat
index 0.

QUESTIONS (work the exact algebra yourself):
1. For the layered case, does the rate F(phi) = (x_p)^2 * U survive when u enters via "u*E" in the interior
   Schur frame rather than via a leaf "u*Rfin"? (The chain telescopes the product to u*H for a u-free H.)
2. The determinant: with u = x_0 playing DOUBLE DUTY (the scalar u multiplying E AND a flat coordinate feeding
   a role-slot), and with the leaf residual Rfin=0 meaning some input coords feed UNUSED block slots, what is
   |det Dphi|? Is it |x_p|^{m} (off by one), or is it identically 0 (degenerate, rank-deficient), or something
   else? Reason about the rank of the Jacobian R^N -> R^N when some input coords map to nothing in the output
   and the pivot does not scale a fixed-1 slot.
3. The design fix: which is correct/cleanest?
   (A) Redefine the decoder to add a designated pivot slot scaling a FIXED-1 residual entry + nonzero leaf Rfin,
       so the m actives are (pivot, m-1 free), net radial det = |x_p|^{m-1}.
   (B) Keep the layer-structure decoder UNTOUCHED for the rate, and supply the |x_p|^{m-1} blow-up via a SEPARATE
       radial factor (pivotBlowupOn) composed in (phi = Q_linear ∘ radial), as the (4,4,2,2) template does
       (it is literally composeFold [linearFactor Q, radialFactor active p]). Where does the (x_p)^2 in the rate
       then come from -- the radial factor or the layer structure? Can the rate stay (x_p)^2?
   (C) something else.
   Weigh: which keeps a SINGLE chart phi with BOTH rate and det, minimal blast radius, and is the (4,4,2,2)
   template generalizable to the layered (nontrivial Schur/LDU) case?
4. SANITY on the validate-small case: M=(2,2,2). The Aoyagi codim recursion is
   minAdm(M_0,...,M_L) = min_t [ (M_0-t)(M_1-t) + minAdm(t, M_2, ..., M_L) ]  (peeling the first two layers to
   rank t), base minAdm(a,b)=a*b. Compute minAdm(2,2,2). Separately, a candidate chain descent path has ranks
   Text=[2,2,1,1] (rank stays 2 after layer 0, drops to 1 after layer 1); its per-boundary "chain codim" is
   sum_k (Text_k - Text_{k+1})(M_k - Text_{k+1}). Compute that. Do they agree? If not, what does the disagreement
   mean for using Text=[2,2,1,1] as a "validate-small" test of the DET = |x_p|^{minAdm-1} identity?
</task>

<output_contract>
- For each question, show the exact algebra / computation, then a one-line verdict.
- For Q2 give the determinant value with reasoning about Jacobian rank.
- For Q3 give a single recommendation (A/B/C) with the why.
- For Q4 give both numbers and state whether the test case is valid for the DET identity.
- Distinguish FACT (you computed it) from INFERENCE (you reason it likely).
</output_contract>

<grounding_rules>
- Work the matrix algebra concretely; do not hand-wave the determinant.
- The (4,4,2,2) template is FACT (validated). Use it as the reference for "what correct looks like".
- Do not assume the structured decoder is correct; it may be degenerate.
</grounding_rules>

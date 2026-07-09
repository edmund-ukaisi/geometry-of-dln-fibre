Decorrelated second opinion on a formalisation-scoping question. Be independent; do not defer.

SETTING. Aoyagi (2023/2024, "Consideration of learning efficiency of deep linear networks", Neural Networks) computes the exact real-log-canonical-threshold (learning coefficient) of the deep linear network square loss. The singular object, after his Theorem 4 reduces to the deepest singular point (all layer ranks r(s)=r), is the log-canonical threshold of

   || prod_{s=1}^{L} C^{(s)} ||^2 ,   C^{(s)} an M^{(s)} x M^{(s+1)} matrix of variables,  M^{(s)} = H^{(s)} - r.

He proves the value (his Theorem 2) by an EXPLICIT RECURSIVE BLOW-UP. Key structure I have read directly from the paper:
- The recursion carries the invariant  < prod_{s=1}^L C^{(s)} > = < diag(b_1,...,b_{M(S)}) * [E_J | O ; O | D_J] * prod_{s>S} C^{(s)} > , where M(S) = min{ M^{(s)} : 1 <= s <= S } is the RUNNING-MINIMUM corank, J a within-layer counter, and the b_i accumulate the blow-up variables u_{s,k}.
- Two branches, Case 1 and Case 2, each construct the blow-up along a COORDINATE submanifold: { d_{ij} = 0 (block), u_{s,k} = 0 }. The u_{s,k} are shared across generators and tracked in the b_i diagonal (a "shared-divisor ledger").
- The induction terminates and yields a normal-crossing resolution; the LCT is read off the monomial exponents. Proof stated complete ("End of Proof").

THE QUESTION. A Lean formalisation project reduced its remaining gap to a DIFFERENT-looking object: it front-peels one boundary matrix (Schur complement + a measure-preserving shear), then INTEGRATES OUT the freed block Gamma via a Gram change of variables Gamma -> Gamma * Q_b, which manufactures a factor det(Q_b Q_b^T)^{-(M_0-t)/2} where Q_b is rows of the matrix PRODUCT A_1*A_2*...  . That factor blows up on the product's rank-drop locus, and at a binding case (widths (3,3,3,4)) it sits EXACTLY at its integrability threshold with zero slack, apparently forcing a "joint principalisation of the product's determinantal locus" that needs a NON-coordinate blow-up center (a dense-torus witness [[1,1,2,1],[1,1,2,1]] invisible to coordinate centers). This was flagged as a possible genuine wall / Mathlib-missing resolution-of-singularities.

I want your independent read on THESE claims:

1. Is the det(Q_b Q_b^T) coupling / zero-slack borderline an INTRINSIC feature of the DLN RLCT at the sub-generic (product-rank-deficient intermediate) strata, OR is it an ARTIFACT of the specific "integrate-out-Gamma via Gram CoV" peel — i.e. does Aoyagi's NATIVE recursion (blow up the whole product prod C^{(s)} directly along coordinate centers, tracking the running-min M(S) in diag(b)) simply never form that determinant?

2. Aoyagi's published centers are COORDINATE submanifolds and his proof is complete. If that is correct, does the "non-coordinate center forced by a dense-torus witness" claim survive? (Note: the witness is a POSITIVE-loss point, i.e. off the zero locus {prod C = 0} that the deepest-point resolution actually resolves.) Reconcile: how can coordinate centers suffice (Aoyagi) if a dense-torus rank-drop point needs a non-coordinate center?

3. Given Aoyagi's recursion is coordinate-center-based and covers product-rank-deficient intermediates via the running-min M(S), classify the Lean gap: (a) formalise Aoyagi's explicit coordinate-chart recursion (large-but-bounded, cite only a monomial-integrability endpoint), (b) a bounded analytic build with some new lemma, or (c) a genuine wall needing Mathlib-missing res-of-singularities. 

4. If (a): what is the DOMINANT formalisation difficulty — is it (i) the carrier data structure (the diag(b) shared-divisor ledger + the [E_J|D_J] block invariant preserved across (S,J)->(S,J+1) and S->S+1), (ii) the chart algebra, or (iii) termination/covering? Rough size tier (person-weeks) and top risk.

Be concrete. The decision is build-Aoyagi-native vs cite-Aoyagi. Calibration over optimism.

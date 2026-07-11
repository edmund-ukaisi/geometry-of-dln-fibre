<task>
Adjudicate a convergence question about a determinant-power ("pivot charge") integral and a
proposed dyadic-shell summation. This arises in a resolution-of-singularities / RLCT computation
for products of matrices. Work it out yourself from scratch; give exact exponents.

SETUP (self-contained). Real matrices, all integrals over the unit box (entries in [-1,1]).
- A tail matrix P (size m1 x mL) and a front matrix A0 (size m0 x m1). The object of interest is
    J = ∫_{A0 box} ∫_{P box} frobSq(A0 · P)^{-c'} dP dA0,
  where frobSq(X) = sum of squares of entries, and c' > 0 is an exponent parameter. (In the
  application P is itself a product of L-1 free matrices, but for THIS question treat P as free /
  or as a single free matrix — analyze the single-matrix case m1 x mL first, then comment on
  whether a product tail changes the answer.)
- Fix a corank q (1 ≤ q ≤ min(m1,mL)). On the pivot chart where a fixed q x q minor B = P[rows,cols]
  is invertible, a block Schur/shear normal form gives, EXACTLY (verify this yourself):
    frobSq(A0 · P) = ‖R̃ · α‖² + ‖R̃ · Bmat + S̃ · Z‖²,
  where α (q x q) is the pivot block (det α = det of the q-minor), R̃ (m0 x q), S̃ (m0 x (m1-q))
  are column blocks of the sheared A0, and Z is the Schur complement (the "reduced" block).
- To "clean" the loss to ‖R‖² one sets R = R̃·α, which introduces a Jacobian |det α|^{-m0} — a
  DETERMINANT INVERSE (a "pivot charge").

PROPOSED MECHANISM to prove J < ∞ (this is the thing to adjudicate — do NOT assume it works):
  decompose the α-domain into disjoint dyadic shells  Shell_k = { 2^{-k-1} ≤ |det α| < 2^{-k} },
  bound J on each shell, and sum:  J ≲ Σ_k [vol(Shell_k)] · [charge on shell k] · [rest on shell k].

QUESTIONS (answer each with an exact exponent / condition):
  1. Compute vol{ α (q x q) in box : |det α| ≤ t } as t→0 (leading power of t, and any log power).
  2. For what s does ∫_{box} |det α|^{-s} d(entries) converge? Hence: is the raw charge
     |det α|^{-m0} integrable on its own for m0 ≥ 1?
  3. If one bounds "rest on shell k" by a shift-INDEPENDENT constant and "charge on shell k" by
     |det α|^{-m0} ~ 2^{k m0}, does the shell sum Σ_k vol(Shell_k)·2^{k m0}·const converge? Give the
     tail term_k and the verdict. If it diverges, WHERE (which locus in P-space) does the divergence
     sit, and is it a divergence of the TRUE integral J or an artifact of the bound?
  4. Does the coupling save it? On Shell_k the Schur complement Z ~ α^{-1} blows up like 2^k, so the
     "rest" (an integral of ‖(front)·Z‖^{-2s}) decays. Can you rescue convergence by a FACTORIZED
     per-shell bound [∫ charge]·[∫ rest], or does the charge×rest coupling resist factorization?
     (Consider: is ∫_{box} |det α|^{-m0}·(anything shift-independent) ever finite for m0 large?)
  5. What is the ACTUAL small-parameter that controls J near the deeper stratum {rank P ≤ q-1}?
     Compute the scaling of  g(P) := ∫_{A0 box} frobSq(A0·P)^{-c'} dA0  as P approaches
     {rank P = q-1} (let σ = the q-th singular value of P → 0). Is there a |det α|^{-m0}-type or
     σ^{-m0}-type blow-up, or is it milder? Give the exponent of σ. Then state the condition on c'
     under which ∫_P g(P) dP converges near {rank P ≤ q-1} (in terms of the codimension D of that
     stratum). Compare that threshold to the dyadic-shell verdict of Q3.
</task>

<output_contract>
For each of Q1–Q5: an exact exponent or convergence condition, with the one-line derivation. Then a
BOTTOM LINE: does the proposed dyadic-|det α|-shell mechanism (as literally stated in Q3) prove
J < ∞, or not? If not, what is the correct finiteness mechanism and its exact threshold? Distinguish
"the bound diverges" from "the integral J diverges". Mark each claim [exact] / [heuristic].
</output_contract>

<grounding_rules>
- Real exact algebra: determinant sublevel-set volumes, Beta-type radial integrals, tube/codim
  estimates. State the radial integral you use.
- Do not assume the shell mechanism works; test it adversarially. It may hide a divergence.
- Keep the levels separate: a codimension/budget bound is NOT a convergence proof.
- If you need a concrete case, use m0=2, q=2, single-matrix tail (m1=mL=2), and general.
</grounding_rules>

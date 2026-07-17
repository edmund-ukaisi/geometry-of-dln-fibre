<task>
I need a rigorous, independent adjudication of a single measure-theory / RLCT (real log-canonical threshold) integrability statement, and a soundness check of a proposed proof route. Please recompute from scratch; do not defer to my framing.

THE STATEMENT (to prove or refute, and to characterise the exact hypotheses):
Let a,b,q be positive integers with min(a,b) >= 2. Let S be a FIXED real b x q matrix, with r := rank(S). Let c' >= 0 be a real number. Let Gamma range over real a x b matrices. Consider
    I(box) = integral over Gamma in `box` of  ( frobSq(Gamma * S) )^(-c')  dGamma,
where frobSq(A) = sum of squares of all entries of A (Frobenius norm squared), and `box` is a subset of the a*b-dimensional space of a x b matrices.

Q1. Under the hypothesis "2*c' < a*r" (strict), is I(box) finite? Characterise EXACTLY what regularity `box` must satisfy for finiteness to hold: is "Lebesgue-volume(box) < infinity" sufficient, or is a stronger condition (e.g. box bounded / contained in a ball) required? If finite-volume is NOT sufficient, give an explicit counterexample with min(a,b) >= 2.

Q2. Is the number "a*r" (= a*rank(S)) the correct/tight critical count, i.e. is the threshold exactly c' < a*r/2? Is it tight (does the integral diverge at c' = a*r/2 for a genuine bounded box that meets the singular locus)?

Q3. PROOF-ROUTE SOUNDNESS. Consider this proposed route for the finite-radius / bounded box case:
   (i) rewrite frobSq(Gamma*S) = sum_i (row_i of Gamma) * (S S^T) * (row_i of Gamma)^T, i.e. a quadratic form in the entries of Gamma with matrix built from the b x b Gram G = S S^T;
   (ii) spectrally diagonalise the FIXED Gram G = U D U^T (U orthogonal, D = diag(sigma_1^2,...,sigma_r^2,0,...,0));
   (iii) apply the orthogonal change of variables Gamma -> Gamma U (Jacobian determinant magnitude 1), turning the integrand into ( sum_{i=1..a} sum_{j=1..r} sigma_j^2 * y_{ij}^2 )^(-c'), a positive-definite quadratic form in the n := a*r "active" variables y_{ij} (j<=r); the remaining a*(b-r) variables do not appear;
   (iv) bound box by a bounded rectangle, split active (n=a*r vars) x free (a*(b-r) vars); integrate the free vars (bounded => finite factor); apply a standard radial/polar "reciprocal power of a positive-definite quadratic form over a cube/ball is integrable iff c' < n/2" lemma on the active block.
   Is this route CORRECT and COMPLETE for the bounded-box case? Does it genuinely resolve the singularity, or does it silently miss part of the singular locus?

Q4. There is a competing claim in my project's design notes that this kind of "corank block" integrand for min(a,b) >= 2 CANNOT be resolved by "a single radial coordinate" and instead REQUIRES a full determinantal / multi-singular-value blow-up ("d = c exceptional coordinates"), because "a single radial coordinate resolves only Gamma = 0, not the rank-1..c-1 cone". Is that objection VALID for the statement above (S FIXED, only Gamma integrated)? Or does that objection apply to a DIFFERENT problem (e.g. where S also varies / is itself a matrix product, so the joint incidence {Gamma*S = 0} becomes a determinantal variety)? Be precise about which problem needs the determinantal blow-up and which is a plain Morse-type (smooth-center) computation.
</task>

<output_contract>
- Lead with a one-line verdict on Q1 (finite-volume sufficient? Y/N) and Q3 (route sound & complete? Y/N).
- Q1: exact regularity condition on box; explicit counterexample if finite-volume insufficient.
- Q2: threshold value + tightness (yes/no + reason).
- Q3: correct/complete? name any gap.
- Q4: which problem needs the determinantal blow-up; is the objection valid for FIXED S.
- Keep facts and inferences distinct. Show the key computation for the counterexample and the threshold.
</output_contract>

<grounding_rules>
- The setting is real-field RLCT / Lebesgue integrability, elementary real analysis + linear algebra. No RLCT black-box theorem needed; argue from first principles (change of variables, polar coordinates, Fubini/Tonelli).
- frobSq(Gamma*S) as a function of Gamma is a homogeneous degree-2 polynomial (a quadratic form). Its zero locus in Gamma-space (S fixed) is exactly {Gamma : Gamma*S = 0}.
- "rank(S)" means ordinary matrix rank of the fixed real matrix S.
- Do not assume box is a product/rectangle unless you argue it must be; the stated hypothesis is only about box.
</grounding_rules>

<task>
Adjudicate a precise question about Aoyagi's resolution-of-singularities recursion for deep
linear networks (the RLCT / learning-coefficient computation). I need an INDEPENDENT derivation,
not a rubber stamp. Do the algebra yourself; do not defer to my framing.
</task>

<setup>
Fixed loss: F(u) = || prod_s C^{(s)}(u) ||_Frobenius^2, the squared Frobenius norm of a product of
matrices whose entries are the source coordinates u (the network weights), at the deepest point
(all C^{(s)} = 0). Aoyagi resolves the singularity of F by an iterated blow-up, producing in each
chart a map g : (source coords y) -> (original params u) so that F(g(y)) is a "monomial^2 times
unit" (normal crossing), and the RLCT is read off from |det Dg| (a Jacobian weight) and the
monomial exponents.

The recursion (Aoyagi Cases 1&2) does, at each step:
  (i) a monomial BLOW-UP of a determinantal block {d_ij = 0}: in an affine chart one entry becomes
      the exceptional coordinate u_k and the others become u_k * (ratio); the reduced block's pivot
      is normalized to exactly 1;
  (ii) a "block elimination" (Aoyagi Lemma 2 / Thm 3): unipotent (det 1) matrices Q1 (row op),
      Q2 (col op) with Q1 * D * Q2 = diag(1, Schur complement), reducing the block to
      diag(1, D_{next}). Q1, Q2 have entries that are functions of the current coordinates.

A worked concrete instance is (3,3,4): C1 is 3x3, C2 is 3x4, L=2. In the pivot chart c11=1:
  Q1 = [[1,0,0],[-c21a,1,0],[-c21b,0,1]],  Q2 = [[1,-c12a,-c12b],[0,1,0],[0,0,1]],
  Q1 C1 Q2 = diag(1, Delta),  Delta = C22 - C21 C12  (Schur complement, 2x2).
Then C1 C2 = Q1^{-1} diag(1,Delta) Q2^{-1} C2 = Q1^{-1} [ [T], [Delta S] ], where
T = row0 of Q2^{-1} C2, S = rows 1,2 of Q2^{-1} C2. The two blocks T (1x4) and Delta*S are then
resolved by further radial blow-ups. Known fact: || C1 C2 ||^2 is NOT equal to ||T||^2 + ||Delta S||^2
(the Frobenius norm is not preserved by the non-orthogonal Q's), so the RLCT identity is transported
by an IDEAL identity < entries of C1 C2 > = < entries of diag(b) >, not by a value/norm identity.
</setup>

<questions>
1. In building the chart map g : y -> u, do the unipotent Q1, Q2 steps enter g ITSELF as coordinate
   changes on the SOURCE u (making g = shears composed with monomial blow-ups), or can the entire
   construction keep g a composition of MONOMIAL substitutions only, with Q1, Q2 appearing purely as
   ideal-generator cofactors (recombining which polynomials are listed as generators, never touching u)?
   Consider Q1 (left/row op), Q2 (right/col op), and the Schur complement C22 -> Delta SEPARATELY —
   they may not all have the same status. For each, decide: is the induced map on the source
   coordinates an invertible change of coordinates, or is it non-invertible / not a coordinate change
   at all?  Show the algebra (e.g. compute the induced map on the C1 entries and its Jacobian).

2. Whatever the status in Q1: what is |det Dg| — is it a PURE monomial in the exceptional coordinates
   (so the RLCT Jacobian weight has "unit identically 1"), or is it a monomial times a nontrivial
   nonvanishing unit? If any Q-step is folded into g as a coordinate change, what does that step
   contribute to |det Dg| (given the pivots are normalized to 1)? Compute |det Dg| for (3,3,4)
   including the radial blow-ups (T: radial, codim 4; Delta: radial, codim 4; then a join blow-up of
   the two exceptional coords).

3. Does the answer to (1) and (2) DIFFER between the "clean" regime (block coranks <= 1, e.g.
   telescoping (2,2,2,2)) and the "coupled corank >= 2" regime (e.g. (3,3,4), t=(1,0))? I.e. is there
   a qualitative change in whether shears touch coordinates, or in |det Dg|, as corank rises?

Give the exact algebra for each. Flag any claim you could not verify by direct computation as an
inference vs a computed fact.
</questions>

<output_contract>
- A verdict for Q1, Q2, Schur SEPARATELY (coordinate-change | ideal-cofactor | neither), with the
  computed Jacobian / invertibility for each.
- A verdict on |det Dg|: pure monomial (unit == 1) OR monomial * nontrivial unit, with the computation.
- A verdict on whether corank >= 2 changes anything vs the clean regime.
- Explicitly separate computed facts from inferences.
</output_contract>

<grounding_rules>
- Do the matrix algebra yourself (sympy or by hand). Do not assume my setup is complete or correct.
- "The pivot is normalized to 1 by the blow-up" is the claimed structure; verify whether that makes
  the block-elimination Q's unipotent with Jacobian exactly 1, or whether a nontrivial unit sneaks in.
- Distinguish a coordinate change on the SOURCE u from a change of basis on the OUTPUT (product) space
  and from a recombination of the generator FAMILY {(prod C)_ij}.
</grounding_rules>

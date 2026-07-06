<task>
I am adjudicating whether the RLCT LOWER bound for a deep-linear-network (DLN) square loss
admits an ELEMENTARY, DLN-STRUCTURE-SPECIFIC derivation, versus needing general parametrized
Morse-Bott / constant-rank machinery. I need your independent read on the actual method used
in the literature to compute this RLCT lower bound.

SETUP (exact objects):
- Layer widths d_0, d_1, ..., d_N in N (a DLN of depth N). Parameter space Rep = product over
  i of Mat(d_i, d_{i-1}) (composable matrix tuples A = (A_1,...,A_N)).
- mult(A) = A_N A_{N-1} ... A_1, a d_N x d_0 matrix.
- Fix a "true" matrix B of rank r, 0 <= r <= min_i d_i (realisable case). Define the loss
    K(A) = || mult(A) - B ||_F^2   (squared Frobenius norm; a sum of squares of the entries of
    the difference; each entry is a degree-N polynomial in the entries of A).
- K >= 0, K^{-1}(0) = mult^{-1}(B) = the fibre of the multiplication map over B.
- The real log-canonical threshold (RLCT) lambda = rlct(K) = sup{ s : |K|^{-s} locally integrable }.
- Watanabe's universal bound gives the UPPER bound lambda <= codim(mult^{-1}(B)) / 2
  (this side is easy, from the tangent-space / IFT at a smooth point of the zero locus).
- The HARD direction is the LOWER bound lambda >= codim / 2, i.e. proving the RLCT is not
  SMALLER than half the codimension. This is governed by the SINGULAR locus of K^{-1}(0),
  not the smooth locus. The equality lambda = codim/2 is the statement that the DLN loss is
  "as mildly singular as possible" (RLCT saturates the codim bound).

THE SPECIFIC CITED RESULT (what I am tracing the METHOD of):
- M. Aoyagi, "Consideration on the learning efficiency of multiple-layered neural networks
  with linear units", Neural Networks 172 (2024), article 106132. This computes rlct(K) for
  the DLN exactly. Earlier building block: Aoyagi & Watanabe, "Stochastic complexities of
  reduced rank regression in Bayesian estimation" (Neural Networks 2005) computes the RLCT
  (learning coefficient) for the THREE-layer / two-matrix case K = ||B A - B_0||^2 (reduced
  rank regression), which is the N=2 DLN.

WHAT I ALREADY KNOW / TRIED:
- For a NONDEGENERATE sum of squares x_1^2 + ... + x_e^2 the RLCT is e/2 = codim/2 by
  Thom-Sebastiani additivity (rlct(F+G) = rlct(F)+rlct(G) for F,G >= 0) plus rlct(x^2)=1/2.
  This handles the smooth / transverse part. The DLN loss is DEGENERATE (the zero locus is a
  singular variety = the rank/zero-product locus), so plain Thom-Sebastiani does not apply
  at the singular strata.
- The reduced-rank-regression (N=2) RLCT was originally computed via an EXPLICIT desingularization
  / blow-up (a sequence of monomial blow-ups) producing a normal-crossing form, then reading off
  the RLCT from the exponents of the monomialized Jacobian and the function.
- A Lean formalization has S2 = "monomial_rlct": given a NORMAL-CROSSING (monomial) local form,
  extract the RLCT as a min over blow-up chart data. The question is whether the DLN lower bound
  can be fed to S2 via an EXPLICIT, BOUNDED monomialization, rather than requiring a general
  parametrized-Morse-Bott / constant-rank-splitting theorem (which Mathlib lacks entirely).

I DELIBERATELY WITHHOLD my current leaning. Do NOT try to agree with me.
</task>

<questions>
1. METHOD of Aoyagi (2024) and Aoyagi-Watanabe (2005): By what technique is the RLCT LOWER bound
   actually established? Specifically: is it (a) an explicit resolution of singularities / an
   explicit sequence of monomial blow-ups producing a normal-crossing form, from which the RLCT is
   read off; (b) a reduction to reduced-rank-regression via recursion on depth (peeling one layer
   at a time), each step reduced-rank-regression's known RLCT; (c) a Newton-polyhedron / toric
   computation; (d) something using the group action / a slice; or (e) general Morse theory?
   Give your best reconstruction of the ACTUAL argument structure, distinguishing what is
   RIGOROUSLY established from folklore.

2. Is the blow-up / monomialization EXPLICIT and UNIFORM enough (a named, finite, combinatorial
   sequence of blow-ups indexed by the rank pattern / dimension vector) that one could in principle
   write it down concretely for a fixed dimension vector and depth, OR does the argument route
   through a non-constructive existence-of-resolution (Hironaka) step? For the N=2 (reduced rank
   regression) case, is the desingularization concretely a known explicit chart family?

3. THE SINGULAR-LOCUS LOWER BOUND: Independently of Aoyagi, is there a DIRECT lower-bound argument
   for rlct(||mult(A)-B||^2) >= codim/2 that exploits the polynomial/rank structure — e.g. via the
   zeta-function pole (Igusa-type), via a lower bound on rlct from an explicit upper bound on the
   density of the zero-locus (a volume/measure estimate |{K < epsilon}| <= C epsilon^{codim/2}), or
   via the group-orbit stratification (the fibre is a union of GL x ... x GL orbits with known
   codimensions)? Which of these is closest to a BOUNDED, formalization-scoped argument citing only
   the normal-crossing-to-RLCT extraction, and which genuinely need a resolution-of-singularities
   or Morse-Bott existence theorem?

4. For the DEEPEST / most-degenerate point (A = 0 when B = 0, or the fully-degenerate optimal),
   is there a shortcut: the loss near A=0 is (to leading order) a sum of squares of the degree-N
   monomials that are the entries of the product; does the RLCT of such a "product of matrices,
   sum of squares of degree-N monomials" have a known closed-form / explicit toric computation
   that avoids general Morse-Bott?
</questions>

<output_contract>
For each of the 4 questions: a direct answer, marked [FACT] (established/published, name the
mechanism) vs [INFERENCE] (your reconstruction) vs [UNCERTAIN]. Then a final section:
"CHEAPEST BOUNDED ROUTE" — if any elementary DLN-specific lower-bound route exists that could feed
a normal-crossing-to-RLCT extraction WITHOUT a general Morse-Bott/constant-rank existence theorem,
name it and its key steps; if you believe NO such elementary route exists and the general machinery
is genuinely required, say so plainly and identify the irreducible obstruction. Be concise.
Preserve your FACT-vs-INFERENCE distinctions.
</output_contract>

<grounding_rules>
Ground your answer in the actual published methods of Aoyagi (2024), Aoyagi-Watanabe (2005 reduced
rank regression), and Watanabe's singular learning theory (algebraic geometry / resolution of
singularities method for the RLCT). If you are reconstructing rather than recalling a specific
published lemma, mark it [INFERENCE]. Do not invent a citation. Do not paste runnable code.
</grounding_rules>

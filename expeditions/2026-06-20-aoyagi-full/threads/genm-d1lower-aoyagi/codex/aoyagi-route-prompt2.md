<task>
I have the primary source of Aoyagi's deep-linear-network (DLN) RLCT computation as a local PDF in
this repo. Read it and answer a focused route question. DO NOT web-search (offline). Use pdftotext.

PRIMARY SOURCE (read it):
  paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf
  Extract with:  pdftotext -layout <path> - | sed -n '840,3010p'
(This is Aoyagi 2024, "Consideration on the learning efficiency of multiple-layered neural networks
 with linear units", the paper that proves the DLN learning coefficient / RLCT. Section 5 "Proof of
 Main Theorem" is the relevant part, roughly text-lines 852-3010 of the layout extraction.)

CONTEXT (the adjudication):
- The DLN square loss is K(w) = ||prod_{s} A^(s) - prod_s A*^(s)||^2 (plus bias terms). Its RLCT
  (learning coefficient) lambda equals codim/2 of the fibre (the "mildly singular" statement).
- The EASY direction is the UPPER bound lambda <= codim/2 (smooth-point / IFT / tangent-space).
- The HARD direction is the LOWER bound lambda >= codim/2, governed by the SINGULAR locus (the
  deepest / most degenerate stratum). A deeper stratum could in principle have a SMALLER RLCT
  (higher vanishing order lowers the threshold); the DLN claim is that it does NOT.
- A Lean formalization already has S2 = "monomial_rlct": the bare fact that a NORMAL-CROSSING
  (monomial) local form u_1^{2k_1}...u_d^{2k_d} with Jacobian u_1^{h_1}...u_d^{h_d} has RLCT =
  min_j (h_j+1)/(2k_j). The question is whether Aoyagi's DLN lower bound can be formalized citing
  ONLY this S2 fact + elementary linear algebra, WITHOUT a general parametrized Morse-Bott /
  constant-rank-splitting existence theorem (which the Lean library lacks).

I WITHHOLD my current conclusion. Do not try to agree with me. Read the source and judge.
</task>

<questions>
1. What is the ARGUMENT STRUCTURE of Section 5's proof of the main theorem? In particular:
   (a) the role of Lemma 2 + Theorem 3 (regular matrices P1, P2 putting the product into a
       block-diagonal normal form diag(C1, prod C^(s))), and how the RLCT splits into a
       "regular/transverse" term [-r^2 + r(H^(1)+H^(L+1))]/2 PLUS lambda<prod C^(s)>;
   (b) the role of Theorem 4 ("Method for determining the deepest singular point") — does it
       reduce the RLCT to the deepest (origin) point via a HOMOGENEITY argument, giving the
       lower bound lambda(deepest) <= lambda(anywhere)?
   (c) the "recursive blow-up process" on the reduced matrices C^(s) (Cases 1, 1(1), 1(2), 2):
       is this an EXPLICIT, constructive sequence of monomial blow-ups along NAMED submanifolds
       {d_ij=0, u_{s,k}=0}, indexed combinatorially by the reduced dimensions M^(s), that produces
       a normal-crossing form?

2. Given (1): does the lower bound come DIRECTLY from the normal-crossing exponents (i.e. the same
   min_j (h_j+1)/(2k_j) extraction that S2/monomial_rlct provides), so that once the explicit
   blow-up sequence is carried out, BOTH bounds fall out of the monomial form + a Jacobian
   determinant computation + the arithmetic minimization (Lemma 3)?

3. Is there anywhere in Section 5 a step that genuinely requires a NON-CONSTRUCTIVE resolution
   (invoking Hironaka's existence theorem for the DLN function itself), a general Morse-Bott /
   constant-rank splitting, or an implicit-function-theorem-with-parameters — as opposed to the
   explicit named blow-ups + linear algebra? If yes, quote it. If no, say so.

4. FORMALIZATION SIZING: assuming the target Lean library has (i) S2 = monomial_rlct, (ii) the
   RLCT invariance under multiplication by a bounded-above-and-below positive analytic factor
   (Aoyagi's Theorem 3 Gram-matrix sandwich + the ideal-equality Lemma 1), and (iii) basic RLCT
   additivity for disjoint-variable-block sums — what is the residual mathematical content of the
   lower bound that would still need to be built? Is it (A) purely the explicit blow-up
   combinatorics + Jacobian bookkeeping + Lemma-3 arithmetic (bounded, if intricate), or (B) does
   it hide a genuinely missing analytic existence theorem?
</questions>

<output_contract>
Per question: a direct answer marked [FACT-from-source] (cite the text-line or theorem number you
read) vs [INFERENCE] vs [UNCERTAIN]. Final section "VERDICT": is the DLN RLCT lower bound a BOUNDED
explicit-blow-up build citing only S2 + elementary linear algebra, or does it genuinely require
general Morse-Bott / non-constructive resolution? If bounded, name the residual pieces and their
rough size; if a wall, name the irreducible obstruction. Be concise. Do not paste runnable code.
</output_contract>

<grounding_rules>
Ground your answer in the actual text of the local PDF (Section 5). Cite what you read. Mark
reconstructions [INFERENCE]. Do not web-search. Do not invent citations.
</grounding_rules>

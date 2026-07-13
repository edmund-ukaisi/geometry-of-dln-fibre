<task>
Adjudicate ONE truth-value about an induction step in a "resolution of singularities / RLCT"
formalisation. Answer the yes/no crisply, then justify with exact algebra. Do NOT rubber-stamp; if
you think the framing is wrong, say so.

QUESTION: In the recursion below, the singular locus of a deep-tail matrix Z is stratified into
"count shells" S_j indexed by j = 0,1,...,r (r = min(M0−t, M1−t)), where on S_j exactly j (lumped:
≥r at j=r) singular values of Z are below a threshold ε. On shell S_j the argument peels a corner at
cut u = t+j. The STRICT shells (j<r) are handled by a "head-split domination" that frees an
(M0−u)×(M1−u) corner block, blows up a pivot, and controls the corner's Gram determinant divisor
det(GramOfCorankBlock)^{-(M0−u)/2}. The SATURATED shell (j=r) has min(M0−u, M1−u) = 0.

Decide: at the saturated shell j=r, does the SAME head-split corner-domination machinery apply
(i.e. j=r is the same lemma as j<r), OR does j=r genuinely require a DIFFERENT (simpler) closing
argument because the corner degenerates? Give the exact reason and, if different, the exact simpler
argument.
</task>

<grounding_rules>
Treat these as GIVEN facts (definitions and banked lemmas of the formalisation; use them, do not
re-derive them):

- A "chain" is a width vector M = (M0, M1, ..., M_last), all Mi ≥ 1. "prod M A" is the ordered
  product of the layer matrices (M0×M1, M1×M2, ...). The loss is frobSq(prod M A) = sum of squares
  of entries.
- redChain u M := (u, M2, M3, ..., M_last): collapse the first two layers into a single pivot rank u,
  one fewer layer.
- peelCharge M u := (M0 − u)·(M1 − u)   [natural-number truncated subtraction].
- minAdm M is a nonneg integer (the "minimal admissible codimension" of the chain). carrierThreshold
  M = minAdm M / 2.
- BANKED (proved): for any legal cut u ≤ min(M0, M1),
       minAdm M ≤ peelCharge M u + minAdm (redChain u M).      (*)
  (An INEQUALITY; equality holds at the binding cut.)
- BANKED: the "front cut" t used for the shells is ≤ min(M0,M1), and the shell index j ranges
  0 ≤ j ≤ r := min(M0−t, M1−t). The cut on shell j is u = t+j.
- The induction is on chain ARITY (number of layers). The step is given a strong IH: for EVERY chain
  M' with one fewer layer and every "admissible decoration" D' of M', the box integral of D' is
  finite below carrierThreshold M' = minAdm M'/2. In particular the reduced chain redChain u M
  (one fewer layer than M) is covered by the IH.
- BANKED: there is an "admissible comparator" decoration of redChain u M whose loss is
  commonDivisor(v)^2 · frobSq(prod (redChain u M) z), admissible for the IH, whose box integral at
  exponent e is finite whenever e < minAdm(redChain u M)/2.
- The head-split domination (for j<r) produces:
       shellSpineIntegrand(cut u) ≤ C · comparator(redChain u M).integral(c' − ½·peelCharge M u),
  with C < ⊤, and then the IH closes the comparator PROVIDED
       c' − ½·peelCharge M u < ½·minAdm(redChain u M).
- The overall step operates at c' < carrierThreshold M = ½·minAdm M (strict).
- The block matrix being peeled is the M0×M1 leading layer written fromBlocks P B12 C D, where P is
  u×u (pivot), B12 is u×(M1−u), C is (M0−u)×u, D is (M0−u)×(M1−u) (the freed corner). The freed Schur
  loss = frobSq(P·Qtilde) + frobSq(C·Qtilde + D·Qbot) with Qtilde = Qtop + P^{-1}·B12·Qbot; the
  corner D is integrated as a free (M0−u)×(M1−u) variable against the corank block Qbot (which is
  (M1−u)×(deeper)); integrating it out yields the Gram divisor det(Qbot·QbotT)^{−(M0−u)/2} and a
  charge (M0−u)(M1−u)/2 = ½·peelCharge.

FACTS OF WHAT WAS TRIED / OBSERVED (verify or refute, don't just accept):
- At j=r, r = min(M0−t, M1−t) = min(M0,M1) − t, so u = t+r = min(M0,M1) EXACTLY.
- Hence at j=r, peelCharge M u = (M0−u)(M1−u) with min(M0−u,M1−u)=0, i.e. peelCharge = 0.
- The freed corner D is (M0−u)×(M1−u); one dimension is 0, so D is an empty matrix (a single point),
  and the Gram-divisor exponent (M0−u)/2 is either 0 (if M0−u=0 ⟹ det(...)^0 = 1) or the corank
  block Qbot is empty (if M1−u=0).

Answer these sub-questions explicitly:
Q1. At j=r, is the exponent shift ½·peelCharge M u = 0, so the comparator target is at exponent c'
    (unshifted)? And does the IH then close it, i.e. is c' < ½·minAdm(redChain u M)? Use (*).
Q2. When one corner dimension is 0, what does the corner-Gram-divisor control (the det^{−(M0−u)/2}
    factor and the ½·peelCharge charge) contribute? Is it load-bearing at j=r or vacuous?
Q3. Does the head-split domination's HARD content (controlling how the corner Gram determinant
    degenerates as the deep tail Z degenerates, uniformly) have anything to control at j=r, or is it
    inert because there is no corner Gram divisor?
Q4. If j=r is closed by a simpler argument, state it precisely: what is peeled, what charge is used,
    which IH instance closes it, and why the strict c' < ½·minAdm M suffices even if (*) is tight at
    u=min(M0,M1).
</grounding_rules>

<output_contract>
1. VERDICT: one of {SAME-LEMMA-AS-j<r, DIFFERENT-SIMPLER-ARGUMENT, framing-is-wrong}. One line.
2. Q1–Q4 answered, each with the exact arithmetic.
3. The single most likely way your verdict is WRONG (the failure mode to check).
Keep it tight. Exact algebra only; no hand-waving about "generically".
</output_contract>

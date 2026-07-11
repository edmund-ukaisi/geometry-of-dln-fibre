<task>
Adversarially audit the ENCODING of an admissibility predicate for a decorated induction. Find the slop:
is the predicate TOO LOOSE (admits members whose base case is false) or TOO TIGHT (excludes members the
recursion actually produces, so peel-closure fails)? Reason in exact algebra. Self-contained.

CONTEXT. A decorated finiteness induction proves INT loss^{-c'} d(measure) < ⊤ for c' < ½·minAdm(M), over
chains M=(M0,...,ML). The induction is over an ADMISSIBLE family of "decorations" D (a monomial carrier: a
support/coeff on exceptional-divisor coordinates + a deeper context). Driver (already built, abstract in a
predicate `adm`):
 - base `DecoratedBaseHyp adm`: for admissible fully-reduced D, the loss is finite (reduces to a banked
   monomial-integral lemma `sjLoss_terminal`);
 - step `DecoratedStepHyp adm`: admissible D at arity L, given the decorated IH at arity L-1, is finite;
 - specialise at the TRIVIAL decoration to recover the plain statement.

THE PEEL. One decorated peel of M at a binding cut t (a=M0-t, b=M1-t, front Gamma-block a×b) blows up the
Gamma-block (radial u, det-normal v) and hands a reduced-chain decoration to the IH. The loss on the front
chart is f = R² + u²(H₁² + v²H₂²), H₁=|q₁+s q₂|, H₂=|q₂| the corank rows, R the pivot energy.

ESTABLISHED FACTS (take as given, proven elsewhere):
 (F1) The load-bearing valuation is p = ν_η(H₁) on the CRITICAL reduced divisor η. Finiteness at ½minAdm
      holds iff p=0 on every critical divisor (a combined-ray formula: p>0 ⟹ an exceptional ray with ratio
      < ½minAdm). q=ν_η(H₂) is HARMLESS (p=0,q≥0 still fine).
 (F2) TRANSVERSALITY (proven, width-general): at a nondegenerate binding cut (a≥1,b≥1), every top-dim
      component X of the reduced zero-product locus has generic deeper rank rank_gen,X(Zdeep) ≥ a+b-1 ≥ b.
      Hence the corank block A_cor·Zdeep has generic row rank b there → the corank rows are UNITS → p=0.
      IMPORTANT: this does NOT say Zdeep is generic FULL rank — e.g. reduced (2,2,2) has its unique top
      component at rank Zdeep=1 < 2 (a real rank drop), yet b=1 so the single corank row still survives (p=0).
 (F3) Degenerate peels (a=0 or b=0): the Gamma-block is empty, no corank term, so p=0 is VACUOUS (a no-op
      layer-drop). So p=0 is needed exactly at peels with a≥1 AND b≥1.
 (F4) Terminal reduction: on the p=0 divisor H₁,H₂ are units, f ≍ R² + u²·(unit); the fully-resolved loss is
      a sum of exceptional monomials, finite via `sjLoss_terminal` GIVEN a "dehomogenised generator" hypothesis
      (∃ a generator NOT divisible by the shared/critical divisor).

THE PROPOSED ENCODING (to audit). `adm n M D` := "D is reachable-from-trivial by peels" AND "D is p=0-
transverse", where p=0-transverse is stated as: "the corank generators of the carrier are NOT divisible by
the critical (pivot-vanishing) divisor — i.e. the shared deeper Z enters them at FULL RANK." The three
invariants claimed: (i) trivial ∈ adm (carrier = product entries, no exceptional divisors, p=0 vacuous);
(ii) peel-closed (a decorated peel of an admissible D is admissible = F2); (iii) provable base (F4).
</task>

<output_contract>
Rank the encoding's failure modes. Specifically decide, with reasons:
 Q1. Is the p=0-transverse clause AS STATED ("shared deeper Z enters at full rank") correct, or is it TOO
     TIGHT? (Cross-check against F2's (2,2,2): rank Z = 1 < 2 = not full, yet admissible.) If too tight,
     state the CORRECT predicate.
 Q2. Is "reachable-from-trivial" ∧ "p=0-transverse" the right conjunction, or is one clause redundant /
     one too loose? Does reachability (via binding-cut peels) already IMPLY p=0-transversality (F2), so
     transversality should be a THEOREM not a carried hypothesis? Or can a reachable D be non-transverse?
 Q3. Does the TERMINAL/base (F4) actually follow from the predicate — is "p=0" exactly the "dehomogenised
     generator" hypothesis `sjLoss_terminal` needs, or is there a gap (e.g. wide corank b>2, or the
     intersection of two critical divisors)?
 Q4. TOO-LOOSE check: is there a reachable, "p=0-transverse"-as-encoded decoration whose base case is
     nonetheless FALSE (finiteness fails)? TOO-TIGHT check: a decoration the peel genuinely produces that
     the predicate REJECTS (breaking peel-closure)?
For each: verdict (SOUND / TOO-TIGHT / TOO-LOOSE / GAP) + the fix. End with the single cleanest correct
`adm` predicate you would encode, and the cheapest check that would break a wrong one.
</output_contract>

<grounding_rules>
Do not assume the proposed encoding is right. The distinction "corank generator not divisible by critical
divisor (valuation 0)" vs "Zdeep full rank" is load-bearing — test it against F2's (2,2,2). Distinguish a
too-tight predicate (peel-closure false) from a too-loose one (base false). Reason in exact algebra.
</grounding_rules>

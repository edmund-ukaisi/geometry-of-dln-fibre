<task>
Corroborate or refute a sharp result from an exact-algebra pass, and sanity-check the resulting
build decision for a deep-linear-network RLCT formalisation. Do NOT rubber-stamp.

CONTEXT. Box integral ∫_box ‖A0···A_{L-1}‖^{-2c'} finite for c'<½minAdm(M) (Aoyagi's exact DLN
learning coefficient). The boundary-0 peel at cut t (charge a=(M0-t)(M1-t)) was shown to collapse
EXACTLY to a per-step integrand J ≍ P_tail^{-(c'-a/2)} · P_full^{-a/2}, where P_tail=(t,M2,…,ML)
reduced-chain loss and P_full=(M1,…,ML) FULL-remaining-product loss (coupling factor), sharing the
deeper factors B:=A2···A_{L-1}. Question was: does this reduce to a black-box tail-chain call, or need
Aoyagi's joint (S,J) double induction?

THE OVERTURN TEST just run (integrate out the spectator rows Y = bottom M1-t rows of A1 first):
    M(X,B) := ∫_Y P_full^{-a/2} dY = ∫_Y (‖XB‖^2 + ‖YB‖^2)^{-a/2} dY,   g:=‖XB‖=√P_tail.
EXACT NUMERICAL RESULT (GL quadrature + MC, clean slopes):
  M(X,B) ≍ bounded/log(1/g)              when  a ≤ (M1-t)·rank(B)
  M(X,B) ≍ g^{-(a-(M1-t)·rank(B))} (POWER) when a > (M1-t)·rank(B).
So the coupling is benign (only a log, harmless to the RLCT) on the GENERIC full/high-rank shared
factor, but LOSES A POWER on the shared factor's LOW-RANK strata. Confirmed e.g. M=(4,4,4,4), cut t=2
(a=4, spectator 2×4): at rank(B)=1 the multiplier ~ g^{-2}. At full-rank-B, a ≤ (M1-t)M2 holds at
ALL binding cuts (0 violations / 5440 chains). A uniformly-"gentle" binding path (a ≤ M1-t at every
L≥3 peel, which would confine power loss to rank(B)=0 only) does NOT always exist (1966/5440 chains
force a non-gentle cut at some level).

INTERPRETATION I reached: the power loss on the shared factor's low-rank divisors = exactly the
deeper boundary's rank drop; absorbing it needs cross-level charge transfer = Aoyagi's accumulating
diag(b) / D_J bookkeeping. A black-box single-chain recursion (opaque tail-finiteness hypothesis)
cannot do this transfer. Verdict: JOINT (S,J) needed, BOUNDED (all charges sum to minAdm; coupling
always subordinate so the value is exactly ½minAdm). The multiplier finding SHARPENS the wall:
coupling benign except on shared-factor rank-drop divisors, localizing the (S,J) blow-up's work.

<grounding_rules>
- Treat the exact identity and the numerically-verified multiplier criterion (a vs (M1-t)·rank(B)) as
  given facts. Judge the INTERPRETATION and the build decision. Separate inference from assertion.
</grounding_rules>

<output_contract>
1. Do you AGREE the power loss on the shared factor's low-rank strata blocks a black-box single-chain
   reduction and requires the joint (S,J) resolution? BOUNDED or new obstruction? One line.
2. Is there a lighter escape I am missing: e.g. a resolution that ALWAYS chooses a gentle cut where the
   deeper factor is generic, handling low-rank-B strata by a SEPARATE (cheaper) sub-induction rather than
   the full (S,J)? Or is the cross-level transfer genuinely irreducible? Be concrete.
3. Briefly: the minimal formalisable pieces of Aoyagi's diag(b)·[E_J|D_J]·∏C^{(s)} double induction
   (S=layer, J=within-layer rank-drop counter) — list the ~5-7 lemmas a Lean build would need, in
   dependency order, flagging which is the load-bearing analytic core vs mechanical plumbing.
</output_contract>

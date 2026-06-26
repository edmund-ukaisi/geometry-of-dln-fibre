<task>
Decorrelated soundness check of a Lean theorem's CONJUNCTS. I suspect two conjuncts of a downstream
"producer" obligation are FALSE as stated, and want an independent verdict before I report it (this is a
kill-condition-level claim, so I need a careful second opinion, not agreement).

## Context

Deep-linear-network RLCT, deepest point, L=2 reduced core. A "producer" theorem `hproducer` asserts:
there exist constants t, gamma1, gamma2 > 0 and a neighborhood U of the deepest point (in flat
parameter coords) such that FOR EVERY w in U, with block matrices (P00 invertible, P01, P10, P11) read
off the conjugated/reindexed loss `reindex(P0*(prod(w) - B)*QL) = fromBlocks (P00-1) P01 P10 P11`,
defining Rcore := P11 - P10 * inv(P00) * P01 (the global product Schur complement) and
coreF := deepestCoreF(coreAbsorb(split w)) = ||S0(w) * S1(w)||_F^2 (the product of the two per-layer
reduced Schur cores), the following TWO conjuncts hold with the SAME gamma1, gamma2 uniform over U:

    (d)  sum_ij (Rcore i j)^2  <=  gamma2 * coreF
    (e)  coreF  <=  gamma1 * sum_ij (Rcore i j)^2

i.e. a UNIFORM two-sided multiplicative comparability of ||Rcore||^2 and ||S0 S1||^2 over a whole
neighborhood U.

## The known facts (from an earlier symbolic/numeric cert, S5c)

- EXACT middle-factor identity (L=2): Rcore = S0 * W * S1, W = I - Z1 * A^{-1} * Y0, A the product pivot.
- So Rcore - S0*S1 = -S0*(Z1 A^{-1} Y0)*S1.
- The cert found a COUNTEREXAMPLE to the naive uniform box ratio ||Rcore||^2 ~ ||S0 S1||^2 for core
  dimension M>1: take S0 = eps*E_12, S1 = eps*E_21 (rank-1 each). Then S0*S1 = eps^2 * E_11 != 0, but W
  can have W[1,1] = 0, forcing Rcore = S0*W*S1 = 0. So ||Rcore||^2 = 0 while ||S0 S1||^2 = eps^4 != 0.
- The cert's verdict: the comparability is a GERM statement (the ABSOLUTE in-sum bound
  |sum||Rcore||^2 - sum||S0 S1||^2| <= C * sumE2 holds on a neighborhood), NOT a uniform two-sided
  multiplicative box ratio.

## My claim to check

I claim conjunct (e) `coreF <= gamma1 * ||Rcore||^2` is FALSE as a UNIFORM-over-U statement, because:
the counterexample point (S0 = eps E_12, S1 = eps E_21, W[1,1]=0) can be realized for arbitrarily small
eps, hence inside ANY neighborhood U of the deepest point. At such a point coreF = ||S0 S1||^2 = eps^4 >
0 but ||Rcore||^2 = 0, so (e) reads eps^4 <= gamma1 * 0 = 0, contradiction. Therefore NO finite gamma1
makes (e) hold uniformly on any U. (And symmetrically (d) is the SAFE direction — ||Rcore||^2 <=
gamma2*coreF could fail too if Rcore can exceed S0 S1, but the counterexample makes Rcore=0 which is
fine for (d); (d) might be salvageable, (e) is the broken one.)

## Questions

1. Is my claim that conjunct (e) is FALSE-as-uniform CORRECT? Walk through whether the counterexample
   point is genuinely realizable inside an arbitrary U (i.e. is W[1,1]=0 achievable with S0,S1 = O(eps)
   AND the off-pivot data Y0,Z1 also -> 0? The cert says W[1,1]=0 requires off-pivot Y0*Z1 ~ -1 which is
   O(1), NOT a germ path -- so on the GERM both Y0,Z1 -> 0 and W -> I. Does that RESCUE (e)? Reconcile:
   is the S0=eps E12 / S1=eps E21 counterexample a GERM path (all deviations incl Y0,Z1 -> 0) or does it
   require off-germ O(1) data? If the rank-deficiency counterexample needs W[1,1]=0 which needs O(1)
   off-pivot, then on a small enough U it does NOT arise, and (e) MIGHT hold. Which is it?)

2. If (e) CAN be rescued by shrinking U (because the W[1,1]=0 obstruction is off-germ), then what is the
   correct sufficient condition / lower bound? I.e. on a small U is there a uniform gamma1 with
   coreF <= gamma1 * ||Rcore||^2? Sketch why (the relative-error route: ||Rcore - S0 S1||^2 <= theta *
   ||S0 S1||^2 with theta < 1 on a small U, giving (1-sqrt(theta))^2 ||S0 S1||^2 <= ||Rcore||^2)? Does
   that relative bound actually hold uniformly on a small U, or does the rank-deficient S0/S1 still break
   it (||S0 S1||^2 = eps^4 but ||Rcore - S0 S1||^2 = ||S0 W' S1||^2 could be COMPARABLE to eps^4, theta
   NOT < 1)?

3. BOTTOM LINE: is hproducer's conjunct (e) (and (d)) PROVABLE as a uniform-over-U multiplicative
   comparability, or must it be RE-STATED (e.g. as the absolute in-sum germ bound, or with the loss/E
   energy folded in as in the cert's `sumE2 + ||Rcore||^2 ~ sumE2 + ||S0 S1||^2` form)? Give a crisp
   PROVABLE-AS-IS / MUST-RESTATE verdict.
</task>

<output_contract>
Three numbered sections (Q1, Q2, Q3), each <= 220 words. Q1: is the counterexample a germ path or off-germ
(decisive). Q2: does shrinking U rescue (e), with the relative-error analysis. Q3: crisp verdict
PROVABLE-AS-IS or MUST-RESTATE, and if restate, the exact correct statement. End with one BOTTOM LINE line.
</output_contract>

<grounding_rules>
Do NOT just agree with me -- I want the truth. If the counterexample is off-germ (needs O(1) off-pivot
data), then it does NOT live in a small U and (e) may be fine; say so. If it IS a germ path, (e) is
broken; say so. Distinguish "this is forced by the algebra" (fact) from "I expect" (inference). The
key technical question is whether ||S0 W S1||^2 / ||S0 S1||^2 can stay bounded BELOW away from 1 (i.e.
||Rcore||^2 not collapsing relative to ||S0 S1||^2) UNIFORMLY on a small germ where Y0, Z1 -> 0.
</grounding_rules>

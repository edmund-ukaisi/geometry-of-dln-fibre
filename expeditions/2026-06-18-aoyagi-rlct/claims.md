# claims.md - Aoyagi claim ledger

Each claim is a working card. Source inventory must replace all `TBD` entries
with page-pinned source references before formalisation depends on them.

For every substantial Aoyagi-specific calculation, add:

- **Pen-and-paper reproduction.** path/status.
- **Reproduction check.** checker/path/verdict.

No such claim is formalisation-ready until both fields are filled.

## Claim A0 - cited normal-crossing extraction interface

- **Statement.** A suitable normal-crossing presentation of the transformed
  square loss determines the RLCT and pole order by the standard exponent
  minimum/order formula.
- **Tier.** Established analytic background.
- **Status.** open; intended Cited.
- **Kill-condition.** Aoyagi's final extraction uses an analytic hypothesis not
  captured by the interface we state, or the interface computes a different
  invariant.
- **Evidence/source.** Aoyagi Definition 1, Lemma 1, Definition 2, and
  Hironaka/normal-crossing extraction discussion, PDF pp. 5-6.
- **Pen-and-paper reproduction.** Cite-interface check pending.
- **Reproduction check.** analytic scout report at
  `threads/02-analytic-interface/scout-report.md`; controller interface draft
  at `threads/02-analytic-interface/interface-draft.md`.
- **Lean target.** A named hypothesis/interface, not a theorem pretending to
  prove the analytic extraction.
- **Proved.** none by us.
- **Assumed.** the exact normal-crossing hypotheses once specified.
- **Cited.** normal-crossing-to-RLCT extraction theorem.
- **Deferred.** formal proof of the analytic theorem.
- **Controller caution.** Aoyagi Lemma 1 on PDF p. 5 is analytic ideal-generator
  background. The expedition must not cite it as an additional Lean axiom unless
  the operator explicitly expands the cited boundary; prove/avoid it or include
  only the exact needed content in the single normal-crossing extraction
  interface.

## Claim A1 - block elimination

- **Statement.** Aoyagi's full-rank block reduction rewrites a block matrix on
  an explicit full-rank chart into a block diagonal form by triangular
  invertible matrices; broader ideal/loss-germ consequences are separate.
- **Tier.** Established in Aoyagi; to be proved in Lean if elementary.
- **Status.** algebraic core formalised: Schur-complement block identities and
  rank formula are proved and reviewed in Lean; analytic/local-germ
  consequences remain out of scope.
- **Kill-condition.** The transformation requires an analytic/local inverse or
  rank-open chart hypothesis not represented in the Lean statement.
- **Evidence/source.** Aoyagi Lemma 2, PDF pp. 10-11.
- **Pen-and-paper reproduction.** draft at
  `threads/03-block-product-reduction/reproduction-draft.md`.
- **Reproduction check.** partial pass at
  `threads/03-block-product-reduction/reproduction-check.md`.
- **Lean target.** `DLNFibre.DLN.Aoyagi.schurComplement_leftBlockElim_fromBlocks`
  and `DLNFibre.DLN.Aoyagi.schurComplement_blockElim_fromBlocks`,
  plus `DLNFibre.DLN.Aoyagi.rank_fromBlocks_zero_zero` and
  `DLNFibre.DLN.Aoyagi.rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det`,
  in `lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`.
- **Proved.** two algebraic block identities over a commutative ring, and over a
  field the block-diagonal rank additivity theorem and Schur-complement rank
  formula under explicit determinant-unit chart hypothesis `IsUnit A1.det`.
- **Assumed.** determinant-unit chart for the top-left block.
- **Cited.** none planned.
- **Deferred.** RLCT/local-germ invariance consequences until analytic boundary
  is resolved; product-level basis/open-chart induction remains A2.

## Claim A2 - product reduction

- **Statement.** The DLN product near a rank-r target splits into regular square
  factors and a reduced singular product, with RLCT computation reducible to the
  reduced problem plus regular variables.
- **Tier.** Established in Aoyagi; to be proved except for analytic extraction.
- **Status.** full claim blocked; chart-local algebraic induction step is
  reproduction-ready after repair report.
- **Kill-condition.** The reduction silently uses the cited normal-crossing/RLCT
  theorem or another analytic equivalence not represented as a hypothesis.
- **Evidence/source.** Aoyagi Theorem 3 and following regular-variable
  contribution, PDF pp. 11-13.
- **Pen-and-paper reproduction.** draft at
  `threads/03-block-product-reduction/reproduction-draft.md`.
- **Reproduction check.** findings at
  `threads/03-block-product-reduction/reproduction-check.md`; not
  formalisation-ready as stated. Repair report at
  `threads/03-block-product-reduction/reproduction-repair-a2.md`.
- **Lean target.** chart-local algebraic induction-step theorem next; full
  Theorem 3 target blocked.
- **Proved.** pending.
- **Assumed.** rank and dimension hypotheses.
- **Cited.** analytic invariance only if source inventory shows it is not purely
  algebraic.
- **Deferred.** post-Theorem-3 RLCT reduction and regular-coordinate additivity
  until the allowed analytic interface is fixed.

## Claim A3 - deepest singular point

- **Statement.** The global RLCT is attained at the deepest singular point used
  by Aoyagi's reduction.
- **Tier.** Established in Aoyagi; status to be decided by probe.
- **Status.** scope conflict / probe. Xhigh scout says this is analytic
  background cited to another Aoyagi paper, but the goal permits only the
  normal-crossing extraction citation in Lean.
- **Kill-condition.** The proof depends on lower semicontinuity/global analytic
  facts rather than elementary homogeneous scaling or explicit reduction.
- **Evidence/source.** Aoyagi Theorem 4, PDF p. 14.
- **Pen-and-paper reproduction.** pending/probe.
- **Reproduction check.** pending.
- **Lean target.** TBD by thread 02 or 06.
- **Proved.** pending.
- **Assumed.** TBD.
- **Cited.** not allowed as a separate Lean citation under current goal.
- **Deferred.** restricted proof or avoidance strategy pending.
- **Controller caution.** Allowed paths are: prove a restricted homogeneous
  deepest-point lemma, avoid Theorem 4 by formulating locally at the deepest
  point, or surface an operator decision to expand the cited boundary.

## Claim A4 - blow-up transition certificate

- **Statement.** Aoyagi's recursive Case 1 / Case 2 coordinate substitutions
  transform the reduced ideal into a monomial/diagonal normal-crossing form with
  the exponent vectors stated in the paper.
- **Tier.** New Lean packaging of established Aoyagi proof.
- **Status.** blocked after independent reproduction check; draft has a
  source-fidelity error in width bookkeeping and unresolved chart,
  regularity/divisibility, termination, and boundary-case gaps.
- **Kill-condition.** The transition system misses a source chart or permits a
  terminal state not covered by Aoyagi's proof.
- **Evidence/source.** Aoyagi blow-up section, PDF pp. 14-23.
- **Pen-and-paper reproduction.** draft at
  `threads/04-blow-up-certificate/reproduction-draft.md`.
- **Reproduction check.** failed/blocked at
  `threads/04-blow-up-certificate/reproduction-check.md`.
- **Lean target.** TBD by thread 04.
- **Proved.** pending.
- **Assumed.** finite dimension/rank hypotheses; no transition invariant is
  accepted yet.
- **Cited.** none planned.
- **Deferred.** none planned.

## Claim A5 - arithmetic minimisation and pole-order count

- **Statement.** The exponent vectors from the blow-up certificate have minimum
  ratio and multiplicity/order equal to Aoyagi's closed formula.
- **Tier.** Established in Aoyagi; to be proved in Lean.
- **Status.** blocked after independent reproduction check; interior quadratic
  algebra is promising, but endpoint cases, terminal-variable restriction,
  minimiser feasibility, and Lemma 5 order-count construction are not checked.
- **Kill-condition.** Boundary cases in the dimension vector contradict the
  stated minimiser or pole-order count.
- **Evidence/source.** Aoyagi quadratic exponent expression and Lemmas 3-5,
  PDF pp. 22-27.
- **Pen-and-paper reproduction.** draft at
  `threads/05-arithmetic-tail/reproduction-draft.md`.
- **Reproduction check.** failed/blocked at
  `threads/05-arithmetic-tail/reproduction-check.md`.
- **Lean target.** TBD by thread 05.
- **Proved.** pending.
- **Assumed.** exact integer hypotheses from Aoyagi; no RLCT/arithmetic final
  theorem is accepted yet.
- **Cited.** none planned.
- **Deferred.** none planned.

## Claim A6 - final Aoyagi formula, conditional on A0

- **Statement.** Combining the proved Aoyagi-specific reductions with the cited
  normal-crossing extraction interface gives Aoyagi's RLCT and RLCT-order
  formula for deep linear networks.
- **Tier.** Final synthesis claim.
- **Status.** open.
- **Kill-condition.** Any source hypothesis, rank bound, dimension convention,
  or pole-order convention is lost in translation.
- **Evidence/source.** Aoyagi Theorem 2, PDF pp. 8-9. Aoyagi Theorem 1
  (PDF pp. 6-7) is a cited earlier three-layer formula, not the multi-layer
  main theorem.
- **Pen-and-paper reproduction.** pending.
- **Reproduction check.** pending.
- **Lean target.** TBD after A1-A5.
- **Proved.** pending; should include all Aoyagi-specific content.
- **Assumed.** cited analytic interface A0 and source hypotheses.
- **Cited.** A0 only, if expedition succeeds as intended.
- **Deferred.** formal analytic extraction theorem.

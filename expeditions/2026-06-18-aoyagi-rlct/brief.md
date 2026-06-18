# Expedition brief - aoyagi-rlct

## Central question

Formalise Aoyagi's 2023 computation of the learning coefficient for deep linear
networks as an independent Lean development, following Aoyagi's elementary
coordinate reductions and blow-up bookkeeping rather than the quiver-geometric
paper.

The target is ambitious: prove every Aoyagi-specific algebraic, matrix, blow-up
bookkeeping, and finite-arithmetic step that is within reach. The planned cited
boundary is the general analytic theorem that extracts the RLCT and pole order
from a normal-crossing resolution. That boundary must be explicit in the final
statement and in the statement cards.

## Workspace

This expedition runs in the dedicated worktree
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`
on branch `expedition/aoyagi-rlct`. Controller and teammates should treat that
worktree as the expedition root. Do not write Aoyagi expedition state into the
main checkout unless explicitly integrating or closing.

## Scope

In scope:

- Aoyagi's notation, hypotheses, and final formula, transcribed faithfully from
  `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`.
- The elementary matrix reductions around full-rank blocks.
- The product reduction that separates regular square factors from the reduced
  singular product.
- The recursive blow-up case split as formal coordinate transformations or as a
  certified finite transition system whose terminal state gives the
  normal-crossing exponents.
- The finite arithmetic minimisation and pole-order count.
- The translation between Aoyagi's dimension notation and this repo's DLN
  notation, using Aoyagi's paper as the source of truth.

Out of scope unless the operator reopens it:

- Formalising the general analytic resolution theorem that converts a
  normal-crossing form into RLCT and multiplicity. This is Cited.
- Replacing Aoyagi's statistical-learning setup with a broader Watanabe theory.
- Using the Lehalleur-Rimanyi quiver paper, its Lean formalisation, or its
  notation as a proof input or source-fidelity shortcut. Any comparison with
  that paper is outside this Aoyagi-only expedition.

## Controller directive

Default stance: Prove, do not pre-defer. A small missing helper, parser,
certificate checker, or Lean API is infrastructure to build. A gap may be moved
to Cited or Deferred only after a real probe shows it is analytic background,
not Aoyagi-specific elementary content.

The controller may do tactical probes and integration work, but substantive
proof threads should be owned by formalisation or pen-and-paper teammates. Every
claim with broad scope must pass fidelity review and a hardener pass before it
is treated as bedrock.

## Pen-and-paper reproduction gate

Before any substantial Aoyagi calculation becomes a Lean formalisation target,
there must be a pen-and-paper reproduction artifact. This is not a summary of
the paper. It is a re-derivation in the expedition's own notation, with:

- the source hypotheses copied exactly;
- each algebraic transformation or case split reproduced step by step;
- boundary cases and dimension/rank edge cases checked explicitly;
- the exact point where the cited normal-crossing extraction interface is used;
- a list of kill-conditions that would refute the reproduced calculation.

A separate checker then reads the reproduction against Aoyagi's PDF and the
claim card. Only after that check can the controller mark the claim
formalisation-ready. This is the expedition-level version of the stance in
`CLAUDE.md`: observe before theorising, distinguish data from interpretation,
and fill the layer before building on it.

## Rungs

1. Source inventory and statement cards. Build the theorem ledger from the PDF:
   definitions, lemmas, theorems, hypotheses, notation, source pages, and exact
   dependencies.
2. Analytic interface. State the cited normal-crossing-to-RLCT theorem as a
   named interface with exact inputs and outputs. Do not hide it in an RLCT
   theorem name.
3. Pen-and-paper reproduction. Reproduce each substantial calculation cluster
   before assigning the corresponding Lean tide; record the reproduction and
   checker verdict in the claim card and theorem ledger.
4. Block and product reductions. Formalise Aoyagi's block Gaussian elimination
   and the reduction of the matrix product to the smaller singular core.
5. Blow-up certificate. Recast Aoyagi's recursive Case 1 / Case 2 proof as a
   finite transition invariant or certificate, and prove the certificate matches
   the coordinate substitutions.
6. Arithmetic tail. Prove the finite minimisation lemmas and pole-order count.
7. Final synthesis. Assemble the conditional Aoyagi theorem: Aoyagi-specific
   computation proved; analytic normal-crossing extraction cited.
8. Review to equilibrium. Fidelity, precision, source, and hardener reviews for
   each broad theorem and the final theorem.

## Closing criterion

- A green, sorry-free, axiom-clean Lean development for the Aoyagi-specific
  content that the expedition claims to prove.
- A final theorem whose statement names the cited analytic interface explicitly.
- `claims.md` and `theorem-ledger.md` complete enough that a post-compaction
  controller can identify every source theorem, Lean theorem, status, and
  remaining cited/deferred boundary.
- Pen-and-paper reproduction artifacts, with independent checker verdicts, for
  every substantial Aoyagi calculation used by the final theorem.
- Statement cards for the final theorem and each load-bearing intermediate
  theorem.
- A final `synthesis.md` and reader-facing exposition explaining what was
  proved and what was cited, using Aoyagi's paper as the primary source.

## Pointers

- Process: `../../CLAUDE.md`, `../../docs/policies/expedition.md`,
  `../../docs/policies/claims.md`, `../../docs/policies/precision.md`,
  `../../docs/policies/bedrock.md`, `../../docs/policies/review.md`.
- Lean: read `../../lean/CLAUDE.md` before any Lean work.
- Source: `../../paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`.

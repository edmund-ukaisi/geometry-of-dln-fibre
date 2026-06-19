# Thread 03 - block and product reduction

Type: formalisation. Status: in-progress.

## Task

Formalise Aoyagi's elementary matrix reductions: the full-rank block elimination
and product reduction.

## Output contract

- Lean statements for Claim A1 and Claim A2 at exact scope.
- Proofs where elementary; any analytic/local hypotheses named explicitly.
- Statement cards at AUDIT time.

## Controller notes

Read `lean/CLAUDE.md` before Lean work. Keep Aoyagi/DLN application code out of
`DLNFibre.Core`.

## 2026-06-18 A1 narrow tide

Opened xhigh worker tide `Lovelace` for the first Lean implementation. Scope is
only Aoyagi Lemma 2's checked algebraic block-elimination chart identity, and
possibly the rank formula if it falls out without overclaiming. Explicitly out
of scope: RLCT invariance, local-germ/ideal consequences, Theorem 3 product
reduction, and target-normalisation claims.

Read-only xhigh statement reviewer `Euclid` was also opened to audit the exact
statement shape before controller acceptance.

Outcome: landed two algebraic block identities in
`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`:
`schurComplement_leftBlockElim_fromBlocks` and
`schurComplement_blockElim_fromBlocks`. Theorems are over `[CommRing K]` with
explicit chart hypothesis `IsUnit A1.det`, and contain no rank/RLCT/germ/ideal
claim. Controller verified targeted build, full `DLNFibre` build, and
`scripts/sorries`. Statement card:
`statement-card-a1-block-identities.md`.

Remaining A1 target: rank formula as a separate theorem, likely via a
block-diagonal rank lemma over a field. A2 remains blocked by the checker
findings: source-faithful basis/open-chart hypotheses and analytic-boundary
decision.

## 2026-06-18 A1 rank-formula tide

Opened xhigh worker tide `Lovelace` to prove a separate block-diagonal rank
theorem and then the Schur-complement rank corollary. Scope remains purely
algebraic: no RLCT/germ/ideal/Theorem 3 claim.

Outcome: landed `rank_fromBlocks_zero_zero` and
`rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det` in
`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`. Controller verified targeted
build, full `DLNFibre` build, and `scripts/sorries`. Xhigh reviewer `Euclid`
accepted after minor docstring/name edits. Rank statement card:
`statement-card-a1-rank-formula.md`.

## 2026-06-18 A2 repair scout

Opened xhigh read-only scout `Erdos` to repair the pen-and-paper reproduction of
Aoyagi Theorem 3/product reduction before any A2 Lean target. The requested
output is a source-faithful algebraic statement, induction invariant, boundary
case analysis, and separation of analytic/RLCT assumptions.

Outcome: report saved at `reproduction-repair-a2.md`. Verdict: full Theorem 3
is still blocked, but the chart-local algebraic induction-step theorem is
reproduction-ready for Lean. The target-product normalization and post-Theorem-3
RLCT equality remain analytic-boundary issues.

## 2026-06-18 A2 chart-local induction-step tide

Opened xhigh formalisation work on only the reproduction-ready chart-local
algebraic induction step from the A2 repair report. Scope is the block identity
for a prefix diagonal block `fromBlocks C1 0 0 D` multiplied by the next
transformed layer `fromBlocks A1 A2 A3 A4`, under explicit determinant-unit
chart hypotheses for `C1` and `A1`.

Outcome: landed
`DLNFibre.DLN.Aoyagi.productReduction_chartLocalInductionStep_fromBlocks` in
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`, imported by the single-writer
aggregator. The theorem proves only the chart-local algebraic block identity:
left lower-left multiplier `-(D * A3 * (C1 * A1)⁻¹)`, right upper-right
multiplier `-(A1⁻¹ * A2)`, and residual block
`D * (A4 - A3 * A1⁻¹ * A2)`. It includes an identity-corner example showing
the determinant-unit chart hypotheses are inhabited, including zero-size
corners.

Controller verified targeted build, full `DLNFibre` build, `scripts/sorries`,
and `#print axioms` for the theorem. Xhigh hardener `Jason` and xhigh fidelity
reviewer `Huygens` passed the artifact at this narrow scope. Statement card:
`statement-card-a2-chart-local-induction-step.md`.

Still blocked: full Aoyagi Theorem 3 from source rank/neighborhood hypotheses,
through-layer basis/open-chart existence, target-product normalization via
Aoyagi Lemma 1, local analytic/ideal-germ invariance, regular-coordinate RLCT
additivity, and every final RLCT consequence.

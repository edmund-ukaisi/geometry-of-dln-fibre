# Thread 04 - blow-up certificate

Type: pen-and-paper/formalisation. Status: blocked.

## Task

Turn Aoyagi's recursive Case 1 / Case 2 blow-up bookkeeping into a formal
transition invariant or certificate, then prove the certificate matches the
coordinate substitutions.

## Output contract

- A finite state representation of the exponent/vector bookkeeping.
- Explicit source correspondence for every transition and terminal case.
- A completeness argument for the case split, with a decorrelated
  counterexample hunt before treating it as established.
- Lean implementation only after the certificate shape is stable.

## Controller notes

This is likely the crux. Build small infrastructure if it reduces proof risk.
Do not mimic prose geometry if a certificate gives a cleaner Lean target.

## 2026-06-18 check result

Draft reproduction: `reproduction-draft.md`. Independent checker:
`Copernicus`, saved at `reproduction-check.md`.

Status: not formalisation-ready. The certificate must first separate actual
layer widths `M^{(S+1)}` from prefix minima `M(S+1)`, repair the Case 1/2
transition updates, cover missing pivot charts, prove regularity/divisibility
for the `P` matrices, and replace the unstable termination measure.

## 2026-06-19 repair checkpoint

Repair report: `reproduction-repair-a4.md`.

Status: still blocked. The width split is now source-faithful: actual reduced
widths are `M^{(s)}`, while `M(S)` is the prefix minimum. Page-image inspection
and xhigh source scout `Russell the 2nd` confirm that Case 2 prints
`t_{S,J+1}^{(i)} = M^{(i+1)}` for `i < S` and
`M'_{S,J+1}=(M(S)-J)(M^{(S+1)}-J)`. The terminal exponent formula on PDF p. 22
uses actual widths `M^{(j)}`. Therefore the printed Case 2 vector gives
`(M^{(S)}-J)(M^{(S+1)}-J)` in the terminal formula, not the printed Case 2
increment, unless `M(S)=M^{(S)}`. Xhigh pen-and-paper scout `Hume the 2nd`
confirmed that replacing the earlier coordinates by prefix minima
`M(2),...,M(S)` repairs the arithmetic while keeping actual-width label
ranges. Do not start a full Lean transition theorem until this is explicitly
split into source-faithful and corrected-certificate statements.

Additional open obligations: all pivot charts, monomial divisibility for
`P`, recurrence-based interpretation of the `b'_i`/standalone-`u` algebra,
termination/off-by-one convention, and rectangular/boundary cases.

## 2026-06-19 Lean arithmetic split

Statement card: `statement-card-a4-terminal-exponent-split.md`.

Landed `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`, imported by
`lean/DLNFibre.lean`. This file proves the terminal-exponent arithmetic for
both the printed Case 2 vector and the prefix-minimum repaired vector:

- `terminalExponent_printedCase2Vector` gives
  `(M^(S)-J)(M^(S+1)-J)`.
- `terminalExponent_prefixCase2Vector` gives
  `(M(S)-J)(M^(S+1)-J)`.

This is deliberately not a blow-up transition theorem. It isolates the source
gap and gives a clean arithmetic target for any corrected certificate.

## 2026-06-19 Lean monomial divisibility

Statement card: `statement-card-a4-monomial-recurrence-divisibility.md`.

Xhigh pen-and-paper scout `McClintock the 2nd` confirmed that regularity of the
quotients `b'_i / b'_(J+1)` in the displayed `P` matrix reduces to a plain
monomial recurrence lemma.  Lean now proves that a recurrence
`b_(k+1)=step_k*b_k` has tail-product divisibility `b_a | b_b` for `a <= b`,
and that common multiplication by a pivot variable preserves this divisibility.
This still does not construct `P` or prove the matrix row-operation identity.

## 2026-06-19 Lean normalized `P` row operation

Statement card: `statement-card-a4-normalized-p-row-operation.md`.

Xhigh scout `Gauss the 2nd` reproduced the normalized row-operation algebra.
Lean now proves `weightedPivotBlockRowOp_mul_diagonal_mul`: in a pivot split
`Unit ⊕ lower`, if the `Q`-normalised block is `[1 0; x D]` and lower weights
satisfy `b_i=q_i*b0`, then the lower-unitriangular `P` matrix clears the lower
first column and leaves the lower-right block unchanged:

```text
P * diag(b0,b) * [1 0; x D] = diag(b0,b) * [1 0; 0 D].
```

This is independent of the Case 2 printed-vector mismatch and applies to both
displayed pivot branches after choosing one normalization for the common pivot
factor. It still does not prove the surrounding `Q` operation, pivot-chart
coverage, or the full transition invariant.

## 2026-06-19 Lean normalized `Q` column operation

Statement card: `statement-card-a4-normalized-q-operation.md`.

Xhigh scout `Franklin the 2nd` reproduced the source's normalized column
operation. Lean now proves `pivotPreQBlock_mul_pivotQ`: for a pivot split

```text
[ 1  y
  x  D ] * [ 1 -y
             0  I ] = [ 1  0
                        x  D - x*y ].
```

The inverse matrices `pivotQ` and `pivotQinv` are proved two-sided inverses,
and `pivotPreQBlock_mul_eq_postQ_mul_Qinv_mul` proves that replacing the
following factor by `Q^-1 C` preserves the local product. This applies to both
displayed pivot branches after normalizing the pivot entry to `1`. It still
does not prove pivot-chart coverage, exponent updates, or the full transition
invariant.

## 2026-06-19 Lean normalized pivot step

Statement card: `statement-card-a4-normalized-pivot-step.md`.

Lean now packages the local `Q` and `P` identities together. The bridge lemma
`pivotPostQBlock_eq_weightedPivotBlockMatrix` identifies the post-`Q` block
with the input shape required by the row-operation theorem. The combined
theorem `weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ`
then proves:

```text
P * diag(b0,b) * ([1 y; x D] * Q)
  = diag(b0,b) * [1 0; 0 D - x*y].
```

The product version
`weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul` is the algebraic
corollary with the following factor multiplied by `Q^-1`. This is still only a
normalized displayed matrix identity. It does not construct the pivot chart,
prove polynomial regularity/Jacobian facts, update exponents, cover all pivot
charts, or prove a transition invariant.

## 2026-06-19 Lean actual-width labels

Statement card: `statement-card-a4-actual-width-labels.md`.

Lean now records the label-range part of the width repair. `actualWidthLabel`
uses the source's actual range `1 <= k <= n_(s+1)`, while `prefixWidthLabel`
uses the narrower prefix-minimum range `1 <= k <= mu_(s+1)`.
`actualWidthLabel_not_prefixWidthLabel_of_prefixMinNat_lt_width` proves that
prefix-width labels strictly undercount actual labels whenever
`mu_(s+1) < n_(s+1)`. The Case 2 new-label lemmas then separate the actual
source-label bound `J+1 <= n_(S+1)` from the stronger continuation bound
`J+1 <= mu_(S+1)`.

The same checkpoint adds `correctedCase2PivotVector` and
`terminalExponent_correctedCase2PivotVector`, a natural-width wrapper around
the existing prefix-minimum terminal-exponent theorem.

This is finite bookkeeping only. It does not yet define the full corrected
vector invariant or prove any transition.

## 2026-06-19 Lean introduced labels

Statement card: `statement-card-a4-introduced-labels.md`.

Lean now defines `introducedLabel L n S J s k` for the source labels whose
exceptional variables have been introduced by state `(S,J)`: actual-width
labels with either `s < S` or `s = S` and `k <= J`. It proves introducedness is
monotone in `J`, that `(S,J+1)` is not introduced before the pivot advance, and
that `(S,J+1)` is introduced after the advance under the actual-width bound.
The prefix-bound corollary records that the source continuation condition
`J+1 <= mu_(S+1)` implies this label fact, without treating actual-width
validity as a continuation theorem.

This records the active-label domain for later vector/exponent assignments. It
does not assign those data or prove a transition.

## 2026-06-19 Lean corrected Case 2 vector minimum

Statement card: `statement-card-a4-corrected-case2-vector-minimum.md`.

Lean now proves the finite `\tilde t=J` fact for the corrected Case 2 vector.
`prefixMinNat_antitone` records that prefix minima only decrease as the prefix
grows. The component lemmas state that the corrected vector is `mu_(i+1)` for
`i<S` and `J` for `i>=S`. Therefore, under the state bound `J<=mu_S`,
`correctedCase2PivotVector_min_certificate` proves every total component is at
least `J` and the `S` component is exactly `J`. The theorem
`correctedCase2PivotVector_isLeast_valueSet_Icc` packages the same fact over
the source component range `1..L`, assuming `1<=S<=L`.

This uses the corrected prefix-minimum vector. It does not assert pairwise
comparability, assign vector data to every introduced label, or prove a
transition.

## 2026-06-19 Lean corrected Case 2 new-label certificate

Statement card: `statement-card-a4-corrected-case2-new-label-certificate.md`.

Lean now packages the corrected Case 2 new-label bookkeeping as the Prop-valued
certificate `CorrectedCase2NewLabelCertificate`. The certificate is deliberately
only for `(S,J+1)`: it records introducedness after the pivot advance, the
corrected terminal exponent formula, and the finite least-value fact for the
corrected prefix-minimum vector.

The primary theorem keeps the two hypotheses separate: actual source-label
validity uses `J+1 <= n_(S+1)`, while the least-value certificate uses the
state bound `J <= mu_S`. The corollary
`correctedCase2NewLabelCertificate_of_prefixBound` derives both facts from the
stronger continuation condition `J+1 <= mu_(S+1)`.

This is not a full vector invariant, transition theorem, or claim about the
PDF's printed Case 2 vector.

## 2026-06-19 Lean finite exponent-domain bookkeeping

Statement card: `statement-card-a4-finite-exponent-domain-bookkeeping.md`.

Lean now has `LabelExponentCertificate` for a single introduced label and
`IntroducedLabelExponentCertificates` for all labels introduced at a state.
The package records only finite terminal-exponent and least-value certificates.
It is not a chart invariant.

The domain-change lemmas `introducedLabel_succ_cases` and
`introducedLabel_succ_iff` prove that advancing from `(S,J)` to `(S,J+1)`
changes the introduced-label domain only at the possible new label
`(S,J+1)`. The extension lemmas then say: if old assignments are supplied as
unchanged and the new label has a certificate, the certificate package extends
to the larger introduced domain.

The corrected Case 2 new-label certificate supplies that one new-label input
under either separate actual/state bounds or the stronger continuation bound.
This remains domain-extension bookkeeping only; it does not prove old data is
unchanged by a chart or prove a blow-up transition.

## 2026-06-19 Lean Case 2 residual-block entries

Statement card: `statement-card-a4-case2-residual-block-entries.md`.

Lean now records the finite residual-block entry set for corrected Case 2:
rows `J+1..mu_S` and columns `J+1..n_(S+1)`. The membership theorem keeps the
prefix-minimum row bound and actual-width column bound explicit. Under the
continuation bound `J+1 <= mu_(S+1)`, the displayed source pivot
`(J+1,J+1)` belongs to this entry set.

This records candidate selected entries in the residual-block center only. It
does not construct the selected-entry charts or prove coverage of the
non-displayed charts.

## 2026-06-19 Lean selected-entry substitution scaffold

Statement card: `statement-card-a4-selected-entry-substitution.md`.

Lean now has a generic finite algebra scaffold `selectedEntryChartMap` for a
selected generator of a center: the selected generator maps to `u`, while every
other center generator maps to `u` times a residual coordinate. It proves the
selected value, the non-selected value, divisibility by `u`, and occurrence of
the pivot value in the finite value set.

The Case 2 specialization combines this generic scaffold with the already
proved residual-block entry set: under continuation, Aoyagi's displayed pivot
`(J+1,J+1)` gives the value `u` in the residual-block selected-entry value
set.

This is finite algebra only. It does not construct blow-up charts, prove chart
coverage, prove non-displayed selected-entry transition formulas, or establish
regularity/Jacobian facts.

## 2026-06-19 Lean arbitrary selected-entry center facts

Statement card: `statement-card-a4-arbitrary-selected-entry-center-facts.md`.

Lean now specializes the finite map `selectedEntryChartMap` to arbitrary
selected generators in the Case 1 center and arbitrary selected entries in the
Case 2 residual-block center, under the hypothesis that the selected pivot
already belongs to that finite center. The Case-specific facts say that `u`
occurs in the finite substitution value set, witnessed by the pivot, and that
every transformed finite-center generator is divisible by `u`.

This is a chart-index bookkeeping step toward a family of selected-entry
charts. It does not construct an affine blow-up atlas, prove non-displayed
transition formulas, establish row/column permutation symmetry, or prove chart
coverage.

## 2026-06-19 Lean generic pivot-first `Q/P` algebra bridge

Reproduction: `reproduction-arbitrary-pivot-q-p-bridge-a4.md`.
Statement card: `statement-card-a4-generic-pivot-first-q-p-bridge.md`.

Lean now proves the generic algebraic bridge from an arbitrary normalised
matrix pivot to the already-formalised top-left `Q/P` identities. The new
`pivotFirstMatrix` API puts a chosen row and column pivot first, names the
lower-left/upper-right/lower-right pieces, and proves that pivot entry `1`
identifies the reindexed matrix with `pivotPreQBlock`. The two pivot-first
`weightedPivotBlockRowOp...` corollaries apply the existing `Q/P` clearing
identities under the explicit quotient-witness hypothesis
`forall i, b i = q i * b0`.

This is pure finite matrix algebra. Aoyagi displays only the top-left pivot
chart in Case 1(2) and Case 2; this checkpoint does not prove non-displayed
selected-entry charts, coordinate transport for following factors and weights,
quotient witnesses for arbitrary Aoyagi pivot rows, chart coverage, exponent
updates, or a transition invariant.

## 2026-06-19 Lean pivot-row quotient witnesses

Reproduction: `reproduction-pivot-row-weight-quotients-a4.md`.
Statement card: `statement-card-a4-pivot-row-quotient-witnesses.md`.

Lean now proves the generic quotient-witness layer needed by the `P`
row-operation theorem. The core theorem
`exists_right_quotients_of_forall_dvd` turns divisibility of every lower-row
weight by the pivot-row weight into witnesses `q` satisfying
`weight i = q i * weight_pivot`. Equality, equality-or-divisibility, constant
row weights, later monomial recurrence terms, equality-or-later recurrence
terms, and common pivot multiplication all have corresponding witness
wrappers.

The bridge
`exists_weightedPivotBlockRowOp_mul_diagonal_mul_of_forall_dvd` packages this
with the existing normalised `P` matrix identity. This still assumes that row
weights are already in pivot-first coordinates and does not prove Aoyagi's
selected-entry charts, coordinate transport, arbitrary-pivot row hypotheses,
chart coverage, exponent updates, or a transition invariant.

## 2026-06-19 Lean pivot-first existential `Q/P` wrappers

Reproduction: `reproduction-pivot-first-existential-q-p-a4.md`.
Statement card: `statement-card-a4-pivot-first-existential-q-p.md`.

Lean now connects the pivot-first `Q/P` algebra bridge to the quotient-witness
layer existentially. The new `exists_pivotFirstQP...` theorems take
divisibility or equality-or-later recurrence hypotheses and choose the `q`
function needed by the normalised row operation. Both the local `...mul_pivotQ`
identity and the product-preservation `...mul` identity are packaged, including
the common-pivot-multiple recurrence variant matching the displayed `b'_i =
u*b_i` shape.

The same checkpoint adds small `Case1FirstJumpHypotheses` membership
corollaries for the displayed pivot and row-strip entries. This is still
conditional algebra in already-normalised, pivot-first coordinates. It does not
prove selected-entry chart construction, coordinate/weight transport,
Aoyagi-specific arbitrary row hypotheses, chart coverage, exponent updates, or
a transition invariant.

## 2026-06-19 Lean Case 2 displayed pivot `Q/P`

Reproduction: `reproduction-case2-displayed-pivot-q-p-a4.md`.
Statement card: `statement-card-a4-case2-displayed-pivot-q-p.md`.

Lean now instantiates the pivot-first product `Q/P` identity for the
source-displayed Case 2 top-left pivot `d_(J+1,J+1)`. The new finite row and
column index types record the corrected residual-block row range `J+1..mu_S`
and actual-width column range `J+1..n_(S+1)`. Under the source continuation
bound, `case2DisplayedPivotRow` and `case2DisplayedPivotCol` package the
displayed pivot indices.

The selected-entry substitution is split into a selected variable times a
normalised matrix with pivot entry `1`, and
`exists_case2DisplayedQP_mul_of_flat_weights` applies the existing
pivot-first existential `Q/P` wrapper under flat displayed residual-row
weights. This is the displayed Case 2 local algebra only. It does not prove
arbitrary selected-entry charts, affine atlas coverage, full source-variable
transport, exponent updates, or a transition invariant.

## 2026-06-19 Lean pivot-first following-factor transport

Reproduction: `reproduction-pivot-first-following-factor-a4.md`.
Statement card: `statement-card-a4-pivot-first-following-factor.md`.

Lean now names the following factor in pivot-first column coordinates as
`pivotFirstFollowingFactor` and proves
`pivotFirstMatrix_mul_pivotFirstFollowingFactor`: multiplying a pivot-first
residual block by this reindexed following factor is the same as reindexing the
pre-reindexed product in the pivot-first row order.

This is the finite matrix transport behind the displayed replacement
`C' = Q^{-1} C`, but it remains pure reindexing algebra. It does not construct
source coordinates, prove regularity/Jacobian facts, prove chart coverage, or
update exponents.

## 2026-06-19 Lean pivot-first diagonal weight transport

Reproduction: `reproduction-pivot-first-diagonal-weights-a4.md`.
Statement card: `statement-card-a4-pivot-first-diagonal-weights.md`.

Lean now proves `weightedPivotDiagonal_eq_pivotFirst_diagonal`: the split
diagonal matrix used by the pivot-first `P` operation is exactly the original
row-weight diagonal matrix reindexed by `pivotFirstIndexEquiv` on rows and
columns.

This transports supplied row weights into pivot-first coordinates. It does not
prove Aoyagi's recurrence flatness, quotient witnesses, selected-entry chart
construction, coordinate regularity, exponent updates, or transition
invariants.

## 2026-06-19 Lean Case 2 pivot-first following-factor package

Reproduction: `reproduction-case2-pivot-first-following-factor-a4.md`.
Statement card: `statement-card-a4-case2-pivot-first-following-factor.md`.

Lean now packages the source-displayed Case 2 top-left `Q/P` theorem with a
residual following factor supplied before pivot-first reindexing. The aliases
`case2DisplayedNormalizedMatrix` and `case2DisplayedFollowingFactor` name the
displayed normalised residual matrix and the following factor reindexed into
pivot-first column coordinates. The theorem
`case2DisplayedNormalizedMatrix_mul_followingFactor` proves the finite
multiplication transport, and
`exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights` applies
the displayed flat-row-weight `Q/P` identity with that reindexed following
factor.

This is still local finite algebra for the displayed chart. It does not prove
the full source-coordinate construction, arbitrary-pivot chart coverage,
regularity/Jacobian facts, exponent updates, or transition invariants.

## 2026-06-19 Lean Case 2 source-substitution factor

Reproduction: `reproduction-case2-source-substitution-factor-a4.md`.
Statement card: `statement-card-a4-case2-source-substitution-factor.md`.

Lean now proves the finite source-substitution factoring step for the displayed
Case 2 selected-entry chart. The generic theorem
`diagonal_mul_selectedEntrySubstitutionMatrix` proves
`diag(weight) * sourceSubstitutedBlock = diag(u * weight) * normalisedBlock`.
The displayed wrappers `case2DisplayedSubstitutionMatrix`,
`case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst`, and
`case2Displayed_diagonal_mul_substitutionMatrix_mul_followingFactor` transport
this equality into the pivot-first/following-factor coordinates used by the
existing displayed `Q/P` theorem. The wrapper
`exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights` applies that
`Q/P` theorem after the source factor has been absorbed into row weights.

This counts the selected variable once, as `newWeight = u * oldWeight`. It
does not prove the full source blockdiag identity, arbitrary-pivot chart
coverage, regularity/Jacobian facts, exponent updates, or transition
invariants.

## 2026-06-19 Lean Case 2 transported following factor and monomial rows

Reproduction: `reproduction-case2-transported-following-factor-monomial-a4.md`.
Statement card: `statement-card-a4-case2-transported-following-factor-monomial.md`.

Lean now names the displayed following-factor update
`case2DisplayedTransportedFollowingFactor`, defined as `Q^{-1}` times the
pivot-first following factor. It also names the residual source row projection
`case2ResidualRowLevel` and proves every displayed residual row satisfies
`J+1 <= rowLevel`.

The theorem
`exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec`
applies the pivot-first `Q/P` product identity when the updated row weights are
`u * monomialRec step rowLevel`. The quotient witnesses for the `P` matrix are
chosen from recurrence divisibility and the row-level lower bound.

This is still local finite algebra. It assumes the row weights have already
been represented in the row-index recurrence form and does not prove Aoyagi's
source recurrence, full source blockdiag identity, arbitrary-pivot chart
coverage, regularity/Jacobian facts, exponent updates, or transition
invariants.

## 2026-06-19 Lean Case 2 source-block tail lift

Reproduction: `reproduction-case2-source-block-tail-lift-a4.md`.
Statement card: `statement-card-a4-case2-source-block-tail-lift.md`.

Lean now proves the finite block-matrix step that lifts an already-proved
displayed Case 2 residual-tail identity through unchanged top rows. The generic
helper `verticalBlock` stacks a top following-factor block over a residual-tail
following-factor block. The theorem `fromBlocks_mul_verticalBlock` proves that
`fromBlocks A_top 0 0 L_tail` acts as `A_top` on the top rows and `L_tail` on
the residual rows, and `fromBlocks_mul_verticalBlock_eq_of_tail` lifts any
tail identity `L_tail*C_tail = R_tail*C_tail'`.

The displayed wrappers
`exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_flat_weights`
and
`exists_case2DisplayedQP_verticalBlock_transportedFollowingFactor_of_rowIndex_monomialRec`
apply this to the source-substitution tail theorem and to the row-index
monomial-recurrence transported-following-factor theorem. The top block is
unchanged except for the same supplied `A_top` on both sides.

This closes only the finite "reattach unchanged top rows" bookkeeping gap. It
does not prove arbitrary-pivot charts, source chart regularity/Jacobian facts,
source recurrence-to-row-weight production, exponent updates, transition
invariants, termination, normal crossings, RLCT extraction, or the printed
Case 2 vector repair.

## 2026-06-19 Lean Case 2 gap row weights

Reproduction: `reproduction-case2-gap-row-weights-a4.md`.
Statement card: `statement-card-a4-case2-gap-row-weights.md`.

Lean now proves the displayed Case 2 row-weight flatness consequence of an
explicit recurrence gap. The generic lemmas
`monomialTail_eq_one_of_forall_eq_one` and
`monomialRec_eq_of_step_eq_one_on_Ico` say that a monomial recurrence is
constant across an interval whose step factors are all `1`. The displayed
wrapper `case2ResidualRow_monomialRec_eq_pivot_of_gap` applies this
to residual rows `J+1..prefixMinNat n S`.

The theorem
`exists_case2DisplayedQP_mul_sourceSubstitution_of_gap_monomialRec` then feeds
that flatness into the existing displayed source-substitution `Q/P` theorem,
with row weights `monomialRec step rowLevel` and the selected variable counted
once as `u * oldWeight`.

This is a conditional row-weight bridge. It assumes the Case 2 gap as
`step k = 1` for `J+1 <= k < prefixMinNat n S`; it does not prove that the
recursive state establishes the gap, arbitrary-pivot chart coverage, chart
regularity/Jacobian facts, exponent updates, transition invariants,
termination, normal crossings, RLCT extraction, or the printed Case 2 vector
repair.

## 2026-06-19 Lean Case 2 label-product gap

Reproduction: `reproduction-case2-label-product-gap-a4.md`.
Statement card: `statement-card-a4-case2-label-product-gap.md`.

Lean now models a recurrence factor as a finite product over supplied labels at
a given level. The definition `levelProductStep labels level var r` multiplies
the variables in `labels` whose `level` equals `r`. The lemmas
`levelProductStep_eq_one_of_forall_ne` and `levelProductStep_eq_one_of_gap`
prove that a finite label gap forces the corresponding recurrence factor to be
`1`.

The displayed wrapper
`case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap` combines this with
the previous Case 2 gap-row-weight bridge. The theorem
`exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap` then applies the
displayed source-substitution `Q/P` theorem when row weights are the monomial
recurrence generated by this finite label-product step.

This still assumes the finite `labels` set is the one used by the recurrence
factor; it does not prove that the supplied labels are exactly Aoyagi's
introduced-label set at the recursive state. The bridge keeps displayed
residual rows `J+1..mu_S` distinct from actual-width residual columns
`J+1..n_(S+1)` and counts the selected variable once in `u*b_i`. Review artifact:
`review-case2-label-product-gap-a4.md`. It does not prove the recursive
invariant establishes the gap, arbitrary-pivot chart coverage, chart
regularity/Jacobian facts, exponent updates, transition invariants, termination,
normal crossings, RLCT extraction, or the printed Case 2 vector repair.

## 2026-06-19 Lean Case 2 introduced-label gap

Reproduction: `reproduction-case2-introduced-label-gap-a4.md`.
Statement card: `statement-card-a4-case2-introduced-label-gap.md`.
Review artifact: `review-case2-introduced-label-gap-a4.md`.

Lean now instantiates the previous finite label-product bridge over the finite
domain of labels introduced at state `(S,J)`. The definitions
`actualWidthLabelFinset` and `introducedLabelFinset` enumerate actual-width
source labels and the already-modeled `introducedLabel` predicate; the
membership lemmas identify these finite domains with the Prop-valued predicates.

The new wrappers
`levelProductStep_introducedLabelFinset_eq_one_of_gap`,
`case2ResidualRow_introducedLabel_monomialRec_eq_pivot_of_gap`, and
`exists_case2DisplayedQP_mul_sourceSubstitution_of_introducedLabelGap` prove the
Case 2 label-product row-weight bridge over this introduced-label domain.

This removes the arbitrary supplied-label domain, but it still assumes the
Nat-valued `level` map is Aoyagi's current `tilde_t`, the variable map is the
source recurrence variable assignment, the introduced-label Case 2 gap holds,
and row weights are generated by this recurrence. It does not prove the
recursive invariant, the source's Case 2 comparability sentence, arbitrary-pivot
chart coverage, chart regularity/Jacobian facts, exponent updates, transition
invariants, termination, normal crossings, RLCT extraction, or the printed Case
2 vector repair.

## 2026-06-19 Lean Case 2 recurrence-state interface

Reproduction: `reproduction-case2-recurrence-state-interface-a4.md`.
Statement card: `statement-card-a4-case2-recurrence-state-interface.md`.
Review artifact: `review-case2-recurrence-state-interface-a4.md`.

Lean now packages the introduced-label recurrence data used by the Case 2
row-weight bridge. `IntroducedLabelRecurrenceState` stores only the source-level
map and variable map; `step`, `weight`, and `case2ResidualRowWeight` are derived
from `introducedLabelFinset`, not independent fields. The package includes a
Nat-valued Case 2 gap predicate, an integer least-value gap bridge through
the equality-only `IntroducedLabelLevelInvariants`, residual-row weight flatness lemmas, and a
displayed source-substitution `Q/P` wrapper
`exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap`.

This is still an assumption interface. It does not prove that Aoyagi's
transition produces the state, that the Case 2 gap holds, or that the source's
comparability sentence follows. It also does not resolve arbitrary pivots,
regularity/Jacobian facts, exponent updates, transition invariants, termination,
normal crossings, RLCT extraction, or the printed Case 2 vector repair.

## 2026-06-19 Lean Case 2 recurrence-weight update

Reproduction: `reproduction-case2-recurrence-weight-update-a4.md`.
Statement card: `statement-card-a4-case2-recurrence-weight-update.md`.
Review artifact: `review-case2-recurrence-weight-update-a4.md`.

Lean now proves the conditional recurrence-weight update behind Aoyagi's
displayed Case 2 line `b'_i = u*b_i`. The finite-domain lemma
`introducedLabelFinset_succ_eq_insert` proves that advancing from `(S,J)` to
`(S,J+1)` adds exactly `(S,J+1)` to the introduced-label finite set, when that
label is source-valid. The finite product lemmas
`levelProductStep_insert_eq_mul_of_new` and `levelProductStep_insert_eq_of_ne`,
combined with `monomialRec_eq_mul_of_step_eq_mul_at`, show that a supplied
post-state with the new label at level `J` and variable `u` has
`post.weight i = u * pre.weight i` for every `J+1 <= i`.

The source-facing theorem
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul`
packages this against the corrected new-label certificate. The residual-flat
consequence
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap`
says that if the old state satisfies the Case 2 gap, then the supplied
successor weights are flat across the old displayed residual-row range after
common multiplication by `u`.

This is still recurrence bookkeeping. It assumes the supplied post-state keeps
old introduced-label recurrence data unchanged and assigns the new label data
as specified; it does not prove that the blow-up chart produces that post-state.
It also does not repair the printed Case 2 vector mismatch, prove source
comparability, justify double-counting the standalone outside `u`, or prove
chart coverage, regularity/Jacobian facts, exponent updates, transition
invariants, termination, normal crossings, or RLCT extraction.

## 2026-06-19 Lean Case 2 successor source substitution

Reproduction: `reproduction-case2-successor-source-substitution-a4.md`.
Statement card: `statement-card-a4-case2-successor-source-substitution.md`.
Review artifact: `review-case2-successor-source-substitution-a4.md`.

Lean now connects the displayed Case 2 source-substitution algebra to supplied
successor recurrence weights. The new theorem
`CorrectedCase2NewLabelCertificate.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`
rewrites the pivot-first equality
`diag(pre row weights) * D_J = diag(u*pre row weights) * D'_J` using a supplied
post-state satisfying the recurrence update, so the right-side diagonal is
written as `post.weight (J+1)` and `post.weight rowLevel`.

The `Q/P` wrapper
`CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`
does the same rewrite inside the existing displayed source-substitution `Q/P`
identity under the old Case 2 gap. This is a source-facing handoff between
Aoyagi's displayed `D_J = uD'_J` and `b'_i=u b_i` lines; it is not chart
production, arbitrary-pivot coverage, regularity/Jacobian, exponent update,
transition invariant, normal-crossing, RLCT extraction, source comparability,
or a repair of the printed Case 2 vector mismatch.

## 2026-06-19 Lean Case 2 supplied post-data package

Reproduction: `reproduction-case2-supplied-post-data-a4.md`.
Statement card: `statement-card-a4-case2-supplied-post-data.md`.
Review artifact: `review-case2-supplied-post-data-a4.md`.

Lean now packages the repeated supplied recurrence post-data for a Case 2
`J`-advance as
`IntroducedLabelRecurrenceState.Case2SuppliedPostData`. The package records
only old-label level/variable agreement and the new label `(S,J+1)` having
level `J` and variable `u`. It deliberately does not contain the old Case 2
gap, the displayed pivot bounds, or the corrected new-label certificate.

The concrete successor `pre.case2Succ u` satisfies the package. The package
also has a recurrence-weight method under actual source-validity, a residual
flatness method under the old Case 2 gap, and corrected-certificate wrappers
for the recurrence update, residual flatness, displayed pivot-first
source-substitution, and displayed `Q/P` handoff. This removes repeated
hypothesis lists without asserting chart production, arbitrary-pivot coverage,
regularity/Jacobian facts, exponent updates, transition invariants, normal
crossings, RLCT extraction, source comparability, or the printed Case 2 vector
repair.

## 2026-06-19 Lean Case 2 exponent update data

Reproduction: `reproduction-case2-exponent-update-data-a4.md`.
Statement card: `statement-card-a4-case2-exponent-update-data.md`.
Review artifact: `review-case2-exponent-update-data-a4.md`.

Lean now has a concrete update-data wrapper for corrected Case 2
exponent-domain extension:
`IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_updateData_of_prefixBound`.
It extends an old introduced-label exponent certificate package from `(S,J)` to
`(S,J+1)` using total assignment overrides that change only the new label
`(S,J+1)` to the corrected Case 2 vector, numerator, and least value.

This is intentionally independent of `Case2SuppliedPostData`: recurrence
`level/var` post-data does not imply old exponent vectors, numerators, or least
values are unchanged. The wrapper is only syntactic exponent-domain
bookkeeping around the existing corrected new-label certificate. It is not
chart production, exponent transition invariance, source comparability,
arbitrary-pivot transport, normal crossing, RLCT extraction, or a claim that
the corrected vector is the PDF's printed vector.

## 2026-06-19 Lean Case 1 center generators

Statement card: `statement-card-a4-case1-center-generators.md`.

Lean now has finite symbols for the Case 1 center after the old exceptional
variable has been chosen externally. The type `Case1CenterGenerator` is
`Unit ⊕ (Nat × Nat)`: the `Unit` branch is the chosen old exceptional
generator, and the right branch is a row-strip entry `d_ij`. The row strip is
`J+1..J+J1` by `J+1..n_(S+1)`, with actual active column width.

Lean proves row/column/entry membership criteria, membership of the chosen old
generator, membership of any row-strip entry, and membership of Aoyagi's
displayed pivot entry under `1 <= J1` and `J+1 <= n_(S+1)`. It also specializes
the generic selected-entry substitution value-set lemma to the selected-old and
displayed-pivot choices.

This remains finite generator bookkeeping. It does not encode the old label's
validity, level, minimality, or comparability, and it does not prove row-strip
source validity, chart coverage, or transition formulas.

## 2026-06-19 Lean Case 1 row-strip containment

Statement card: `statement-card-a4-case1-row-strip-containment.md`.

Lean now proves the finite containment that was left explicit in the Case 1
center scaffold: if `J+J1 <= mu_S`, then the Case 1 row strip
`J+1..J+J1` lies in the residual-block row range `J+1..mu_S`. The column ranges
are definitionally the same actual-width range `J+1..n_(S+1)`, so the row-strip
entries are contained in the residual-block entry set under the same row bound.

It also proves that the displayed pivot `(J+1,J+1)` lies in the residual-block
entry set under `1 <= J1`, `J+J1 <= mu_S`, and `J+1 <= n_(S+1)`.

This is finite entry-set containment only. It does not prove the Case 1
first-jump hypotheses, old-label hypotheses, chart coverage, or transition
formulas.

## 2026-06-19 Lean Case 1 first-jump hypotheses

Statement card: `statement-card-a4-case1-first-jump-hypotheses.md`.

Lean now packages the finite source hypotheses for a chosen Case 1 old label:
`1 <= J1`, strict nonterminal boundary `J+J1 < mu_S`, selected introduced
label `(s,k)`, selected level `J+J1`, no introduced label in the intermediate
gap `J+1..J+J1-1`, and componentwise minimality on `1..L` among labels at the
selected level.

The strict boundary derives the row-strip bound `J+J1 <= mu_S`, so the package
also specializes the existing row-strip containment lemmas. It proves the
selected level is above `J`, casts the selected-level equality to the integer
convention, and records the immediate self-minimality specialization.

This is still only finite bookkeeping. It does not prove the recurrence
equalities or inequality for the `b_i`, construct or prove existence of the
minimal selected label, relate `level` to certificate `leastValue`, prove the
flat-tail/old-minimum hypotheses, tie the anonymous center generator to
`(s,k)`, or give chart coverage or a transition invariant.

## 2026-06-19 Lean Case 1 same-domain lower-tail update

Statement card: `statement-card-a4-case1-same-domain-lower-tail-update.md`.

Lean now proves the conditional package-level bookkeeping for the Case 1(1)
selected-old-variable branch. First, `updateSelected` replaces one introduced
label certificate inside `IntroducedLabelExponentCertificates` while carrying
all other introduced labels by explicit unchanged-data hypotheses. Second,
`Case1FirstJumpHypotheses.lowerTailVector_labelExponentCertificate` applies the
one-label lower-tail transformer to the selected label when `leastValue =
level` and `FlatTailFromPred` are supplied. Finally,
`case1_selectedLowerTail_sameDomain` combines these into a same-state package
update at `(S,J)`.

The update assumes the selected post vector, numerator, and least value:
`lowerTailVector`, numerator increment `J1*(n_(S+1)-J)`, and least value `J`.
It also assumes non-selected introduced labels are unchanged. This is not a
chart theorem: it does not prove the chart produces those post assignments,
does not prove `b'_i` recurrence bookkeeping, does not use minimality for
comparability or termination, and does not extend the introduced-label domain.

## 2026-06-19 Lean selected-label update data

Statement card: `statement-card-a4-selected-label-update-data.md`.

Lean now has total assignment overrides for one selected label:
`updateSelectedLabelVector` and `updateSelectedLabelScalar`. They rewrite to
the selected post-data at `(s0,k0)` and to the old assignment at every label
different from `(s0,k0)`.

The convenience theorem `case1_selectedLowerTail_updateData` applies the
same-domain Case 1 lower-tail certificate update directly to these overrides.
This removes six mechanical post-data equality hypotheses. It is still only
bookkeeping: values outside the introduced-label domain are formal, and the
helpers do not prove that a chart produces the overrides.

## 2026-06-19 Lean level/tail invariant bridge

Statement card: `statement-card-a4-level-tail-invariant-bridge.md`.

Lean now packages the conditional bridge obligations needed by the selected
Case 1 lower-tail update. `IntroducedLabelLevelTailInvariants` assumes
`leastValue=level` for every introduced label and assumes `FlatTailFromPred`
only for introduced labels above the current pivot, `J < level`. This avoids
the false stronger claim that all introduced labels have flat predecessor
tails.

The corollary `case1_selectedLowerTail_of_levelTailInvariants` applies the
selected-label update-data theorem using this bridge. The selected label is
introduced by `Case1FirstJumpHypotheses`, and it is above the pivot by
`lt_selectedLevel`.

This is not a proved invariant or a preservation theorem. The bridge remains
an assumption package, excludes the `S=1` boundary in the downstream update,
and does not prove chart-produced post-data, `b'_i` bookkeeping, or transition
coverage.

## 2026-06-19 Lean Case 1 tail exponent increment

Statement card: `statement-card-a4-case1-tail-exponent-increment.md`.

Lean now proves the terminal-exponent arithmetic for lowering a flat tail.
For a vector `T` that is flat at value `h` from `S-1` through `L`, with
`2 <= S <= L`, `lowerTailVector T S J` changes the terminal exponent by
`(h-J)(n_(S+1)-J)`. The source-shaped corollary takes `h=J+J1` and gives the
Case 1 increment `J1(n_(S+1)-J)`.

The same checkpoint now records component and finite least-value bookkeeping
for `lowerTailVector`, plus `FlatTailFromPred` and a one-label transformer
`LabelExponentCertificate.lowerTailVector_of_flatFromPred_add`. The
transformer re-certifies an already introduced label at the same state; it
requires the old certificate to have least value `J+J1` and the comparison
`J <= J+J1`.

This is only arithmetic. The flat-tail hypothesis is explicit and must be
supplied by a later corrected invariant; it is not inferred from the Case 1
level condition alone. It is not an all-label/domain transition. The boundary
exclusions `S=1` and `S>L` are real.

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

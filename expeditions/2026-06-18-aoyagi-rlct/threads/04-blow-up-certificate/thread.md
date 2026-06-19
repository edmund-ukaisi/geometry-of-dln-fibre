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

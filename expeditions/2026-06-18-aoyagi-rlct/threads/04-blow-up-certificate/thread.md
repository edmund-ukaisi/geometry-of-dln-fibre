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

## 2026-06-20 Lean Case 2 printed mismatch boundary

Reproduction:
`reproduction-case2-printed-mismatch-boundary-a4.md`.
Statement card:
`statement-card-a4-case2-printed-mismatch-boundary.md`.

Lean now records the exact boundary where the PDF's printed Case 2 vector can
match the prefix-minimum exponent formula. The new theorem
`terminalExponent_printedCase2Vector_sub_prefixFormula` proves the difference

```text
E(T_print) - (M(S)-J)(M^(S+1)-J)
  = (M^(S)-M(S))(M^(S+1)-J).
```

The theorem `terminalExponent_printedCase2Vector_eq_prefixFormula_iff`
characterizes equality by the two cases `M^(S)=M(S)` or `M^(S+1)=J`.
The continuation-bound corollary
`terminalExponent_case2Printed_ne_corrected_of_prefixDrop_of_cont`
then says that under `J+1 <= M(S+1)`, where `M(S+1)` is the prefix minimum,
and a genuine prefix-width drop `M(S)<M^(S)`, the printed vector and
corrected prefix-minimum vector have different terminal exponents.

This is still not a Case 2 transition theorem. It does not prove an erratum,
reachable-state equal-width invariant, chart construction, pivot coverage,
regularity, Jacobians, normal crossings, RLCT extraction, or termination.

## 2026-06-20 Lean Case 2 supplied source-selected pivot boundary

Reproduction:
`reproduction-case2-supplied-source-selected-pivot-boundary-a4.md`.
Statement card:
`statement-card-a4-case2-supplied-source-selected-pivot-boundary.md`.
Review artifact:
`review-case2-supplied-source-selected-pivot-boundary-a4.md`.

Lean now packages a supplied boundary for a source-selected Case 2
residual-block pivot. A supplied source pair
`p in case2ResidualBlockPivotEntries n S J` is combined with the
source-coordinate selected-pair wrapper, the supplied Case 2 chart-family
boundary, corrected exponent post-data, recurrence post-data, finite
selected-entry principalization, and source-selected arbitrary-pivot `Q/P`
transport.

This is a supplied source-selected pivot boundary. It does not prove chart
coverage, source-displayed non-top-left charts, chart production, regularity or
transition regularity from coordinates, chart-produced post-data, a Case 2
transition invariant, normal crossings, RLCT extraction, termination, or repair
of the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed concrete-update boundary

Reproduction:
`reproduction-case2-displayed-concrete-update-boundary-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-concrete-update-boundary.md`.
Review artifact:
`review-case2-displayed-concrete-update-boundary-a4.md`.

Lean now names the displayed top-left Case 2 supplied boundary. The
continuation bound supplies membership of Aoyagi's displayed pivot
`(J+1,J+1)` in the residual-block center, and the boundary projects to the
source-selected boundary at that pivot. A concrete constructor chooses
`post = pre.case2Succ u` for recurrence data and
`Case2CorrectedExponentPostData.updateSelected` for the corrected exponent
post-data.

This removes arbitrary recurrence/exponent post-data fields only by choosing
concrete assignment functions. It still does not prove the affine chart
produces those assignments, and it does not prove chart coverage,
non-top-left source-displayed charts, coordinate regularity, Jacobians, normal
crossings, RLCT extraction, termination, a full Case 2 transition invariant,
or repair of the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed source-chart map

Reproduction:
`reproduction-case2-displayed-source-chart-map-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-source-chart-map.md`.
Review artifact:
`review-case2-displayed-source-chart-map-a4.md`.

Lean now names the source-coordinate displayed top-left Case 2 chart map. The
map sends `(J+1,J+1)` to the selected variable `u` and sends every other
source residual-block entry to `u` times its residual coordinate. Restricting
this source map to residual rows `J+1..M(S)` and actual-width residual columns
`J+1..M^(S+1)` recovers the existing displayed selected-entry substitution
matrix. The bridge theorem
`case2Displayed_source_pair_eq_pivot_iff` handles the only dependent-index
bookkeeping: equality of raw source pairs is equivalent to equality with the
displayed pivot in residual-row/column subtype coordinates.

The same checkpoint names the source normalised block, the source substituted
block, and the source transported following factor `Q^-1 C`, then rewrites the
displayed supplied boundary's `Q/P` identity in these source-chart block
names.

This is source-coordinate chart-map algebra only. It does not prove chart
coverage, non-top-left source-displayed formulas, chart-produced recurrence or
exponent post-data, coordinate regularity, Jacobians, normal crossings, RLCT
extraction, termination, a full transition invariant, or repair of the printed
Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed center count

Reproduction:
`reproduction-case2-displayed-center-count-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-center-count.md`.
Review artifact:
`review-case2-displayed-center-count-a4.md`.

Lean now proves the finite coordinate count for Aoyagi's displayed Case 2
residual-block center. The residual rows `J+1..M(S)` have cardinality
`M(S)-J`, the actual-width residual columns `J+1..M^(S+1)` have cardinality
`M^(S+1)-J`, and the selected residual-block coordinate set has cardinality

```text
(M(S)-J)(M^(S+1)-J).
```

The named integer expression `correctedCase2NewLabelNumerator` is proved equal
to this coordinate count under explicit row/column bounds and under the
displayed continuation bound. This supports the corrected prefix-minimum Case
2 scalar update as an elementary selected-coordinate count.

This is not a center-dimension theorem, Jacobian exponent, chart-produced
exponent update, or transition theorem. It does not prove chart coverage,
coordinate regularity, normal crossings, RLCT extraction, termination, or
repair of the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 corrected post-data center-count projection

Reproduction:
`reproduction-case2-corrected-postdata-center-count-a4.md`.
Statement card:
`statement-card-a4-case2-corrected-postdata-center-count.md`.
Review artifact:
`review-case2-corrected-postdata-center-count-a4.md`.

Lean now projects the supplied corrected Case 2 exponent post-data to the
displayed residual-block coordinate count. The generic post-data projection
`Case2CorrectedExponentPostData.numerator_new_eq_correctedNumerator` says the
new label `(S,J+1)` receives the corrected numerator
`correctedCase2NewLabelNumerator n S J`; under displayed continuation,
`Case2CorrectedExponentPostData.numerator_new_eq_card_of_cont` identifies that
integer with the cardinality of `case2ResidualBlockPivotEntries n S J`.
The source-selected and displayed supplied boundary packages export the same
projection as `numerator_new_eq_correctedNumerator` and
`numerator_new_eq_card`.

This is supplied corrected exponent bookkeeping only. It does not prove that
the affine chart produces the post-data, and it is not a Jacobian exponent,
volume-form calculation, chart coverage theorem, coordinate-regularity theorem,
normal-crossing certificate, RLCT extraction, termination theorem, transition
invariant, or repair of the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed source-chart principalization

Reproduction:
`reproduction-case2-displayed-source-chart-principalization-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-source-chart-principalization.md`.
Review artifact:
`review-case2-displayed-source-chart-principalization-a4.md`.

Lean now exposes finite-center principalization in the names of the displayed
Case 2 source-coordinate chart map. The source-chart map has `u` as a
transformed value at the displayed pivot `(J+1,J+1)`, every transformed
finite residual-block center value is divisible by `u`, and the transformed
finite center values generate `Ideal.span {u}`. The displayed supplied
boundary package exports the same value, divisibility, and finite ideal
principalization projections.

This principalizes only the finite residual-block center ideal for Aoyagi's
displayed top-left pivot. It is not arbitrary-pivot source chart data, not the
loss/Kullback ideal or an analytic germ, and not chart production, atlas
coverage, coordinate regularity, Jacobian/volume arithmetic, normal crossings,
RLCT extraction, termination, a transition invariant, or repair of the printed
Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed successor gap projections

Reproduction:
`reproduction-case2-displayed-successor-gap-projections-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-successor-gap-projections.md`.
Review artifact:
`review-case2-displayed-successor-gap-projections-a4.md`.

Lean now exposes successor invariant facts directly from the displayed
top-left Case 2 supplied boundary. The source-selected supplied boundary had
already proved, from supplied recurrence post-data and corrected exponent
post-data, the post-state level/least-value bridge, the successor least-value
Case 2 gap, and the successor recurrence Case 2 gap. The displayed boundary is
the source-selected boundary at `(J+1,J+1)`, so it now exports:

- `Case2DisplayedSuppliedChartFamilyBoundary.postLevelInvariants`;
- `Case2DisplayedSuppliedChartFamilyBoundary.successorLeastValueGap`;
- `Case2DisplayedSuppliedChartFamilyBoundary.postCase2Gap`.

This is projection bookkeeping only. It does not prove that the displayed
affine chart produces the recurrence or exponent post-data, and it does not
prove chart coverage, coordinate regularity, Jacobian/volume arithmetic,
normal crossings, RLCT extraction, termination, transition invariance, or
repair of the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 source-selected chart-map adapter

Reproduction:
`reproduction-case2-source-selected-chart-map-a4.md`.
Statement card:
`statement-card-a4-case2-source-selected-chart-map.md`.
Review artifact:
`review-case2-source-selected-chart-map-a4.md`.

Lean now names the source-coordinate selected-entry chart map for any supplied
Case 2 residual-block pivot
`p in case2ResidualBlockPivotEntries n S J`. The new source map sends the
supplied pivot to `u`, sends every other source pair to `u` times its residual
coordinate, and factors pointwise through the corresponding normalized source
map. The residual-block restriction lemmas identify these source-coordinate
blocks with the already proved subtype-indexed source-selected substitution
and normalized matrices.

The supplied source-selected boundary now exports
`sourceSelectedQP_sourceChartMap`, which is the existing arbitrary-pivot
source-selected `Q/P` identity rewritten in these source-chart names. The
pivot row weight remains
`post.weight (case2ResidualRowLevel n S J row)`, where `row` is extracted from
the supplied pivot membership proof; it is not specialized to
`post.weight (J+1)`.

This is a finite source-selected adapter only. It does not prove atlas
coverage, does not claim Aoyagi displays non-top-left source charts, and does
not prove chart-produced recurrence/exponent post-data, coordinate regularity,
Jacobian/volume arithmetic, normal crossings, RLCT extraction, termination,
transition invariance, or repair of the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed source-chart recurrence boundary

Reproduction:
`reproduction-case2-displayed-source-chart-recurrence-boundary-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-source-chart-recurrence-boundary.md`.
Review artifact:
`review-case2-displayed-source-chart-recurrence-boundary-a4.md`.

Lean now records the recurrence-only boundary connecting Aoyagi's displayed
top-left source chart variable to the concrete successor recurrence state. The
new theorems are:

- `case2DisplayedSourceChartMap_case2Succ_postData`;
- `case2DisplayedSourceChartMap_case2Succ_weight_update`;
- `case2DisplayedSourceChartMap_case2Succ_residualRowWeight_update`.

They state that `pre.case2Succ u` uses the displayed source chart's pivot value
as the new recurrence variable, and that all recurrence weights from `J+1`
onward are multiplied by that pivot value. The residual-row specialization
applies this update to every row in the Case 2 residual block.

This checkpoint uses the displayed chart only through the pivot value
`case2DisplayedSourceChartMap(...)(J+1,J+1) = u`. It does not construct an
affine chart, prove chart-produced exponent post-data, compute Jacobians,
prove chart coverage, coordinate regularity, normal crossings, RLCT
extraction, termination, transition invariance, or repair of the printed Case
2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed source-chart boundary constructor

Reproduction:
`reproduction-case2-displayed-source-chart-boundary-constructor-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-source-chart-boundary-constructor.md`.
Review artifact:
`review-case2-displayed-source-chart-boundary-constructor-a4.md`.

Lean now packages the displayed supplied Case 2 boundary with scalar equal to
the displayed source chart pivot value. The new theorem is

- `Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`.

It constructs the same corrected displayed supplied boundary as the concrete
constructor, but the scalar and successor are written as

```text
case2DisplayedSourceChartMap(...)(J+1,J+1)
pre.case2Succ (case2DisplayedSourceChartMap(...)(J+1,J+1)).
```

This is source-facing packaging only. The displayed chart map is still used
only through its pivot value, and chart regularity/transition regularity still
come from the supplied chart-family boundary. It does not prove chart-produced
recurrence or exponent post-data, non-top-left displayed charts, atlas
coverage, coordinate regularity, Jacobian/volume arithmetic, normal crossings,
RLCT extraction, termination, transition invariance, or repair of the printed
Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 post-pivot exhaustion boundary

Reproduction:
`reproduction-case2-post-pivot-exhaustion-a4.md`.
Statement card:
`statement-card-a4-case2-post-pivot-exhaustion.md`.
Review artifact:
`review-case2-post-pivot-exhaustion-a4.md`.

Lean now names the finite lower-right domain left after the displayed Case 2
pivot at `(J+1,J+1)`.  The new definitions are:

- `case2PostPivotRows`;
- `case2PostPivotCols`;
- `case2PostPivotEntries`.

In old `(S,J)` notation these are the row range `J+2..M(S)`, the column range
`J+2..M^(S+1)`, and their product.  Lean proves membership, cardinality,
row/column nonemptiness, and the key boundary:

```text
case2PostPivotEntries n S J is nonempty
  iff J+2 <= prefixMinNat n (S+1).
```

Consequently, if the next Case 2 continuation bound fails then at least one
post-pivot side is empty and the lower-right entry set is empty.  If the
current pivot was valid but the next pivot is not, then the frontier prefix
minimum is exactly `J+1`.

This checkpoint is only finite domain exhaustion.  It does not construct
`D'''_J`, the `S+1` advance state, chart-produced recurrence or exponent
post-data, atlas coverage, coordinate regularity, Jacobian/volume arithmetic,
normal crossings, RLCT extraction, termination, transition invariance, or
repair of the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed pivot-complement exhaustion

Reproduction:
`reproduction-case2-displayed-pivot-complement-exhaustion-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-pivot-complement-exhaustion.md`.
Review artifact:
`review-case2-displayed-pivot-complement-exhaustion-a4.md`.

Lean now identifies the displayed pivot-complement row/column types with the
old post-pivot lower-right domains:

```text
row complement ~= J+2..M(S),
col complement ~= J+2..M^(S+1).
```

The key theorem
`case2DisplayedPivotComplement_isEmpty_or_isEmpty_of_not_next_cont` says that
if the displayed pivot is valid and the next continuation bound fails, then
one of those complement types is empty.  The matrix-level corollaries
`case2DisplayedPivotComplement_matrix_subsingleton_of_not_next_cont` and
`case2DisplayedPivotComplement_matrix_eq_zero_of_not_next_cont` package the
lower-right complement block's vacuity for later terminal-block work.

This is still not Aoyagi's terminal matrix-shape theorem.  It does not
construct `D'''_J`, prove `D'''_J = (1,0,...,0)` or its transpose, prove the
whole post-`Q/P` zero pattern, construct `C'^(S+1)`, build the `S+1`
recurrence/exponent state, prove chart coverage or regularity, compute
Jacobians, prove normal crossings/RLCT extraction, prove termination or
transition invariance, or repair the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 stage-relabel domain audit

Reproduction:
`reproduction-case2-stage-relabel-domain-a4.md`.
Statement card:
`statement-card-a4-case2-stage-relabel-domain.md`.
Review artifact:
`review-case2-stage-relabel-domain-a4.md`.

Lean now records the finite introduced-label domain side condition behind
advancing from old `(S,J+1)` to `(S+1,0)`.  The frontier theorem
`case2_next_frontier_currentPrefixMin_or_nextWidth_eq_of_cont_of_not_next`
says that if the displayed pivot is valid and the next continuation bound
fails, then either the current prefix minimum is exhausted,
`prefixMinNat n S = J+1`, or the actual next width is exhausted,
`n(S+1)=J+1`.

The introduced-label domains at old `(S,J+1)` and `(S+1,0)` are equal only
under the actual-width side condition `n(S+1)=J+1`, as recorded by
`introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq` and
`introducedLabelFinset_currentSucc_eq_succStage_zero_of_nextWidth_eq`.
Conversely, `introducedLabel_succStage_zero_extra_witness_of_nextWidth_ge`
shows that if `J+2 <= n(S+1)`, then `(S,J+2)` is introduced at `(S+1,0)` but
not at old `(S,J+1)`.

This is only finite label-domain bookkeeping.  It does not construct the
`S+1` recurrence/exponent state, prove the terminal `D'''` block shape,
construct `C'^(S+1)`, prove chart coverage or regularity, compute Jacobians,
prove normal crossings/RLCT extraction, prove termination or transition
invariance, or repair the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed cleared-block vacuity

Reproduction:
`reproduction-case2-displayed-cleared-block-vacuity-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-cleared-block-vacuity.md`.
Review artifact:
`review-case2-displayed-cleared-block-vacuity-a4.md`.

Lean now applies the displayed pivot-complement vacuity theorem to the
already-cleared displayed Case 2 pivot block.  The theorem
`case2DisplayedClearedBlock_eq_pivotOnly_of_not_next_cont` says that if the
displayed pivot is valid and the next continuation bound fails, then the
pivot-first cleared block

```text
weightedPivotClearedBlock (D - x*y)
```

is equal to `weightedPivotClearedBlock 0`.

This is only the lower-right vacuity part of the terminal block shape, in
pivot-first coordinates and for the displayed normalized residual block.  It
does not construct Aoyagi's full `D'''_J` branch, choose the row-vs-column
presentation, construct `C'^(S+1)`, build the `S+1` recurrence/exponent state,
prove chart coverage or regularity, compute Jacobians, prove normal
crossings/RLCT extraction, prove termination or transition invariance, or
repair the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed cleared-block following-factor absorption

Reproduction:
`reproduction-case2-displayed-cleared-block-following-factor-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-cleared-block-following-factor.md`.
Review artifact:
`review-case2-displayed-cleared-block-following-factor-a4.md`.

Lean now proves the generic multiplication identity
`weightedPivotClearedBlock_zero_mul_verticalBlock`: a pivot-only cleared block
keeps the top row of a pivot-first following factor and kills the lower block.
The displayed specialization
`case2DisplayedClearedBlock_mul_verticalBlock_eq_pivotOnly_of_not_next_cont`
combines this with displayed Case 2 lower-right vacuity under failed next
continuation.

This is only pivot-first block multiplication.  It does not construct or
identify Aoyagi's `C'^(S+1)`, construct the full `D'''_J` terminal branch,
choose the row-vs-column presentation, build the `S+1` recurrence/exponent
state, prove chart production or coverage, compute Jacobians, prove normal
crossings/RLCT extraction, prove termination or transition invariance, or
repair the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed paper terminal absorption

Reproduction:
`reproduction-case2-displayed-paper-terminal-absorption-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-paper-terminal-absorption.md`.
Review artifact:
`review-case2-displayed-paper-terminal-absorption-a4.md`.

Lean now exposes paper-facing names for the displayed Case 2 top-left `Q/P`
calculation: `D_chart`, `Q`, `Q^-1`, `D''`, `C' = Q^-1 C`, and `D'''`.
The supplied displayed source-chart identity is restated in this notation.

The generic entry-ideal lemma `matrixEntryIdeal_sumElim_zero_bottom` proves
that adding zero bottom rows to a matrix does not change its matrix-entry
ideal.  Using the existing failed-continuation cleared-block theorem, Lean
then proves
`matrixEntryIdeal_case2DisplayedPaperDppp_mul_Cprime_eq_top_of_not_next_cont`:
under displayed pivot validity and failed next continuation, the
matrix-entry ideal of `D''' * C'` equals the matrix-entry ideal of the top
pivot row of `C'`.

This is only zero-row absorption in pivot-first paper notation.  It does not
construct or identify Aoyagi's next-stage `C'^(S+1)`, choose the source-order
row-vs-column terminal presentation, build the `S+1` recurrence/exponent
state, prove chart production or coverage, compute Jacobians, prove normal
crossings/RLCT extraction, prove termination or transition invariance, or
repair the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed terminal stack

Reproduction:
`reproduction-case2-displayed-terminal-stack-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-terminal-stack.md`.
Review artifact:
`review-case2-displayed-terminal-stack-a4.md`.

Lean now proves the generic entry-ideal facts
`matrixEntryIdeal_sumElim_eq_sup` and
`matrixEntryIdeal_sumElim_congr_bottom`: a stacked row block has entry ideal
equal to the supremum of the two row-block entry ideals, and replacing the
bottom block by another matrix with the same entry ideal preserves the
stacked entry ideal.

The displayed Case 2 specialization
`matrixEntryIdeal_case2DisplayedPaperTerminalStack_eq_topStack_of_not_next_cont`
applies this to an arbitrary supplied old top block `Cold`. Under displayed
pivot validity and failed next continuation,

```text
< entries([Cold; D''' * C']) > = < entries([Cold; C0]) >,
```

where `C0` is the top pivot row of `C' = Q^-1 C`.

This is source-order-shaped finite entry-ideal algebra only. It does not
identify `Cold` with Aoyagi's actual old top rows, construct or identify
`[Cold; C0]` with `C'^(S+1)`, choose the row-vs-column terminal presentation,
prove the diagonal-weighted full terminal product ideal, build `S+1` post-data,
prove chart production or coverage, compute Jacobians, prove normal
crossings/RLCT extraction, prove termination or transition invariance, or
repair the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed weighted terminal product

Reproduction:
`reproduction-case2-displayed-weighted-terminal-product-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-weighted-terminal-product.md`.
Review artifact:
`review-case2-displayed-weighted-terminal-product-a4.md`.

Lean now proves the suffix-aware entry-ideal facts `sumElim_mul`,
`matrixEntryIdeal_sumElim_zero_bottom_mul`, and
`matrixEntryIdeal_sumElim_congr_bottom_mul`: stacked row blocks can be
right-multiplied by a common following factor before zero bottom rows are
removed at the matrix-entry ideal level.

The displayed Case 2 specialization
`matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack_of_not_next_cont`
adds supplied old top weights `Wold`, supplied old top block `Cold`, residual
weights `b0`, `b`, and a supplied following suffix `F`. Under displayed pivot
validity and failed next continuation,

```text
< entries((blockdiag(Wold, diag(b0,b)) * [Cold; D''' * C']) * F) >
  =
< entries([ (Wold * Cold) * F ; (b0 * C0) * F ]) >,
```

where `C0` is the top pivot row of `C' = Q^-1 C`.

This checkpoint incorporates `F` before deleting zero rows, so it does not use
the invalid principle that entry-ideal equality is preserved by arbitrary right
multiplication.  It also retains the pivot weight `b0`; no unit hypothesis or
cancellation is assumed.  It still does not identify `Cold`, `Wold`, or `F`
with the source old top rows, source diagonal weights, or source remaining
product, identify the right hand side with Aoyagi's full `C'^(S+1)`, choose
the row-vs-column terminal presentation, build `S+1` post-data, prove chart
production or coverage, compute Jacobians, prove normal crossings/RLCT
extraction, prove termination or transition invariance, or repair the printed
Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed source-terminal candidate

Reproduction:
`reproduction-case2-displayed-source-terminal-candidate-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-source-terminal-candidate.md`.
Review artifact:
`review-case2-displayed-source-terminal-candidate-a4.md`.

Lean now names the source-order stopped terminal pieces
`case2DisplayedPaperTerminalWeight` and
`case2DisplayedPaperTerminalCnext`, and their product
`case2DisplayedPaperTerminalCprimeCandidate`:

```text
(blockdiag(Wold,[b0]) * [Cold; C0]) * F,
```

where `C0` is the top pivot row of `C' = Q^-1 C`.  The product theorem
`case2DisplayedPaperTerminalCprimeCandidate_eq_weight_mul_cnext_mul` records
this factorisation, and the expansion theorem
`case2DisplayedPaperTerminalCprimeCandidate_eq_verticalBlock_mul` identifies
this product with the previously proved expanded stack
`[(Wold*Cold)*F ; (b0*C0)*F]`.

The supplied displayed-boundary theorem
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont`
combines the supplied source-chart `Q/P` identity with failed-continuation
terminal absorption.  The residual terminal weight is sourced from the supplied
successor recurrence state as `post.weight (J+1)`, while the old top multiplier
`Atop`, old top block `Ctop`, and suffix `F` remain supplied.

This advances the terminal display to the paper-shaped "diagonal outside the
candidate following matrix" form.  It still does not prove that `Atop`, `Ctop`,
or `F` are Aoyagi's actual old diagonal weights, old top rows, or remaining
product, and it does not prove that `[Ctop;C0]` is the source-produced
`C'^(S+1)`.  It also does not choose the row-vs-column terminal presentation
beyond the displayed pivot-first stopped block, build `S+1` post-data, prove
chart production or coverage, compute Jacobians, prove normal crossings/RLCT
extraction, prove termination or transition invariance, or repair the printed
Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 displayed terminal source model

Reproduction:
`reproduction-case2-displayed-terminal-source-model-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-terminal-source-model.md`.
Review artifact:
`review-case2-displayed-terminal-source-model-a4.md`.

Lean now packages the actual-width-exhausted displayed terminal branch as
`Case2DisplayedSuppliedActualWidthTerminalSourceModel`.  The structure carries
supplied old top data and suffix:

```text
Atop : Matrix old old R
Ctop : Matrix old tau R
F    : Matrix tau suffix R
```

together with the branch hypothesis

```text
n(S+1) = J+1.
```

The projections `terminalWeightCandidate`, `terminalCnextCandidate`, and
`terminalProductCandidate` name the supplied candidate

```text
(blockdiag(Atop,[b0]) * [Ctop; C0]) * F,
```

where `C0` is the top pivot row of `C' = Q^-1 C`.

The model proves two branch facts.  First, actual-width exhaustion implies
failed next continuation

```text
not (J+2 <= prefixMinNat n (S+1)).
```

Second, the introduced-label domain after the old pivot `(S,J+1)` equals the
stage-relabelled domain `(S+1,0)`.  This is only finite-domain bookkeeping:
Lean does not construct a recurrence state or exponent state over `(S+1,0)`.

The wrapper
`Case2DisplayedSuppliedChartFamilyBoundary.exists_weightedTerminalProduct_entryIdeal_eq_terminalProductCandidate_of_actualWidth`
calls the existing supplied-boundary terminal theorem with
`model.not_next_cont_of_actualWidth_exhausted`.
It keeps `Atop`, `Ctop`, and `F` supplied and keeps the pivot weight
`post.weight (J+1)` outside the unweighted candidate matrix.  It does not
prove that `[Ctop;C0]` is source-produced `C'^(S+1)`, prove chart production
or coverage, compute Jacobians, prove normal crossings/RLCT extraction, prove
termination or transition invariance, or repair the printed Case 2 vector
mismatch.  Prefix exhaustion alone remains outside this positive model because
if `n(S+1) >= J+2`, then `(S,J+2)` is an extra label at `(S+1,0)`.

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

## 2026-06-19 Lean Case 2 corrected exponent post-data

Reproduction: `reproduction-case2-corrected-exponent-post-data-a4.md`.
Statement card: `statement-card-a4-case2-corrected-exponent-post-data.md`.
Review artifact: `review-case2-corrected-exponent-post-data-a4.md`.

Lean now packages supplied corrected exponent post-data as
`Case2CorrectedExponentPostData`: old introduced-label vectors, numerators, and
least values are unchanged, while the new label `(S,J+1)` receives the
corrected prefix-minimum vector, numerator `(mu_S-J)(n_(S+1)-J)`, and least
value `J`.

The all-label extension theorem
`IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_postData`
uses this package with a corrected new-label certificate. The concrete update
wrapper now factors through the package. On the recurrence side,
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.levelInvariants_of_correctedExponentPostData`
and
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.case2Gap_of_leastValueGap_of_correctedExponentPostData`
connect supplied recurrence post-data to supplied corrected exponent post-data:
the equality bridge `leastValue = level` and the integer least-value Case 2 gap
advance to the successor recurrence-level gap.

This remains corrected certificate and invariant bookkeeping. It is not chart
production, an exponent transition invariant, arbitrary-pivot transport, source
comparability, normal crossing, RLCT extraction, or a claim that the corrected
vector is the PDF's printed Case 2 vector.

## 2026-06-19 Lean Case 2 arbitrary selected-entry source substitution

Reproduction: `reproduction-case2-arbitrary-selected-source-substitution-a4.md`.
Statement card:
`statement-card-a4-case2-arbitrary-selected-source-substitution.md`.
Review artifact: `review-case2-arbitrary-selected-source-substitution-a4.md`.

Lean now has the arbitrary selected-entry analogue of the displayed Case 2
source-substitution transport. A finite pivot entry in
`case2ResidualBlockPivotEntries` can be converted to row/column subtype pivots.
For any supplied residual-row pivot and residual-column pivot,
`case2SelectedSubstitutionMatrix` is `u` times the normalised selected-entry
matrix, and pivot-first reindexing absorbs the selected variable into row
weights. The following factor is also reindexed into pivot-first column order.

The conditional wrapper
`exists_case2SelectedQP_mul_sourceSubstitution_of_forall_dvd` applies the
existing pivot-first `Q/P` identity under explicit divisibility of every lower
row weight by the selected pivot-row weight; the flat-row-weight corollary is
`exists_case2SelectedQP_mul_sourceSubstitution_of_flat_weights`.

This is finite algebra and chart-family scaffolding. It is not a proof of an
affine blow-up atlas, arbitrary-pivot chart coverage, chart regularity/Jacobian
facts, recurrence post-state production, exponent updates, transition
invariants, source comparability, normal crossings, or RLCT extraction.

## 2026-06-19 Lean Case 2 arbitrary selected-entry recurrence handoff

Reproduction: `reproduction-case2-arbitrary-selected-recurrence-handoff-a4.md`.
Statement card: `statement-card-a4-case2-arbitrary-selected-recurrence-handoff.md`.
Review artifact: `review-case2-arbitrary-selected-recurrence-handoff-a4.md`.

Lean now lifts the arbitrary selected-entry Case 2 source-substitution algebra
to the packaged recurrence-state boundary. For any supplied residual-block row
and column pivot, the old recurrence-state Case 2 gap gives the flat old row
weights needed by the arbitrary selected-pivot `Q/P` theorem. If a supplied
successor recurrence state preserves old recurrence data and adds `(S,J+1)` at
level `J` with variable `u`, the right-side diagonal is rewritten from
`u * pre.weight` to `post.weight` at the corresponding residual row levels.

The `_of_postData` wrappers accept the named
`IntroducedLabelRecurrenceState.Case2SuppliedPostData` package. This remains
conditional finite algebra for a supplied pivot and supplied post-state; it is
not chart production, arbitrary-pivot chart coverage, regularity/Jacobian,
exponent update, transition invariant, source comparability, normal crossings,
or RLCT extraction.

## 2026-06-19 Lean Case 2 source-selected pair wrapper

Reproduction: `reproduction-case2-source-selected-pair-wrapper-a4.md`.
Statement card: `statement-card-a4-case2-source-selected-pair-wrapper.md`.
Review artifact: `review-case2-source-selected-pair-wrapper-a4.md`.

Lean now has a source-coordinate adapter for supplied arbitrary Case 2
residual-block pivot pairs. A source pair `p : Nat × Nat` with
`p ∈ case2ResidualBlockPivotEntries n S J` extracts row and column subtype
pivots, restricts source residual data to the residual block, restricts a
source-column following factor to residual columns, and instantiates the
arbitrary selected-pivot recurrence-gap and supplied-post-data `Q/P` wrappers.

This is a usability bridge from source-coordinate data into the finite algebra.
It is not chart coverage, not a claim that Aoyagi displays non-top-left Case 2
charts, and not a source-order transition theorem for non-displayed pivots.

## 2026-06-19 Lean selected-entry principalization and unit facts

Reproduction:
`reproduction-selected-entry-principalization-unit-facts-a4.md`.
Statement card: `statement-card-a4-selected-entry-principalization-unit-facts.md`.
Review artifact: `review-selected-entry-principalization-unit-facts-a4.md`.

Lean now records the elementary regularity-boundary algebra for selected-entry
charts. The pivot row operation `P`, the column operation `Q`, and the
displayed inverse `Q^-1` are matrix units, and their determinants are units.
For any finite center and selected pivot in that center, the ideal generated by
the transformed center generators under `selectedEntryChartMap` is exactly the
principal ideal `(u)`. Case 1 and Case 2 specializations apply this to
`case1CenterGenerators` and `case2ResidualBlockPivotEntries`.

This proves principalization of the finite center ideal in a supplied selected
chart. It does not prove chart coverage, an affine blow-up atlas, a
polynomial-coordinate Jacobian formula, source-order transition formulas, or
chart-produced recurrence/exponent post-data.

## 2026-06-19 Lean Case 2 chart-family boundary

Reproduction: `reproduction-case2-chart-family-boundary-a4.md`.
Statement card: `statement-card-a4-case2-chart-family-boundary.md`.
Review artifact: `review-case2-chart-family-boundary-a4.md`.

Lean now names the remaining Case 2 selected-entry chart-family assumptions.
The generic `SelectedEntryChartFamilyBoundary` records supplied
chart-regularity and transition-regularity predicates for every selected entry
in a finite center. `Case2ResidualBlockChartFamilyBoundary` specializes this
to the Case 2 residual-block center. The only new proved source fact is
nonemptiness under continuation: the displayed pivot `(J+1,J+1)` belongs to
`case2ResidualBlockPivotEntries n S J`.

This is an assumption boundary, not chart coverage. It does not prove chart
regularity, transition regularity, affine blow-up atlas construction,
source-order transition formulas, chart-produced post-data, Jacobians, normal
crossings, or RLCT extraction.

## 2026-06-19 Lean Case 1 chart-family boundary

Reproduction: `reproduction-case1-chart-family-boundary-a4.md`.
Statement card: `statement-card-a4-case1-chart-family-boundary.md`.
Review artifact: `review-case1-chart-family-boundary-a4.md`.

Lean now names the analogous Case 1 chart-family boundary. The finite center
is `case1CenterGenerators n S J J1`: the `Unit` branch is the externally
chosen old exceptional generator, and the right branch is the row-strip entry
set. The new helper lemmas prove that this finite center is nonempty, that the
row-strip part is nonempty under `1 <= J1` and `J+1 <= n_(S+1)`, and that a
right-branch generator belongs to the center iff its underlying pair belongs
to the row strip.

`Case1CenterChartFamilyBoundary` packages supplied `ChartRegular` and
`TransitionRegular` predicates for all generators in this finite center. The
boundary projections give chart regularity for arbitrary members, transition
regularity for arbitrary pairs, the old-exceptional-variable chart, and the
displayed top-left row-strip pivot under the displayed entry bounds or the
first-jump positivity package plus the column bound.

This is an assumption boundary. It does not prove chart coverage, chart
regularity, transition regularity, the source validity of the hidden old label
represented by `Unit`, arbitrary row-strip pivot source-order formulas,
chart-produced recurrence/exponent post-data, Jacobians, normal crossings, or
RLCT extraction.

## 2026-06-19 Lean displayed top-left source-order adapter

Reproduction: `reproduction-displayed-top-left-source-order-adapter-a4.md`.
Statement card: `statement-card-a4-displayed-top-left-source-order-adapter.md`.
Review artifact: `review-displayed-top-left-source-order-adapter-a4.md`.

Lean now has a generic source-order adapter for the displayed top-left
selected-entry pivot calculation. `WeightedPivotFirstSubstitutionData` records
an already weighted, already source-substituted block `weightedSource`,
normalised pivot block components `x`, `y`, `D`, row weights `b0`, `b`, a
following factor `C`, and supplied equations
`weightedSource = weightedPivotDiagonal b0 b * pivotPreQBlock x y D` and
`b i = q i * b0`. The theorem `sourceOrder_identity` applies the already
proved finite `Q/P` algebra to this supplied data. The existential wrapper
chooses quotient witnesses from divisibility.

The same checkpoint proves the finite Case 1 helper
`Case1FirstJumpHypotheses.continuationBound_of_colBound`: first-jump row
boundedness plus the actual column bound imply `J+1 <= mu_(S+1)` for the
displayed top-left pivot.

This is not a Case 1 or Case 2 transition theorem. It does not construct the
selected chart, prove full residual-block substitution in Case 1(2), produce
recurrence/exponent post-data, decide continuation vs advance, prove chart
coverage/regularity/Jacobians, normal crossings, or RLCT extraction.

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

## 2026-06-19 Lean Case 1 displayed row-strip new-label exponent

Statement card:
`statement-card-a4-case1-displayed-row-strip-new-label-exponent.md`.

Lean now separates the Case 1(2) displayed row-strip new-label exponent
extension from the older same-domain selected-label update. The new theorem
`Case1FirstJumpHypotheses.displayedRowStrip_newLabelExponentCertificate`
reuses the lower-tail terminal-exponent and least-value arithmetic for the old
selected label, but gives the certificate to the fresh post-state label
`(S,J+1)` using the actual-width bound `J+1 <= n(S+1)`.

The accompanying post-data package
`Case1DisplayedRowStripExponentPostData` preserves all old introduced labels
and assigns `(S,J+1)` the source-shaped vector, numerator increment
`J1*(n(S+1)-J)`, and least value `J`. The concrete update-data wrapper changes
only `(S,J+1)`, relying on the fact that this label is not introduced at
state `(S,J)`.

This is not a chart-production or transition theorem. The chart-produced
post-data, level/least-value bridge, flat-tail invariant, recurrence
bookkeeping, hidden old-label validity, Jacobian formula, normal crossings,
and RLCT extraction remain outside this checkpoint.

## 2026-06-19 Lean Case 1 displayed row-strip factored-base post-data

Statement card:
`statement-card-a4-case1-displayed-row-strip-factored-base-postdata.md`.

Lean now names the recurrence boundary needed for the displayed Case 1(2)
row-strip branch.  The new alias
`Case1DisplayedRowStripFactoredBasePostData` deliberately uses a factored-old
base recurrence state, not the original pre-chart state.  The supplied
post-data then adds the fresh label `(S,J+1)` at level `J` with variable `u`,
so the existing recurrence update gives `post.weight i = u*base.weight i` for
all residual rows `J+1 <= i`.

The new displayed source-order wrapper starts from the previously proved
row-strip source matrix with `case1RowStripOldWeight`, chooses quotient
witnesses from factored-base monomial recurrence divisibility, and rewrites the
right-hand diagonal to supplied post weights.

This is still a supplied-data boundary.  It does not relate the original
pre-state to the factored-base state, prove hidden old-label validity, extract
complete old-label post assignments from the PDF, construct charts, prove
coverage/regularity, compute Jacobians, or prove normal crossings/RLCT.

## 2026-06-19 Lean Case 1 monomial recurrence split

Statement card: `statement-card-a4-case1-monomial-recurrence-split.md`.

Lean now proves the pure recurrence off-by-one calculation used by the
factored-base Case 1(2) boundary.  The new `mulStepAt` operation inserts one
factor at one recurrence level.  Theorems
`monomialRec_mulStepAt_eq_of_le` and
`monomialRec_mulStepAt_eq_mul_of_ge` show that a factor inserted at level `r`
does not affect rows `i <= r` and multiplies all rows `r+1 <= i`.

The Case 1 corollaries then compare an old source factor at level `h` with a
new post factor at level `J`: on `J+1 <= i <= h`, only the post recurrence has
picked up the factor; on `h+1 <= i`, both recurrences have picked it up and
the row weights agree.

This is only monomial recurrence algebra.  It does not construct the
factored-base state, prove chart production, prove hidden old-label validity,
or assert a transition invariant.

## 2026-06-19 Lean Case 1 source-weight factored boundary

Statement card: `statement-card-a4-case1-source-weight-factored-boundary.md`.

Lean now connects the original source recurrence after the old selected
substitution `old = u*old'` to the displayed row-strip weight convention. The
new `case1ResidualRowStrip` predicate is the canonical residual-row version of
the strip `J+1..J+J1`: a residual row is in the strip exactly when its source
row level is at most `J+J1`.

The theorem `case1ResidualRowStripOldWeight_eq_sourceMulStepAt` identifies
`case1RowStripOldWeight` with the recurrence obtained by inserting the factor
`u` at the old selected level `J+J1`. The matrix theorem
`case1ResidualRowStrip_diagonal_mul_sourceMatrix_sourceWeights` then rewrites
the existing row-strip source-matrix identity with the original source
recurrence on the left diagonal and the common factored-base weight
`u*baseWeight` on the right.

This remains source-weight algebra only. It does not construct the
factored-base recurrence, prove hidden old-label validity, produce chart
post-data, or assert a transition invariant.

## 2026-06-19 Lean Case 1 displayed row-strip local handoff

Statement card:
`statement-card-a4-case1-displayed-row-strip-local-handoff.md`.

Lean now packages the displayed top-left Case 1(2) local handoff as a supplied
boundary. The source-order projection rewrites the left diagonal in original
source-recurrence form,
`monomialRec (mulStepAt factoredBase.step u (J+J1))`, and rewrites the
right diagonal using supplied post-state weights. The boundary also stores the
supplied pre-state exponent certificates, level-tail invariants, and
Case 1 displayed row-strip exponent post-data, so its exponent projection
extends the certificate domain to the fresh label `(S,J+1)`.

The proof keeps row and column bounds separate: first-jump data and
`J+1 <= n(S+1)` give the continuation bound
`J+1 <= prefixMinNat n (S+1)`, while the exponent increment remains
`J1*(n(S+1)-J)`.

This is still a supplied local handoff. It does not construct the
factored-base recurrence from the original pre-state, prove hidden old-label
source validity, prove that a chart produces the supplied post-data, or assert
chart coverage, regularity, Jacobians, normal crossings, RLCT extraction, or a
full transition invariant.

## 2026-06-19 Lean Case 1 selected-old source substitution

Statement card:
`statement-card-a4-case1-selected-old-source-substitution.md`.

Lean now proves the elementary same-domain recurrence substitution for the
hidden old selected variable in Case 1(2). The new generic finite-product
lemmas show that scaling one existing label variable scales exactly the
recurrence factor at that label's level and leaves all other recurrence factors
unchanged. The Case 1 package
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData` then records
the supplied interpretation of `source` as the pulled-back source recurrence
after `old = u*old'`, relative to a factored-base recurrence using `old'`.

Under first-jump selected-level data, Lean proves

```text
source.step = mulStepAt factoredBase.step u (J+J1).
```

The row-strip corollary rewrites the old-weight convention used by the
displayed source matrix as these substituted source recurrence weights on
residual rows.

This is still recurrence bookkeeping. It does not construct the selected-old
chart, identify the hidden old label behind the `Unit` center generator,
construct the factored-base state, produce post-data, or prove chart coverage,
regularity, Jacobians, normal crossings, RLCT extraction, or a transition
invariant.

## 2026-06-19 Lean Case 1 source-substituted local handoff

Statement card:
`statement-card-a4-case1-source-substituted-local-handoff.md`.

Lean now combines the selected-old source substitution boundary with the
displayed row-strip local handoff. The new theorem
`Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_substitutedSourceWeights`
rewrites the local handoff's left diagonal from
`monomialRec (mulStepAt factoredBase.step u (J+J1))` to the supplied
substituted source recurrence weights
`source.weight (case2ResidualRowLevel n S J i)`.

The theorem requires an explicit equality `level = factoredBase.level`,
because the local exponent/first-jump level map and the recurrence-state level
map are still separate supplied data. This is deliberate: the theorem does not
construct the source pullback, selected-old chart, factored-base state, post
state, chart-produced post-data, coverage, regularity, Jacobians, normal
crossings, RLCT extraction, or a transition invariant.

## 2026-06-19 Lean Case 1 selected-old pullback boundary

Statement card:
`statement-card-a4-case1-selected-old-pullback-boundary.md`.

Lean now packages the supplied selected-old pullback boundary for the displayed
Case 1(2) row-strip chart. The new structure
`Case1DisplayedRowStripSelectedOldPullbackBoundary` combines:

- selected-old pullback recurrence data, where `source` is already the
  recurrence after `old = u*old'`;
- the displayed row-strip local handoff specialized to `factoredBase.level`.

The specialization removes the separate `level = factoredBase.level`
hypothesis needed by the previous wrapper. The package exposes projection
theorems for the selected old step, old-center membership of the `Unit` token,
selected-label facts, row-strip source-weight rewriting, the source-order
identity, and exponent-domain extension.

This is still an assumption interface. It does not construct the selected-old
chart, prove that the `Unit` token determines `(s0,k0)`, construct the raw
source pullback, produce post-data from coordinates, prove chart coverage or
regularity, compute Jacobians, assert normal crossings, extract RLCT, or prove
a transition invariant.

## 2026-06-19 Lean Case 1 selected-old supplied chart-family boundary

Statement card:
`statement-card-a4-case1-selected-old-supplied-chart-family-boundary.md`.

Lean now packages the selected-old pullback boundary together with supplied
Case 1 finite chart-family regularity. The new structure
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary` has two fields:
the selected-old pullback/local handoff boundary and a
`Case1CenterChartFamilyBoundary`.

The projections expose chart regularity for the selected old `Unit` token and
the displayed top-left row-strip pivot, transition regularity in both
directions between those two supplied center members, selected-label facts,
the selected-old source recurrence step, the source-order identity, and the
exponent-domain extension.

This is still a supplied interface. It does not construct charts, prove
coverage, derive `(s0,k0)` from `Unit`, construct the raw source pullback,
compute Jacobians, assert normal crossings, extract RLCT, or prove a
transition invariant.

## 2026-06-19 Lean Case 1 selected-old source-coordinate wrapper

Statement card:
`statement-card-a4-case1-selected-old-source-coordinate-wrapper.md`.

Lean now adapts the already supplied selected-old chart-family boundary to
source-coordinate residual and following-factor functions. The new
`case2DisplayedSourceFollowingFactor` restricts a source following factor to
the residual columns and reindexes it into the displayed top-left pivot-first
column order. The theorem
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates`
then applies the existing source-order identity to
`case2SourceResidualBlock residual`, using the source-coordinate pivot
normalization `residual (J+1,J+1) = 1`.

The same checkpoint projects finite selected-entry principalization facts for
the displayed top-left row-strip pivot. The selected variable occurs as a
transformed center value, divides all transformed finite center generators,
and generates the transformed finite center ideal for that displayed pivot
token. The selected-old `Unit` principalization projection is intentionally
not made with this same variable, because here `u` is the displayed row-strip
pivot factor in `old = u*old'`.

This is still not chart production. It does not construct the selected-old
chart, prove atlas coverage, derive `(s0,k0)` from `Unit`, construct the raw
source pullback, produce chart post-data, compute Jacobians, prove normal
crossings, extract RLCT, or prove a transition invariant.

## 2026-06-19 Lean Case 1 selected-old chart source coordinates

Statement card:
`statement-card-a4-case1-selected-old-chart-source-coordinates.md`.

Lean now proves the elementary Case 1(1) selected-old row-strip
source-coordinate identity. The new post-weight convention
`case1SelectedOldPostWeight` absorbs the selected old chart denominator
exactly on the Case 1 row strip and leaves lower rows unchanged. The theorem
`case1SelectedOld_diagonal_mul_sourceMatrix` proves

```text
diag(baseWeight) * case1RowStripSourceMatrix(strip,u,A)
  = diag(case1SelectedOldPostWeight(strip,u,baseWeight)) * A.
```

The source-coordinate specialization
`case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates` applies this
to `case1ResidualRowStrip n S J J1` and `case2SourceResidualBlock residual`,
so residual rows still use the prefix-minimum row subtype while residual
columns still use actual width.

This is the Case 1(1) row-wise calculation only. It does not introduce
`(S,J+1)`, does not use the displayed Case 1(2) pivot `u_(S,J+1)`, and does
not assert a `Q/P` transition, chart construction, atlas coverage,
regularity, Jacobian, normal crossings, RLCT extraction, or a transition
invariant.

## 2026-06-19 Lean Case 1 selected-old same-domain boundary

Statement card:
`statement-card-a4-case1-selected-old-same-domain-boundary.md`.

Lean now packages the supplied same-domain boundary for Aoyagi Case 1(1). The
new `Case1SelectedOldLowerTailExponentPostData` records that the selected old
label `(s0,k0)` receives the lower-tail vector, the actual-width numerator
increment

```text
J1 * (n(S+1)-J),
```

and least value `J`, while every other introduced label at `(S,J)` is supplied
unchanged.

The theorem
`IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_postData`
feeds this post-data into the existing same-domain lower-tail update, and
`case1_selectedLowerTail_of_levelTailInvariants_postData` uses the packaged
level/tail invariants. The new boundary
`Case1SelectedOldSuppliedSameDomainBoundary` carries first-jump data,
pre-state certificates, level-tail invariants, and supplied post-data, then
projects:

- selected introducedness and selected level;
- the generic and source-coordinate Case 1(1) row-strip identities;
- the same-domain exponent-certificate update over `(S,J)`.

This is still an assumption interface. It does not construct the selected-old
chart, prove that coordinates produce the post-data, introduce `(S,J+1)`, use
the displayed Case 1(2) pivot, assert `Q/P`, prove chart coverage or
regularity, compute Jacobians, prove normal crossings, extract RLCT, or prove
a transition invariant.

## 2026-06-19 Lean Case 1 selected-old recurrence post weight

Statement card:
`statement-card-a4-case1-selected-old-recurrence-postweight.md`.

Lean now proves the pure recurrence calculation behind the Case 1(1) strip
weights. Starting from a supplied base recurrence with the selected old factor
kept separate, moving the factor from level `J+J1` down to level `J` gives
the piecewise post-weight convention on active residual rows:

```text
b'_i =
  u * b_i, if i <= J+J1,
  b_i,     otherwise.
```

The residual-row theorem
`case1SelectedOldPostWeight_eq_monomialRec_loweredLevel` identifies this with
`case1SelectedOldPostWeight`, and the matrix corollaries rewrite the
Case 1(1) source-coordinate identity with the lowered recurrence on the right
diagonal.

This is recurrence algebra only. It does not construct the selected-old chart,
derive the supplied base recurrence from source recurrence data, build a
recurrence-state post-data theorem, introduce `(S,J+1)`, use the displayed
Case 1(2) pivot, assert `Q/P`, prove chart coverage or regularity, compute
Jacobians, prove normal crossings, extract RLCT, or prove a transition
invariant.

## 2026-06-19 Lean Case 1 selected-old lowered recurrence boundary

Statement card:
`statement-card-a4-case1-selected-old-lowered-recurrence-boundary.md`.

Lean now packages the supplied recurrence-state boundary for the Case 1(1)
level lowering. The new structure
`Case1SelectedOldLoweredRecurrenceBoundary` assumes a supplied base recurrence
with the selected old factor kept separate:

```text
pre.step  = mulStepAt baseStep u (J+J1),
post.step = mulStepAt baseStep u J.
```

It also carries the previously proved same-domain selected-old exponent
boundary. The projections identify the piecewise selected-old post-weight
convention with supplied `post.weight` on residual rows and rewrite the
source-coordinate row-strip identity with `pre.weight` on the left and
`post.weight` on the right. The exponent update is re-exported over the same
domain `(S,J)`.

This is still a supplied interface. It does not construct the selected-old
chart, derive `baseStep` or the pre/post recurrence states from source
coordinates, produce recurrence post-data from a chart, introduce `(S,J+1)`,
use the displayed Case 1(2) pivot, assert `Q/P`, prove chart coverage or
regularity, compute Jacobians, prove normal crossings, extract RLCT, or prove
a transition invariant.

## 2026-06-19 Lean Case 1 selected-old Unit chart-family boundary

Statement card:
`statement-card-a4-case1-selected-old-unit-chart-family-boundary.md`.

Lean now packages the supplied chart-family/principalization boundary for the
Case 1(1) selected-old `Unit` chart. The new structure
`Case1SelectedOldUnitSuppliedChartFamilyBoundary` combines
`Case1SelectedOldLoweredRecurrenceBoundary` with
`Case1CenterChartFamilyBoundary`.

The package projects selected introducedness and selected level from the
lowered recurrence boundary, while the finite center token itself remains
`Sum.inl () : Case1CenterGenerator`. It projects supplied chart regularity for
that token, supplied transition regularity from/to any finite Case 1 center
generator, finite selected-entry principalization for the selected-old chart
variable, the pre/post recurrence source identities, and the same-domain
exponent update.

This remains a supplied interface over `(S,J)`. It does not identify the
`Unit` token with `(s0,k0)` from raw source coordinates, construct the
selected-old chart, derive `baseStep` or the pre/post recurrence states from
source data, produce recurrence post-data from a chart, introduce `(S,J+1)`,
use the displayed Case 1(2) pivot, assert `Q/P`, prove chart coverage or
regularity from coordinates, compute Jacobians, prove normal crossings,
extract RLCT, or prove a transition invariant.

## 2026-06-20 Lean Case 1 selected-old erased-base source model

Reproduction:
`reproduction-case1-selected-old-erased-base-source-model-a4.md`.
Statement card:
`statement-card-a4-case1-selected-old-erased-base-source-model.md`.

Lean now derives the lowered-recurrence boundary's two step equalities from a
finite-product source model. The erased base recurrence is the product over the
introduced-label set with the selected old label `(s0,k0)` removed:

```text
baseStep = pre.erasedStep s0 k0.
```

The package `Case1SelectedOldLevelMoveData` records that the selected old label
is introduced, has pre-level `J+J1`, post-level `J`, and the same selected
variable `u` in both states, while all non-selected introduced labels keep
their level and variable data. Lean proves that the erased base is unchanged
and therefore:

```text
pre.step  = mulStepAt (pre.erasedStep s0 k0) u (J+J1),
post.step = mulStepAt (pre.erasedStep s0 k0) u J.
```

The constructor `Case1SelectedOldLoweredRecurrenceBoundary.of_levelMoveData`
instantiates the existing lowered boundary with this erased base recurrence.

This removes the arbitrary `baseStep` assumption for this recurrence
checkpoint, but the moved-level data itself is still supplied recurrence
bookkeeping. It does not construct the selected-old chart, infer `(s0,k0)` from
the `Unit` token, introduce `(S,J+1)`, use Case 1(2), assert `Q/P`, prove chart
coverage or regularity from coordinates, compute Jacobians, prove normal
crossings, extract RLCT, or prove a transition invariant.

## 2026-06-20 Lean Case 1 selected-old concrete level move

Reproduction:
`reproduction-case1-selected-old-concrete-level-move-a4.md`.
Statement card:
`statement-card-a4-case1-selected-old-concrete-level-move.md`.

Lean now defines the concrete same-domain recurrence post-state
`case1SelectedOldLevelMove`.  For a pre-state over `(S,J)`, the post-state
changes only the selected old label's recurrence level to `J`; all
recurrence-label variables are unchanged, and all non-selected levels are
unchanged.  This is only recurrence-label bookkeeping; raw residual matrix
coordinates are still governed by the separate selected-old row-strip
source-coordinate identity.

If `(s0,k0)` is introduced and `pre.level s0 k0 = J+J1`, Lean proves the
concrete post-state supplies `Case1SelectedOldLevelMoveData` with selected
scalar `pre.var s0 k0`.  The thin constructor
`Case1SelectedOldLoweredRecurrenceBoundary.of_sameDomain_case1SelectedOldLevelMove`
then instantiates the erased-base lowered boundary directly from a same-domain
package stated over `pre.level`.

This removes the need to hand-supply a separate post recurrence state for this
checkpoint, but it still does not construct the selected-old chart, infer
`(s0,k0)` from the `Unit` token, introduce `(S,J+1)`, use Case 1(2), assert
`Q/P`, prove chart coverage or regularity from coordinates, compute Jacobians,
prove normal crossings, extract RLCT, or prove a transition invariant.

## 2026-06-20 Lean Case 1 selected-old Unit concrete level move

Reproduction:
`reproduction-case1-selected-old-unit-concrete-level-move-a4.md`.
Statement card:
`statement-card-a4-case1-selected-old-unit-concrete-level-move.md`.

Lean now instantiates the selected-old `Unit` chart-family boundary directly
from the concrete same-domain recurrence post-state.  The theorem
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.of_sameDomain_case1SelectedOldLevelMove`
takes:

- a pre-state over `(S,J)`;
- a same-domain Case 1(1) selected-old boundary stated over `pre.level`;
- a supplied finite Case 1 chart-family boundary.

It returns the Unit chart-family boundary with:

```text
post = pre.case1SelectedOldLevelMove s0 k0,
u = pre.var s0 k0,
baseStep = pre.erasedStep s0 k0.
```

This is only a packaging constructor. Chart regularity and transition
regularity still come from the supplied `Case1CenterChartFamilyBoundary`; the
theorem does not construct the selected-old chart, infer `(s0,k0)` from the
`Unit` token, introduce `(S,J+1)`, use Case 1(2), assert `Q/P`, prove chart
coverage or regularity from coordinates, compute Jacobians, prove normal
crossings, extract RLCT, or prove a transition invariant.

## 2026-06-19 Lean Case 1 displayed paper Q/P adapter

Statement card:
`statement-card-a4-case1-displayed-paper-qp-adapter.md`.

Lean now exposes paper-facing names for Aoyagi Case 1(2)'s displayed top-left
`Q/P` calculation. The new names identify:

- `case1DisplayedPaperDchart`, the already normalized source-coordinate block;
- `case1DisplayedPaperSourceBlock`, the source row-strip block before `Q/P`;
- `case1DisplayedPaperQ` and `case1DisplayedPaperQinv`;
- `case1DisplayedPaperDpp`, corresponding to `D'' = D_chart * Q`;
- `case1DisplayedPaperCprime`, corresponding to `C' = Q^-1 C`;
- `case1DisplayedPaperDppp`, corresponding to the cleared block `D'''`.

The theorem `case1DisplayedPaperDpp_eq_pivotPostQBlock` identifies `D''` with
the generic post-`Q` block under the supplied pivot normalization
`residual (J+1,J+1)=1`. The theorem `case1DisplayedPaperDpp_mul_Cprime` pins
the orientation of Aoyagi's following-factor update by proving
`D'' * C' = D_chart^pivot * C`.

Finally,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates_paperQP`
restates the existing supplied source-order identity in this paper notation.

This checkpoint is only a notation/adapter layer. It does not construct the
displayed chart, derive selected-old pullback data, build recurrence or
exponent post-data from coordinates, prove chart coverage or regularity from
coordinates, compute Jacobians, prove normal crossings, extract RLCT, or prove
a transition invariant.

## 2026-06-20 Lean Case 2 actual-width terminal relabel

Reproduction:
`reproduction-case2-actual-width-terminal-relabel-a4.md`.
Statement card:
`statement-card-a4-case2-actual-width-terminal-relabel.md`.
Review artifact:
`review-case2-actual-width-terminal-relabel-a4.md`.

Lean now proves the elementary relabel of supplied Case 2 post-pivot
recurrence and exponent data from old `(S,J+1)` to stage `(S+1,0)` under
actual next-width exhaustion:

```text
n(S+1) = J+1.
```

The generic relabel lemmas transport `IntroducedLabelLevelInvariants` and
`IntroducedLabelExponentCertificates` across the introduced-label domain
equality.  The copied recurrence state `stageRelabelSuccZero` keeps the same
`level` and `var` maps, and under the same actual-width hypothesis its finite
product `step` and row `weight` agree with the old post-state.  The displayed
boundary projections expose this as `terminalRelabelPost`, together with
level-invariant and exponent-domain transport.

This is supplied-data bookkeeping only.  It does not prove chart production,
does not identify `[Ctop;C0]` with source-produced `C'^(S+1)`, does not
transport Case 2 gap or flat-tail packages automatically, and does not prove
chart coverage, transition regularity, Jacobian arithmetic, normal crossings,
RLCT extraction, termination, transition invariance, or printed-vector repair.

## 2026-06-20 Lean Case 2 terminal relabel-weight candidate

Reproduction:
`reproduction-case2-terminal-relabel-weight-candidate-a4.md`.
Statement card:
`statement-card-a4-case2-terminal-relabel-weight-candidate.md`.
Review artifact:
`review-case2-terminal-relabel-weight-candidate-a4.md`.

Lean now rewrites the stopped displayed Case 2 terminal product using the
relabelled `(S+1,0)` post-state pivot weight.  Under actual next-width
exhaustion, the old supplied post-state weight and the relabelled post-state
weight agree:

```text
terminalRelabelPost.weight(J+1) = post.weight(J+1).
```

The direct wrapper combines this equality with the stopped terminal
entry-ideal theorem.  A second source-model wrapper specializes the supplied
terminal source model to

```text
b0 = terminalRelabelPost.weight(J+1).
```

The latest bridge-consumer checkpoint also applies the same relabelled scalar
to the source old-top/source suffix theorem through a supplied terminal
`Cterm`.  This still assumes `SuppliedTerminalCprimeBridge`; it does not
construct the terminal next matrix.

This is only a presentational bridge from the terminal candidate to relabelled
recurrence vocabulary.  It does not construct source-produced `C'^(S+1)`,
does not prove chart production, does not transport Case 2 gap/tail packages,
and does not prove chart coverage, transition regularity, Jacobian arithmetic,
normal crossings, RLCT extraction, termination, transition invariance, or
printed-vector repair.

## 2026-06-20 Lean Case 2 source-chart terminal model constructor

Reproduction:
`reproduction-case2-source-chart-terminal-model-constructor-a4.md`.
Statement card:
`statement-card-a4-case2-source-chart-terminal-model-constructor.md`.
Review artifact:
`review-case2-source-chart-terminal-model-constructor-a4.md`.

Lean now combines the displayed source-chart constructor with the actual-width
terminal relabel-model wrapper.  The theorem starts from the concrete boundary
produced by `of_sourceChartMap_case2Succ_updateSelected`, so the successor
state is

```text
pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1))
```

and the exponent post-data are the corrected selected-label overrides.  It
then applies the terminal source-model entry-ideal theorem to a model indexed
by the concrete relabelled post-state pivot weight.

This removes arbitrary recurrence/exponent post-data from this terminal
wrapper but still keeps the chart-family predicates and terminal old-top/suffix
data supplied.  It does not construct source-produced `C'^(S+1)`, prove chart
coverage or regularity from coordinates, prove Jacobian arithmetic, normal
crossings, RLCT extraction, termination, transition invariance, automatic
gap/tail transport, or printed-vector repair.

## 2026-06-20 Lean Case 2 actual-width column exhaustion

Reproduction:
`reproduction-case2-actual-width-column-exhaustion-a4.md`.
Statement card:
`statement-card-a4-case2-actual-width-column-exhaustion.md`.
Review artifact:
`review-case2-actual-width-column-exhaustion-a4.md`.

Lean now records the exhausted side of the displayed terminal branch under
actual next-width exhaustion.  If

```text
n(S+1)=J+1,
```

then the post-pivot residual column range `J+2..n(S+1)` is empty, and hence
the displayed pivot's column complement is empty.  The actual-width terminal
source model exports the same fact.

This is finite-domain bookkeeping only.  It does not construct
`C'^(S+1)`, source-produced following-factor data, chart production, chart
coverage, Jacobian arithmetic, normal crossings, RLCT extraction, termination,
transition invariance, automatic gap/tail transport, or printed-vector repair.

## 2026-06-20 Lean Case 2 current-prefix row exhaustion

Reproduction:
`reproduction-case2-current-prefix-row-exhaustion-a4.md`.
Statement card:
`statement-card-a4-case2-current-prefix-row-exhaustion.md`.
Review artifact:
`review-case2-current-prefix-row-exhaustion-a4.md`.

Lean now records the row-exhausted side of the displayed terminal branch under
current-prefix exhaustion.  If

```text
prefixMinNat n S=J+1,
```

then the post-pivot residual row range `J+2..prefixMinNat n S` is empty, and
hence the displayed pivot's row complement is empty.

This is finite-domain bookkeeping only.  It is independent of actual-width
exhaustion and is not a projection from the actual-width terminal source
model.  It does not construct `C'^(S+1)`, source-produced following-factor
data, chart production, chart coverage, Jacobian arithmetic, normal crossings,
RLCT extraction, termination, transition invariance, automatic gap/tail
transport, or printed-vector repair.

## 2026-06-20 Lean Case 2 source old-top/suffix specialization

Reproduction:
`reproduction-case2-source-old-top-suffix-specialization-a4.md`.
Statement card:
`statement-card-a4-case2-source-old-top-suffix-specialization.md`.
Review artifact:
`review-case2-source-old-top-suffix-specialization-a4.md`.

Lean now specializes the stopped displayed Case 2 terminal theorem to source
old-top data.  The old top row type is `1..J`; the old top multiplier is
`diag(pre.weight i)` on these rows; and the old top block is the restriction
`C(i,t)` of the supplied source-coordinate following matrix to rows `1..J`.
The theorem applies the already proved stopped terminal entry-ideal equality
with these old-top choices.

The suffix `F` remains supplied, representing Aoyagi's remaining right product
but not yet constructed as a matrix chain.  This checkpoint does not construct
source-produced `C'^(S+1)`, chart-produced recurrence or exponent data, chart
coverage, Jacobian arithmetic, normal crossings, RLCT extraction, termination,
transition invariance, automatic gap/tail transport, or printed-vector repair.

## 2026-06-20 Lean Case 2 source suffix chain

Reproduction:
`reproduction-case2-source-suffix-chain-a4.md`.
Statement card:
`statement-card-a4-case2-source-suffix-chain.md`.
Review artifact:
`review-case2-source-suffix-chain-a4.md`.

Lean now names a raw paper-order matrix-chain product and the remaining Case 2
terminal suffix `prod_{s=S+2}^L C^(s)`. The raw chain extends the upper
endpoint by right multiplication, matching Aoyagi's paper-order product. The
source suffix wrapper starts at one-based source layer `S+2` and ends at layer
`L+1`, with the empty suffix represented by the raw chain identity when
`S+1=L`.

The stopped source old-top terminal theorem is also instantiated with
`F = sourceSuffixProduct`. This removes the previous supplied suffix from that
wrapper only by naming the matrix chain. It still does not prove that
`[Ctop;C0]` is source-produced `C'^(S+1)`, nor does it prove chart production,
chart coverage, coordinate regularity, Jacobian arithmetic, normal crossings,
RLCT extraction, termination, transition invariance, automatic Case 2
gap/tail transport, or printed-vector repair.

## 2026-06-20 Lean Case 2 source terminal product candidate

Reproduction:
`reproduction-case2-source-terminal-product-candidate-a4.md`.
Statement card:
`statement-card-a4-case2-source-terminal-product-candidate.md`.
Review artifact:
`review-case2-source-terminal-product-candidate-a4.md`.

Lean now packages the stopped displayed Case 2 terminal candidate in one-based
source-row order.  The row equivalence

```text
case2SourceOldTopRowIndex J ⊕ Unit ≃ case2SourceTerminalRowIndex J
```

maps old source rows `1..J` to themselves and the surviving pivot row to
`J+1`.  The new source-row objects are explicitly candidates/reindexed
presentations:

```text
case2DisplayedSourceTerminalCprimeCandidate
case2DisplayedSourceTerminalProductReindexedCandidate
```

The stopped source old-top/source suffix theorem is restated with the
source-row reindexed terminal product candidate on the right hand side.  This
is still a reindexing of supplied terminal data.  It does not prove
source-produced `C'^(S+1)`, and does not prove chart production, coverage,
Jacobians, normal crossings/RLCT, termination, transition invariance,
automatic Case 2 gap/tail transport, or printed-vector repair.

## 2026-06-20 Lean Case 2 source terminal product form

Reproduction:
`reproduction-case2-source-terminal-product-form-a4.md`.
Statement card:
`statement-card-a4-case2-source-terminal-product-form.md`.
Review artifact:
`review-case2-source-terminal-product-form-a4.md`.

Lean now proves that the source-row terminal product candidate is exactly the
product of the separately named source-row terminal weight and source-row
terminal next-factor candidate, followed by the supplied suffix:

```text
case2DisplayedSourceTerminalProductReindexedCandidate
  =
(case2DisplayedSourceTerminalWeight *
  case2DisplayedSourceTerminalCprimeCandidate) * F.
```

The proof is pure matrix reindexing: `Matrix.submatrix_mul_equiv` is applied
to the final multiplication by `F`, then to the terminal weight times terminal
next-factor product.  This closes the product-form packaging gap for the
existing reindexed candidate.  It still does not prove source-produced
`C'^(S+1)`, chart production, coverage, Jacobians, normal crossings/RLCT,
termination, transition invariance, automatic Case 2 gap/tail transport, or
printed-vector repair.

## 2026-06-20 Lean Case 2 terminal frontier bridges

Reproduction:
`reproduction-case2-terminal-frontier-bridges-a4.md`.
Statement card:
`statement-card-a4-case2-terminal-frontier-bridges.md`.
Review artifact:
`review-case2-terminal-frontier-bridges-a4.md`.

Lean now bridges the stopped source-row terminal candidate to Aoyagi's
terminal prefix row range.  Under

```text
J+1 <= prefixMinNat n (S+1)
not (J+2 <= prefixMinNat n (S+1)),
```

the terminal prefix row type `1..M(S+1)` is equivalent to the already used
source-row type `1..J+1`.  The source terminal weight, `C'` candidate, and
terminal product candidate are reindexed onto this terminal prefix row type,
and the stopped source old-top/source suffix theorem is restated with that
prefix-row product candidate on the right.

The same checkpoint adds a supplied terminal matrix handoff: if a supplied
matrix has old rows `C(i,-)` for `i=1..J` and pivot row equal to the top row
of `Q^-1 C`, then the existing source-row terminal product candidate rewrites
to `(source terminal weight * supplied Cterm) * F`.  The row equations are
also packaged as `SuppliedTerminalCprimeBridge`, with projections to the
candidate equality and product rewrite.  A follow-up Lean checkpoint consumes
the same bridge in the terminal-prefix product and in the stopped source
old-top/source suffix theorem, so downstream statements can mention the
supplied terminal `Cterm` directly without constructing it from chart
coordinates.

The latest Lean checkpoint also expands the surviving top row of the
transported following factor `Q^-1 C`: it is `C(J+1,-)` plus the displayed
pivot-row weighted sum over post-pivot actual columns.  The same checkpoint
adds the prefix-row source-suffix consumer, so the stopped source old-top/source
suffix theorem can be rewritten through a supplied terminal `Cterm` after
reindexing to terminal prefix rows.

This is still not chart production.  In the row-exhausted wide-next case,
actual rows beyond `M(S+1)` belong to the transported following factor but not
to the terminal prefix object.  No recurrence/exponent relabel is inferred
from prefix exhaustion.

## 2026-06-20 Lean Case 2 actual-width original-row terminal bridge

Reproduction:
`reproduction-case2-terminal-frontier-bridges-a4.md`.
Statement card:
`statement-card-a4-case2-terminal-frontier-bridges.md`.
Review artifact:
`review-case2-terminal-frontier-bridges-a4.md`.

Lean now specializes the supplied terminal bridge in the actual next-width
exhausted subcase `n(S+1)=J+1`.  The displayed pivot-column complement is
empty, so the top row of `Q^-1 C` is exactly the original source row
`C(J+1,-)`.  Therefore the source-row terminal `C'` candidate is the original
source following rows `1..J+1`, and
`SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq` supplies the
bridge with that concrete terminal matrix.

The relabelled source old-top/source suffix theorem is also specialized to
this original-row terminal matrix.  This is only the actual-width
column-exhausted branch; it is not a theorem for failed next-continuation
alone, prefix exhaustion, or the row-exhausted wide-next case, and it does not
prove chart coverage, Jacobian arithmetic, normal crossings/RLCT, termination,
transition invariance, or automatic Case 2 gap/tail transport.

## 2026-06-20 Lean Case 2 row-exhausted transported terminal

Reproduction:
`reproduction-case2-row-exhausted-transported-terminal-a4.md`.
Statement card:
`statement-card-a4-case2-row-exhausted-transported-terminal.md`.
Review artifact:
`review-case2-row-exhausted-transported-terminal-a4.md`.

Lean now records the other stopped side without collapsing it to the
actual-width case.  Current-prefix row exhaustion
`prefixMinNat n S=J+1` forces failed next continuation, so the existing
terminal-prefix product theorem can be consumed directly in that branch.

The checkpoint also names an explicit transported-row terminal matrix.  Rows
`1..J` are original source rows, while row `J+1` is the top row of `Q^-1 C`.
This matrix supplies `SuppliedTerminalCprimeBridge`, and the row-exhausted
source old-top/source suffix theorem is rewritten through its terminal-prefix
submatrix.  In wide-next row-exhausted cases, this last row may include the
post-pivot column correction sum; no original-row equality or `(S+1,0)`
recurrence relabel is claimed.

## 2026-06-20 Lean Case 2 source-chart terminal source-suffix

Reproduction:
`reproduction-case2-source-chart-terminal-source-suffix-a4.md`.
Statement card:
`statement-card-a4-case2-source-chart-terminal-source-suffix.md`.
Review artifact:
`review-case2-source-chart-terminal-source-suffix-a4.md`.

Lean now composes the concrete displayed source-chart boundary constructor
with the two stopped terminal source-suffix branches.  The actual-width theorem

```text
exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
```

uses `n(S+1)=J+1` to specialize the terminal rows to the original source rows
`1..J+1` and the relabelled successor weight.  The row-exhausted theorem

```text
exists_sourceChart_oldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
```

uses `prefixMinNat n S=J+1` and keeps row `J+1` as the transported top row of
`Q^-1 C`.

Both wrappers fix the post recurrence state to
`pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1))` and use the
corrected selected-label exponent overrides from
`of_sourceChartMap_case2Succ_updateSelected`.  They still leave the
chart-family predicates, source following rows, and suffix matrix chain
supplied.  They do not prove source-produced `C'^(S+1)`, chart coverage,
chart-produced post-data, Jacobian arithmetic, normal crossings/RLCT,
termination, transition invariance, automatic gap/tail transport, or printed
vector repair.

## 2026-06-20 Lean source suffix raw chain split

Reproduction:
`reproduction-source-suffix-chain-split-a4.md`.
Statement card:
`statement-card-a4-source-suffix-chain-split.md`.
Review artifact:
`review-source-suffix-chain-split-and-actual-width-boundary-a4.md`.

Lean now proves the raw paper-order chain split

```text
paperMatrixChain_trans
```

in `MatrixChain.lean`.  If `i <= m <= j`, then

```text
paperMatrixChain(i,j) = paperMatrixChain(i,m) * paperMatrixChain(m,j).
```

The orientation matches the existing raw chain convention: extending the upper
endpoint multiplies by the new paper edge on the right.  This is only raw
matrix-chain algebra.  It does not yet state the dependent-endpoint
`sourceSuffixProduct` empty or peel wrappers, and it does not prove chart
production or any analytic result.

## 2026-06-20 Lean Case 2 actual-width source-chart terminal boundary

Reproduction:
`reproduction-case2-actual-width-source-chart-terminal-boundary-a4.md`.
Statement card:
`statement-card-a4-case2-actual-width-source-chart-terminal-boundary.md`.
Review artifact:
`review-source-suffix-chain-split-and-actual-width-boundary-a4.md`.

Lean now packages the actual-width displayed source-chart terminal branch as

```text
sourceChart_actualWidth_terminalOriginalRowsBoundary.
```

The theorem composes three already proved facts: the source-chart terminal
source-suffix equality with original rows, the actual-width relabelled
level/least-value invariant, and the actual-width relabelled exponent-domain
certificate.  It is restricted to `n(S+1)=J+1`, where the transported pivot row
is the original source row and the `(S+1,0)` relabel is valid.

This is a boundary package, not a source-production theorem.  It does not
prove source-produced `C'^(S+1)`, chart coverage, chart-produced post-data,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, automatic gap/tail transport, or printed-vector repair.

## 2026-06-20 Lean source suffix utilities

Reproduction:
`reproduction-source-suffix-utilities-a4.md`.
Statement card:
`statement-card-a4-source-suffix-utilities.md`.
Review artifact:
`review-source-suffix-utilities-a4.md`.

Lean now adds three source-suffix utilities in `MatrixChain.lean`:

```text
sourceSuffixProduct_proof_irrel
sourceSuffixProduct_eq_paperMatrixChain
sourceSuffixProduct_split_at
```

They expose the raw suffix `prod_{s=S+2}^L C^(s)` as a proof-irrelevant
paper-order chain and split it at a one-based source layer `T`, under
`S+2 <= T <= L+1`.  Endpoint splits are allowed, but the endpoint identity
simplifications are not proved here.

This is still raw chain API.  It does not prove the one-edge source-suffix
peel, the empty-suffix identity, source-produced `C'^(S+1)`, chart coverage,
chart-produced post-data, Jacobian arithmetic, normal crossings/RLCT,
termination, transition invariance, or printed-vector repair.

## 2026-06-20 Lean source suffix one-edge peel

Reproduction:
`reproduction-source-suffix-peel-a4.md`.
Statement card:
`statement-card-a4-source-suffix-peel.md`.
Review artifact:
`review-source-suffix-peel-a4.md`.

Lean now proves the raw first-edge peel

```text
paperMatrixChain_succ_left
```

and the source-suffix wrapper

```text
sourceSuffixProduct_peel.
```

Under `S+2 <= L`, the source suffix rewrites as

```text
sourceSuffixProduct(S)
  = sourceSuffixFirstEdge(S) * sourceSuffixProduct(S+1).
```

The factor `sourceSuffixFirstEdge(S)` is the supplied source edge `C^(S+2)`
with endpoints reindexed as the adjacent source-suffix layers.  This is still
raw matrix-chain algebra.  It does not prove the empty-suffix identity,
source-produced `C'^(S+1)`, chart coverage, chart-produced post-data,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair.

## 2026-06-20 Lean Case 2 arbitrary-suffix terminal wrapper

Reproduction:
`reproduction-case2-arbitrary-suffix-terminal-wrapper-a4.md`.
Statement card:
`statement-card-a4-case2-arbitrary-suffix-terminal-wrapper.md`.
Review artifact:
`review-case2-arbitrary-suffix-terminal-wrapper-a4.md`.

Lean now adds arbitrary supplied-suffix companions to the stopped source-row
terminal wrappers:

```text
exists_sourceOldTopSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont
exists_sourceOldTopSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont
exists_oldTopSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth
exists_oldTopSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth
```

These theorems keep the following product as an arbitrary supplied matrix `F`
instead of immediately specializing to `sourceSuffixProduct`.  The actual-width
original-row specialization still requires `n(S+1)=J+1`; it does not apply to
the row-exhausted wide-next branch.  This is terminal-product packaging and
source-row reindexing only.  It does not prove that `F` is produced by the
chart, source-produced `C'^(S+1)`, chart coverage, chart-produced post-data,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair.

## 2026-06-20 Lean Case 2 source-chart arbitrary-suffix actual-width boundary

Reproduction:
`reproduction-case2-source-chart-arbitrary-suffix-actual-width-a4.md`.
Statement card:
`statement-card-a4-case2-source-chart-arbitrary-suffix-actual-width.md`.
Review artifact:
`review-case2-source-chart-arbitrary-suffix-actual-width-a4.md`.

Lean now adds a concrete displayed source-chart actual-width terminal boundary
with the following product kept as an arbitrary supplied matrix:

```text
exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth
sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary
```

This composes the displayed source-chart constructor with the arbitrary-`F`
actual-width original-row wrapper.  It fixes the successor recurrence state to
`pre.case2Succ(chartMap(J+1,J+1))`, uses corrected selected-label exponent
overrides, and packages the actual-width relabelled `(S+1,0)` level/exponent
certificates.  The following matrix `F` remains supplied.  The theorem does
not apply to row-exhausted wide-next cases and does not prove chart coverage,
source-produced `C'^(S+1)`, chart-produced following product, Jacobian
arithmetic, normal crossings/RLCT, termination, transition invariance, or
printed-vector repair.

## 2026-06-20 Lean Case 2 principalized source-chart actual-width boundary

Reproduction:
`reproduction-case2-principalized-source-chart-actual-width-a4.md`.
Statement card:
`statement-card-a4-principalized-source-chart-actual-width.md`.
Review artifact:
`review-case2-principalized-source-chart-actual-width-a4.md`.

Lean now packages the concrete displayed source-chart actual-width terminal
boundary with finite residual-block center principalization:

```text
sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal
```

This theorem combines the arbitrary-`F` actual-width original-row terminal
boundary with the finite center facts that the displayed selected variable
`u` occurs among the transformed center values, divides every transformed
finite center value, and generates the transformed finite center ideal.  The
following matrix `F` and the residual-block `chartFamily` remain supplied, and
the original-row branch still requires `n(S+1)=J+1`.

This does not principalize the terminal product ideal and does not prove chart
coverage, source-produced `C'^(S+1)`, chart-produced following product,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair.

## 2026-06-20 Lean source suffix terminal-last identity

Reproduction:
`reproduction-source-suffix-terminal-last-a4.md`.
Statement card:
`statement-card-a4-source-suffix-terminal-last.md`.
Review artifact:
`review-source-suffix-terminal-last-a4.md`.

Lean now proves the terminal-last empty source suffix identity:

```text
sourceLayerIndex_terminalLast
sourceSuffixProduct_terminalLast_eq_cast_one
```

Under `S+1=L`, the lower source-suffix endpoint `S+2` is the final source
layer.  The raw suffix is therefore the empty paper-order chain.  Since Lean
sees the lower endpoint and final endpoint as propositionally equal rather
than definitionally identical, the theorem states the identity matrix
transported along `sourceLayerIndex L (S+2)=Fin.last L`.

This is raw matrix-chain algebra only.  It supplies the identity needed by
terminal-last wrappers whose following factor is exactly this source suffix;
it does not justify setting an arbitrary following matrix to `1` away from the
empty-suffix case, and it does not prove chart production, source-produced
`C'^(S+1)`, Jacobian arithmetic, normal crossings/RLCT, termination,
transition invariance, or printed-vector repair.

## 2026-06-20 Lean Case 2 identity-following actual-width boundary

Reproduction:
`reproduction-case2-identity-following-actual-width-a4.md`.
Statement card:
`statement-card-a4-case2-identity-following-actual-width.md`.
Review artifact:
`review-case2-identity-following-actual-width-a4.md`.

Lean now proves the identity-following specialization of the displayed
source-chart actual-width terminal boundary:

```text
sourceChart_actualWidth_terminalOriginalRowsIdentityFollowingBoundary
```

This is the `F = 1` specialization of
`sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary`.  It
removes the rightmost following factor and keeps the actual-width original-row
condition `n(S+1)=J+1`, the pre-state certificates, the least-value gap, and
the supplied chart-family interface explicit.

This theorem does not prove that a source suffix is empty; the raw suffix
identity is the separate theorem `sourceSuffixProduct_terminalLast_eq_cast_one`.
It does not apply to row-exhausted wide-next cases and does not prove chart
coverage, source production of `C'^(S+1)`, chart-produced following products,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair.

## 2026-06-20 Lean Case 2 terminal-last actual-width boundary

Reproduction:
`reproduction-case2-terminal-last-actual-width-a4.md`.
Statement card:
`statement-card-a4-case2-terminal-last-actual-width.md`.
Review artifact:
`review-case2-terminal-last-actual-width-a4.md`.

Lean now proves the actual-width source-chart terminal boundary in the
terminal-last case:

```text
matrixEntryIdeal_mul_ndrec_one
matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast
exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_originalRowsProduct_of_actualWidth
sourceChart_actualWidth_terminalLastOriginalRowsBoundary
```

The theorem consumes the raw source suffix
`sourceSuffixProduct κ Ctail S hSuffix` and the terminal-last condition
`S+1=L`.  The suffix is removed only through the transported empty-chain
identity `sourceSuffixProduct_terminalLast_eq_cast_one`, then at the
matrix-entry-ideal level.  The boundary still requires actual-width exhaustion
`n(S+1)=J+1` to identify the terminal row stack with original source rows
`1..J+1`.

This is the actual-width terminal-last branch only.  The row-exhausted
wide-next branch uses transported prefix rows and remains separate from
original-row equality.  The theorem does not prove chart coverage, source
production of `C'^(S+1)`, chart-produced following products, Jacobian
arithmetic, normal crossings/RLCT, termination, transition invariance, or
printed-vector repair.

## 2026-06-20 Lean Case 2 terminal-last row-exhausted boundary

Reproduction:
`reproduction-case2-terminal-last-row-exhausted-a4.md`.
Statement card:
`statement-card-a4-case2-terminal-last-row-exhausted.md`.
Review artifact:
`review-case2-terminal-last-row-exhausted-a4.md`.

Lean now proves the row-exhausted transported-prefix terminal boundary in the
terminal-last case:

```text
exists_sourceOldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted
```

The theorem consumes the raw source suffix
`sourceSuffixProduct κ Ctail S hSuffix` and the terminal-last condition
`S+1=L`.  The suffix is removed only through the transported empty-chain
identity `sourceSuffixProduct_terminalLast_eq_cast_one`, then at the
matrix-entry-ideal level.  The stopped branch uses current-prefix row
exhaustion `prefixMinNat n S=J+1`.

This is not an original-row theorem.  The terminal side remains the transported
prefix-row matrix, whose row `J+1` is the top row of `Q^-1 C`; in wide-next
cases it may include post-pivot column corrections.  The theorem does not
relabel recurrence/exponent data to `(S+1,0)` and does not prove chart
coverage, source production of `C'^(S+1)`, chart-produced following products,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair.

## 2026-06-20 Lean Case 2 principalized terminal-last boundaries

Reproduction:
`reproduction-case2-principalized-terminal-last-boundaries-a4.md`.
Statement card:
`statement-card-a4-principalized-terminal-last-boundaries.md`.
Review artifact:
`review-case2-principalized-terminal-last-boundaries-a4.md`.

Lean now packages both terminal-last source-chart branches with finite
residual-block center principalization:

```text
sourceChart_actualWidth_terminalLastOriginalRowsBoundary_withFiniteCenterIdeal
sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal
```

Both packages record that the selected variable `u` is a transformed finite
center value, divides every transformed finite center value, and generates the
transformed finite center ideal.  The actual-width package conjoins these facts
with the terminal-last original-row boundary and relabelled `(S+1,0)`
certificates.  The row-exhausted package conjoins them with the terminal-last
transported-prefix boundary and keeps the row `J+1` as the top row of
`Q^-1 C`.

These are finite-center packages only.  They do not principalize the terminal
product ideal and do not prove chart coverage, source production of
`C'^(S+1)`, chart-produced following products, Jacobian arithmetic, normal
crossings/RLCT, termination, transition invariance, or printed-vector repair.

## 2026-06-20 Lean Case 2 post-pivot domain handoff

Reproduction:
`reproduction-case2-post-pivot-domain-handoff-a4.md`.
Statement card:
`statement-card-a4-case2-post-pivot-domain-handoff.md`.
Review artifact:
`review-case2-post-pivot-domain-handoff-a4.md`.

Lean now records that the lower-right finite domain after deleting the
displayed Case 2 pivot `(J+1,J+1)` is exactly the next same-stage residual
center at `(S,J+1)`:

```text
case2PostPivotRows_eq_case2ResidualBlockRows_succ
case2PostPivotCols_eq_case2ResidualBlockCols_succ
case2PostPivotEntries_eq_case2ResidualBlockPivotEntries_succ
case2ResidualBlockPivotEntries_succ_nonempty_iff_next_cont
case2DisplayedPivotRowComplementEquivResidualRowSucc
case2DisplayedPivotColComplementEquivResidualColSucc
```

The nonemptiness wrapper keeps the required `1<=S` hypothesis for the
prefix-minimum recurrence and says the next residual center is nonempty iff
`J+2<=prefixMinNat n (S+1)`.

This is finite domain bookkeeping only.  It does not produce the next residual
matrix, chart coverage, transition invariance, transition regularity, Jacobian
arithmetic, terminal-product principalization, normal crossings, RLCT
extraction, or the terminal `(S+1,0)` relabel branch.

## 2026-06-20 Lean Case 2 post-pivot next-block adapter

Reproduction:
`reproduction-case2-post-pivot-next-block-a4.md`.
Statement card:
`statement-card-a4-case2-post-pivot-next-block.md`.
Review artifact:
`review-case2-post-pivot-next-block-a4.md`.

Lean now names the continuing displayed Case 2 post-pivot lower-right block
and transported following-factor tail over the next same-stage residual
domains:

```text
weightedPivotClearedBlock_mul_verticalBlock
case2DisplayedPostPivotResidualBlock
case2DisplayedPostPivotFollowingFactor
case2DisplayedPostPivotResidualBlock_nonempty_of_next
case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct
```

The residual block is the cleared lower-right expression `D - x*y`, reindexed
from displayed pivot complements to `Case2ResidualRowIndex n S (J+1)` and
`Case2ResidualColIndex n S (J+1)`.  The following factor is the tail of
`C' = Q^-1 C`, reindexed to the same next column domain.  The product theorem
says that the lower rows of `D''' * C'`, under the same row reindexing, are
exactly the product of these two supplied next-block objects.

This is a continuing-branch supplied-data adapter only.  It does not prove
chart production, recurrence/exponent post-data from coordinates, chart
coverage, coordinate regularity, transition invariance, Jacobian arithmetic,
normal crossings, RLCT extraction, arbitrary pivot coverage, the terminal
`(S+1,0)` relabel branch, or repair of the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 source-chart post-pivot boundary

Reproduction:
`reproduction-case2-source-chart-post-pivot-boundary-a4.md`.
Statement card:
`statement-card-a4-case2-source-chart-post-pivot-boundary.md`.
Review artifact:
`review-case2-source-chart-post-pivot-boundary-a4.md`.

Lean now connects the corrected displayed source-chart boundary to the
continuing-branch post-pivot next-block adapter:

```text
Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct
Case2DisplayedSuppliedChartFamilyBoundary.postPivotResidualBlock_nonempty_of_next
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_postPivotNextSameStageProduct_withCorrectedPostData
```

The first projection says that any supplied displayed Case 2 boundary exposes
the lower rows of the paper product `D''' * C'` as the supplied
`(S,J+1)` next-block product.  The nonemptiness projection keeps the explicit
continuing bound `J+2 <= prefixMinNat n (S+1)`.  The source-chart package
instantiates the concrete boundary constructor with post state `pre.case2Succ`
at the displayed source-chart pivot value and conjoins the product identity
with the corrected post-data projections: exponent-domain extension, post
level/least-value invariants, successor least-value Case 2 gap, and successor
recurrence Case 2 gap.

This is still supplied-data compatibility.  It does not prove chart production
of recurrence or exponent data, construct a successor chart-family boundary,
prove chart coverage, coordinate regularity, transition invariance, Jacobian
arithmetic, normal crossings/RLCT, arbitrary pivot coverage, terminal
relabeling, or repair the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 post-pivot following-factor tail

Reproduction:
`reproduction-case2-post-pivot-following-factor-tail-a4.md`.
Statement card:
`statement-card-a4-case2-post-pivot-following-factor-tail.md`.
Review artifact:
`review-case2-post-pivot-following-factor-tail-a4.md`.

Lean now records the elementary tail consequence of Aoyagi's displayed
following-factor update `C' = Q^-1 C`:

```text
pivotQinv_mul_tail_apply
case2DisplayedPaperCprimeTail_apply
case2DisplayedPostPivotFollowingFactor_eq_sourceFollowingFactor_succ
```

Because `Q^-1 = [1 y; 0 I]`, only the pivot row of the following factor
changes.  The lower tail of `C'`, after the displayed pivot-column complement
is reindexed to the next same-stage residual-column domain, is exactly the
source following factor restricted to `(S,J+1)` columns.  The checkpoint also
adds raw-value simp lemmas for the displayed pivot-complement equivalences to
the next same-stage row and column domains.

This is still finite following-factor algebra and reindexing.  It does not
identify the tail with Aoyagi's full next `C'^(S+1)`, prove chart production
of recurrence or exponent data, construct a successor chart-family boundary,
prove chart coverage, coordinate regularity, transition invariance, Jacobian
arithmetic, normal crossings/RLCT, arbitrary pivot coverage, terminal
relabeling, or repair the printed Case 2 vector mismatch.

## 2026-06-20 Lean Case 2 post-pivot source-following product

Reproduction:
`reproduction-case2-post-pivot-source-following-product-a4.md`.
Statement card:
`statement-card-a4-case2-post-pivot-source-following-product.md`.
Blocked audit:
`blocked-audit-case2-chart-production-next-following-a4.md`.
Review artifact:
`review-case2-post-pivot-source-following-product-a4.md`.

Lean now combines the continuing post-pivot next-block adapter with the
following-factor tail identity:

```text
case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct_sourceFollowingFactor
Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct_sourceFollowingFactor
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData
```

The raw theorem rewrites the lower rows of Aoyagi's displayed product
`D''' * C'`, after reindexing to the next same-stage row domain, as the
post-pivot residual block times the original source following factor
restricted to `(S,J+1)` columns.  The boundary theorem exports the same
identity from a supplied displayed boundary.  The concrete source-chart
package conjoins the source-following product identity with the corrected
supplied post-data projections.

The xhigh source/API audit found no honest stronger theorem, from the current
PDF evidence and Lean API, that would prove chart-produced recurrence data,
chart-produced corrected exponent data, a successor chart-family boundary,
full source-produced `C'^(S+1)`, or a transition invariant.  Future work must
either build an independent selected-entry atlas/transition construction or
continue proving finite algebraic consequences beneath the supplied-boundary
interface.

This checkpoint is still a continuing-branch supplied-data adapter.  It does
not prove chart production, successor chart-family construction, full
source-produced next `C'^(S+1)`, transition invariance, chart coverage,
Jacobian arithmetic, normal crossings/RLCT, terminal relabeling, arbitrary
pivot coverage, or printed-vector repair.

## 2026-06-20 Lean Case 2 constructed `Cprime`

Reproduction:
`reproduction-case2-constructed-cprime-a4.md`.
Statement card:
`statement-card-a4-case2-constructed-cprime.md`.
Review artifact:
`review-case2-constructed-cprime-a4.md`.

Lean now proves the reverse coordinate direction for the displayed Case 2
following-factor operation:

```text
case2DisplayedPaperConstructedFollowingFactor
case2DisplayedPaperCprime_of_constructedFollowingFactor
case2DisplayedPaperDpp_mul_constructedCprime
```

Given an arbitrary pivot-first chart-coordinate following factor `Cprime`,
the constructed old pivot-first following factor is `Q*Cprime`.  Applying
`Q^-1` recovers `Cprime`, and the product identity becomes
`D''*Cprime = D_chart*(Q*Cprime)`.

This is finite pivot-first matrix algebra only.  It does not construct a
total source-coordinate function from `Cprime`, produce recurrence or exponent
post-data, construct the successor chart family, prove chart coverage or
regularity, compute Jacobians, prove normal crossings/RLCT, handle arbitrary
pivots, terminal relabeling, or repair the printed Case 2 vector.

## 2026-06-20 Lean Case 2 constructed `Cprime` `Q/P`

Reproduction:
`reproduction-case2-constructed-cprime-qp-a4.md`.
Statement card:
`statement-card-a4-case2-constructed-cprime-qp.md`.
Review artifact:
`review-case2-constructed-cprime-qp-a4.md`.

Lean now combines the constructed-`Cprime` coordinate direction with the
displayed Case 2 `Q/P` row operation:

```text
exists_case2DisplayedQP_mul_arbitraryPivotFirstFollowingFactor_of_flat_weights
CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_freeFollowingFactor_of_postData
Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedCprime_paperQP
```

Given a free pivot-first chart-coordinate following factor `Cprime`, the old
pivot-first following factor is `Q*Cprime`.  The supplied-boundary theorem
rewrites

```text
(P * weighted source-substituted block) * (Q*Cprime)
```

as

```text
(weighted D''') * Cprime.
```

This is finite pivot-first product algebra only.  It does not construct a
total source-coordinate following function from `Cprime`, source-produce next
`C'^(S+1)`, produce recurrence or exponent post-data, construct the successor
chart family, prove chart coverage or regularity, compute Jacobians, prove
normal crossings/RLCT, handle arbitrary pivots, terminal relabeling, or repair
the printed Case 2 vector.

## 2026-06-21 Lean Case 2 constructed source following factor

Reproduction:
`reproduction-case2-constructed-source-following-factor-a4.md`.
Statement card:
`statement-card-a4-case2-constructed-source-following-factor.md`.
Review artifact:
`review-case2-constructed-source-following-factor-a4.md`.

Lean now fills the source-coordinate gap left by the pivot-first constructed
`Cprime` checkpoints:

```text
case2DisplayedConstructedSourceFollowingFactor
case2DisplayedSourceFollowingFactor_constructed
case2DisplayedPaperCprime_of_constructedSourceFollowingFactor
Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedSourceFollowingFactor_paperQP
```

Given any pivot-first following matrix on the old displayed residual columns,
Lean defines a total source-coordinate function by transporting entries back
through the pivot-first equivalence and setting all non-residual columns to
zero.  Restricting this function with
`case2DisplayedSourceFollowingFactor` recovers the supplied matrix exactly.
For the constructed matrix `Q*Cprime`, the paper-named update
`C' = Q^-1 C` therefore recovers the free chart coordinate `Cprime`, and the
supplied-boundary `Q/P` identity can be stated with the old following factor
represented as a total source-coordinate function.

This is still finite source-coordinate bookkeeping and matrix algebra.  It
does not source-produce the full next `C'^(S+1)`, produce recurrence or
exponent post-data, construct a successor chart family, prove chart coverage
or regularity, compute Jacobians, prove normal crossings/RLCT, handle
arbitrary pivots, terminal relabeling, or repair the printed Case 2 vector.

## 2026-06-21 Lean Case 2 displayed frontier branch

Reproduction:
`reproduction-case2-displayed-frontier-branch-a4.md`.
Statement card:
`statement-card-a4-case2-displayed-frontier-branch.md`.
Review artifact:
`review-case2-displayed-frontier-branch-a4.md`.

Lean now records the finite frontier alternatives after the displayed Case 2
pivot:

```text
Case2DisplayedStepBranch
case2DisplayedFrontier_next_or_actualWidth_or_rowExhausted_of_cont
case2DisplayedStepBranch_of_cont
Case2DisplayedSuppliedChartFamilyBoundary.frontierBranch
```

Under displayed pivot validity `J+1 <= prefixMinNat n (S+1)`, Lean proves that
either `J+2 <= prefixMinNat n (S+1)`, or actual next-width exhaustion
`n(S+1)=J+1`, or current-prefix row exhaustion
`prefixMinNat n S=J+1`.  The stopped alternatives are explicitly not claimed
to be mutually exclusive.  A supplied displayed boundary exports this as a
branch witness using only its `stage_pos` and `continuation` fields.

This is finite domain bookkeeping only.  It does not combine the existing
branch-specific product packages, construct a chart, produce recurrence or
exponent post-data, construct a successor chart-family boundary, prove
transition invariance, compute Jacobians, prove normal crossings/RLCT, or
repair the printed Case 2 vector mismatch.

## 2026-06-21 Lean Case 2 source-chart frontier packages

Reproduction:
`reproduction-case2-source-chart-frontier-packages-a4.md`.
Statement card:
`statement-card-a4-case2-source-chart-frontier-packages.md`.
Review artifact:
`review-case2-source-chart-frontier-packages-a4.md`.

Lean now packages the displayed Case 2 source-chart frontier as fielded
implications:

```text
ContinuingSourceChartFrontierPayload
ActualWidthSourceChartFrontierPayload
RowExhaustedTerminalLastSourceChartFrontierPayload
SourceChartFrontierBoundaryPackages
sourceChartMap_frontierBoundaryPackages
```

The package exposes the existing continuing, actual-width, and row-exhausted
boundary theorems under their own explicit branch hypotheses.  This is
deliberately not a single `Or`: the stopped hypotheses may overlap, and their
conclusions have different domains.  Actual-width still carries original rows
and `(S+1,0)` relabelled certificates; row-exhausted still carries transported
prefix rows and only the terminal-last suffix-removal field.

This is supplied-boundary assembly only.  It does not construct charts,
produce recurrence or exponent post-data, construct a successor chart-family
boundary, prove transition invariance, prove terminal source truth, compute
Jacobians, prove normal crossings/RLCT, or repair the printed Case 2 vector
mismatch.

## 2026-06-21 Lean Case 2 free Cprime continuing branch

Reproduction:
`reproduction-case2-free-cprime-continuing-branch-a4.md`.
Statement card:
`statement-card-a4-case2-free-cprime-continuing-branch.md`.
Review artifact:
`review-case2-free-cprime-continuing-branch-a4.md`.

Lean now proves the continuing lower-row product identity for an arbitrary
free pivot-first displayed Case 2 chart-coordinate following factor `Cprime`:

```text
case2DisplayedFreeCprimeTop
case2DisplayedFreeCprimeTail
case2DisplayedFreeCprime_eq_verticalBlock
case2DisplayedPostPivotFreeFollowingFactor
case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
Case2DisplayedSuppliedChartFamilyBoundary.postPivotFreeCprimeNextSameStageProduct
sourceChartMap_postPivotFreeCprimeNextSameStageProduct_withCorrectedPostData
```

The calculation is the block identity
`blockdiag(1,D-x*y) * [Ctop; Ctail] = [Ctop; (D-x*y)*Ctail]`
followed by the existing row/column complement reindexing to `(S,J+1)`.
The source-chart package conjoins this finite product identity with the
existing corrected exponent, level, least-value-gap, and `case2Gap`
projections.

This is finite displayed-pivot matrix algebra only.  It does not assert that
the free `Cprime` is produced by a source-coordinate chart, construct chart
coverage or arbitrary-pivot coverage, produce successor recurrence/exponent
data, prove transition invariance, compute Jacobians, prove normal
crossings/RLCT, terminal relabeling, or repair the printed Case 2 vector
mismatch.

## 2026-06-21 Lean Case 2 free Cprime local product package

Reproduction:
`reproduction-case2-free-cprime-local-product-package-a4.md`.
Statement card:
`statement-card-a4-case2-free-cprime-local-product-package.md`.
Review artifact:
`review-case2-free-cprime-local-product-package-a4.md`.

Lean now packages the displayed source-chart `Q/P` identity for a free
chart-coordinate following matrix together with the free-`Cprime` continuing
lower-row product and corrected post-data:

```text
sourceChartMap_constructedSourceFreeCprimeLocalProduct_withCorrectedPostData
```

The first conjunct reconstructs the old source residual following factor from
`Q*Cprime`, zero-extends it to a total source-coordinate function, and applies
the weighted source-displayed `Q/P` theorem.  Its right side is
`weightedPivotDiagonal(...) * D''' * Cprime`.  The second conjunct is the
separate bare lower-row identity for `D''' * Cprime`, reindexed to
`(S,J+1)`.  Keeping these separate avoids absorbing successor row weights into
the post-pivot residual block.

This is still finite displayed-pivot bookkeeping.  It does not prove chart
coverage, arbitrary-pivot coverage, source production of all `Cprime`,
successor chart-family construction, source-produced recurrence/exponent
post-data, transition invariance, terminal relabeling, Jacobian arithmetic,
normal crossings/RLCT, or repair the printed Case 2 vector mismatch.

## 2026-06-21 Lean Case 2 weighted free Cprime lower-row projection

Reproduction:
`reproduction-case2-weighted-free-cprime-lower-row-projection-a4.md`.
Statement card:
`statement-card-a4-case2-weighted-free-cprime-lower-row-projection.md`.
Review artifact:
`review-case2-weighted-free-cprime-lower-row-projection-a4.md`.

Lean now proves the lower-row projection of Aoyagi's weighted displayed right
side `diag(b') D''' C'`:

```text
weightedPivotDiagonal_mul_lowerRows
weightedPivotDiagonal_mul_lowerRows_reindex
case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct
Case2DisplayedSuppliedChartFamilyBoundary.postPivotWeightedFreeCprimeNextSameStageProduct
```

The generic row-scaling lemmas say lower rows of
`weightedPivotDiagonal * B` are the lower-row diagonal times lower rows of
`B`, also after reindexing.  The Case 2 theorem specializes this to
`D''' * Cprime`, then rewrites the bare lower rows using the existing
free-`Cprime` post-pivot product.  The supplied-boundary wrapper uses the
successor state's row weights and states the diagonal over the next
same-stage row domain `(S,J+1)`.

This is still finite lower-row algebra only.  It does not identify the pivot
row, prove a full successor product, construct chart coverage or arbitrary
pivot coverage, source-produce `Cprime`, derive recurrence/exponent post-data,
prove transition invariance, terminal relabeling, Jacobian arithmetic, normal
crossings/RLCT, or repair the printed Case 2 vector mismatch.

## 2026-06-21 Lean Case 2 source-side weighted lower-row handoff

Reproduction:
`reproduction-case2-source-side-weighted-lower-row-handoff-a4.md`.
Statement card:
`statement-card-a4-case2-source-side-weighted-lower-row-handoff.md`.
Review artifact:
`review-case2-source-side-weighted-lower-row-handoff-a4.md`.

Lean now projects the constructed-source weighted `Q/P` equality itself to the
lower rows and rewrites the weighted right side with the successor lower-row
diagonal:

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_constructedSourceFreeCprimeWeightedNextSameStageProduct_withCorrectedPostData
```

The proof composes the existing local product package with the weighted
free-`Cprime` lower-row projection.  The source-side expression keeps the
`weightedPivotBlockRowOp q` factor and reconstructs the old source following
factor from `Q*Cprime`; the conclusion is the successor lower-row diagonal
times the bare post-pivot residual-block/free-following-factor product, plus
the corrected exponent, level, least-value-gap, and `case2Gap` data.

This remains finite displayed-pivot algebra only.  It is not a full successor
product including the pivot row, and it does not construct charts, prove
chart coverage or arbitrary-pivot coverage, source-produce `Cprime`, derive
source-produced post-data, prove transition invariance, terminal relabeling,
Jacobian arithmetic, normal crossings/RLCT, or repair the printed Case 2
vector mismatch.

## 2026-06-21 Lean Case 2 paper-Cprime source-following weighted handoff

Reproduction:
`reproduction-case2-paper-cprime-source-following-weighted-handoff-a4.md`.
Statement card:
`statement-card-a4-case2-paper-cprime-source-following-weighted-handoff.md`.
Review artifact:
`review-case2-paper-cprime-source-following-weighted-handoff-a4.md`.

Lean now specializes the source-side weighted lower-row handoff to Aoyagi's
paper transported following factor `C' = Q^-1 C`:

```text
case2DisplayedPostPivotFreeFollowingFactor_paperCprime_eq_sourceFollowingFactor_succ
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData
```

The helper identifies only the lower tail of the paper `C'` with the next
same-stage source following factor.  The package projects the `P_q`-operated
weighted source-chart `Q/P` equality to lower rows and rewrites the right side
as the successor lower-row diagonal times
`case2DisplayedPostPivotResidualBlock * case2SourceFollowingFactor (J:=J+1)`.
It also carries the corrected exponent, level, least-value-gap, and
`case2Gap` data.

This remains finite displayed-pivot algebra only.  It is not a full successor
product including the pivot row, and it does not construct charts, prove chart
coverage or arbitrary-pivot coverage, source-produce `C'^(S+1)`, derive
source-produced post-data, prove transition invariance, terminal relabeling,
Jacobian arithmetic, normal crossings/RLCT, or repair the printed Case 2
vector mismatch.

## 2026-06-21 Lean Case 2 continuing weighted source-following payload

Reproduction:
`reproduction-case2-continuing-weighted-source-following-payload-a4.md`.
Statement card:
`statement-card-a4-case2-continuing-weighted-source-following-payload.md`.
Review artifact:
`review-case2-continuing-weighted-source-following-payload-a4.md`.

Lean now exposes the paper-`C'` weighted lower-row handoff through the
source-chart frontier package:

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal
ContinuingWeightedSourceFollowingFrontierPayload
SourceChartFrontierBoundaryPackages.continuingWeighted
```

Under `J+2 <= prefixMinNat n (S+1)`, the payload combines next residual-center
nonemptiness, the existing lower-row weighted source-following equality, the
corrected post-data fields, and the finite displayed source-chart center facts
`u in center`, center divisibility by `u`, and center ideal `Ideal.span {u}`.

This is a payload wrapper only.  It keeps the equality lower-row only and keeps
the successor lower-row diagonal explicit.  It does not prove a full successor
product including the pivot row, chart production, chart coverage,
source-produced `C'^(S+1)`, source-produced post-data, transition invariance,
terminal relabeling, Jacobian arithmetic, normal crossings/RLCT, or repair the
printed Case 2 vector mismatch.

## 2026-06-21 Lean Case 2 terminal-prefix transported product

Reproduction:
`reproduction-case2-terminal-prefix-transported-product-a4.md`.
Statement card:
`statement-card-a4-case2-terminal-prefix-transported-product.md`.
Review artifact:
`review-case2-terminal-prefix-transported-product-a4.md`.

Lean now rewrites the stopped terminal-prefix product candidate directly using
the explicit transported terminal rows:

```text
case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_transportedRowsPrefix_mul
```

It combines the existing terminal-prefix product rewrite with the existing
identity between the terminal-prefix `C'` candidate and
`case2DisplayedSourceTerminalTransportedRows` restricted to the prefix rows.
The final row remains the transported top row of `Q^-1 C`; it is not replaced
by an original source row unless the actual-width column-exhaustion hypothesis
is supplied separately.

This is finite terminal-prefix algebra only.  It does not construct charts,
source-produce `C'^(S+1)`, produce recurrence/exponent post-data, prove chart
coverage or transition invariance, compute a Jacobian, prove normal crossings,
pole order, or RLCT extraction.

## 2026-06-21 Lean Case 2 row-exhausted source-suffix payload

Reproduction:
`reproduction-case2-row-exhausted-source-suffix-payload-a4.md`.
Statement card:
`statement-card-a4-case2-row-exhausted-source-suffix-payload.md`.
Review artifact:
`review-case2-row-exhausted-source-suffix-payload-a4.md`.

Lean now packages the row-exhausted source-chart boundary with the actual
source suffix and finite center principalization:

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_rowExhausted_sourceSuffixTransportedPrefixBoundary_withFiniteCenterIdeal
Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedSourceSuffixTransportedPrefixPayload
SourceChartFrontierBoundaryPackages.rowExhaustedSourceSuffix
```

This removes the previous terminal-last restriction from the row-exhausted
frontier payload by keeping `sourceSuffixProduct` explicitly.  The terminal
side remains transported prefix rows; it does not replace the transported top
row by an original source row, does not set the suffix to `1`, and does not add
`(S+1,0)` relabelled level/exponent certificates.

This is still supplied-boundary assembly and finite center principalization.
It does not construct charts, source-produce `C'^(S+1)`, produce
recurrence/exponent post-data, prove chart coverage or transition invariance,
compute a Jacobian, prove normal crossings, pole order, or RLCT extraction.

## 2026-06-21 Lean Case 2 post-pivot source residual

Reproduction:
`reproduction-case2-post-pivot-source-residual-a4.md`.
Statement card:
`statement-card-a4-case2-post-pivot-source-residual.md`.
Review artifact:
`review-case2-post-pivot-source-residual-a4.md`.

Lean now names a zero-extended source-coordinate representative of the
displayed Case 2 post-pivot lower-right block.  Restricting this source
representative back to the next same-stage residual row/column domains
recovers `case2DisplayedPostPivotResidualBlock`, and the existing paper-`C'`
lower-row product is rewritten in source-residual/source-following notation.

This is finite representative bookkeeping only.  It does not construct the
successor chart, produce recurrence or exponent post-data from coordinates,
prove a transition invariant, handle terminal relabeling, prove normal
crossings, or extract an RLCT.

## 2026-06-22 Lean Case 1(2) J-increment payload

Reproduction:
`reproduction-case1-j-increment-payload-a4.md`.
Statement card:
`statement-card-a4-case1-j-increment-payload.md`.
Review artifact:
`review-case1-j-increment-payload-a4.md`.

Lean now packages the finite payload behind Aoyagi PDF p. 18's statement that
the displayed Case 1(2) continuation branch has the inductive statement with
`J` increased by one:

```text
Case1DisplayedRowStripJIncrementPayload
Case1DisplayedRowStripSuppliedTransitionBoundary.jIncrementPayload
Case1DisplayedRowStripSelectedOldPullbackBoundary.jIncrementPayload
Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.jIncrementPayload
```

The payload records the non-strict next-state bound
`J+1 <= prefixMinNat n (S+1)`, actual-width validity for `(S,J+1)`, insertion
and cardinality of the new introduced-label finite domain, and post exponent
certificates over `(S,J+1)`.

The companion recurrence projection is also exposed through the same boundary
layers:

```text
post.weight i = u * factoredBase.weight i,    for J+1 <= i.
```

The comparison is with the factored-old base state, not with the substituted
source state containing the selected old factor at level `J+J1`.

This is supplied-boundary finite bookkeeping only.  It does not construct the
displayed chart or post-state, prove a nonempty residual block after the
increment, chart coverage, transition invariance, Jacobian arithmetic, Lemma 5
classifier/no-extra/back-to-label data, pole order, normal crossings, or RLCT.

## 2026-06-22 Lean Case 2 displayed J-increment payload

Reproduction:
`reproduction-case2-j-increment-payload-a4.md`.
Statement card:
`statement-card-a4-case2-j-increment-payload.md`.
Review artifact:
`review-case2-j-increment-payload-a4.md`.

Lean now packages the finite payload behind Aoyagi PDF p. 21's displayed Case
2 statement that, under the continuation guard, the inductive statement has
`J` increased by one:

```text
Case2DisplayedJIncrementPayload
Case2DisplayedSuppliedChartFamilyBoundary.jIncrementPayload
```

The payload records the non-strict next-state bound
`J+1 <= prefixMinNat n (S+1)`, the corrected Case 2 new-label certificate for
`(S,J+1)`, actual-width validity, introduced-label insertion and cardinality,
the corrected new-label numerator identities, and post exponent certificates
over `(S,J+1)`.

The companion recurrence projection is

```text
Case2DisplayedSuppliedChartFamilyBoundary.post_weight_eq_new_mul_pre_weight_of_ge
```

which states `post.weight i = u * pre.weight i` for `J+1 <= i`.

This slice uses the corrected Case 2 exponent package already isolated in
Lean; it does not assert that Aoyagi's printed Case 2 vector has the corrected
prefix-minimum terminal exponent.  It does not construct the chart or
post-state, prove a nonempty residual block after the increment, successor
chart-family construction, a full next `C'^(S+1)`, transition invariance,
Jacobian arithmetic, normal crossings, pole order, or RLCT.

## 2026-06-22 Source-frontier audit: Case 2 paper Cprime

Audit artifact:
`source-frontier-audit-case2-paper-cprime-a4.md`.

xhigh auditor `Gauss` checked whether the next A4 move should reproduce the
local paper transported factor `C'=Q^-1*C` as a total source-coordinate
object.  Verdict: a broad new reproduction of that local algebra is not
needed.  Existing artifacts already define `case2DisplayedPaperCprime`, prove
its top-row correction and unchanged lower tail, specialize the weighted
lower-row handoff to paper `C'`, and package `SuppliedTerminalCprimeBridge`.

The missing A4 frontier is chart/source production of the full successor
object or successor following-product data from the displayed chart across
the continuing and terminal branches.  Future work should produce, rather
than supply, the old top rows, transported pivot row, post-pivot tail, and
suffix handling for the next `C'^(S+1)` or successor following-product
package.  A thin total-source adapter for paper `C'` is acceptable only if it
directly serves that source-production theorem.

## 2026-06-22 Lean Case 2 continuing weighted following product

Reproduction:
`reproduction-case2-continuing-weighted-following-product-a4.md`.
Statement card:
`statement-card-a4-case2-continuing-weighted-following-product.md`.
Review artifact:
`review-case2-continuing-weighted-following-product-a4.md`.

Lean now right-multiplies the continuing paper-`C'` weighted lower-row handoff
by an arbitrary supplied following product:

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData
```

This is exactly congruence of the existing lower-row identity under
right-multiplication by `F`.  The matrix `F` is supplied.  The theorem keeps
the pivot row absent, keeps the successor lower-row diagonal explicit, and
carries the corrected exponent/level/gap/recurrence post-data projections from
the existing boundary.  It does not assert next-center nonemptiness, source
production of `F`, source production of the full successor `C'^(S+1)`,
successor chart-family construction, transition invariance, Jacobian
arithmetic, normal crossings, pole order, or RLCT.

## 2026-06-22 Lean Case 2 source successor following factor

Reproduction:
`reproduction-case2-source-successor-following-factor-a4.md`.
Statement card:
`statement-card-a4-case2-source-successor-following-factor.md`.
Review artifact:
`review-case2-source-successor-following-factor-a4.md`.

Lean now names the source-order following factor obtained after the displayed
Case 2 pivot by replacing only source row `J+1` with the transported top row
of `Q^-1 C`:

```text
case2DisplayedSourceSuccessorFollowingFactor
case2DisplayedSourceSuccessorFollowingFactor_pivotRow
case2DisplayedSourceSuccessorFollowingFactor_of_ne
case2DisplayedSourceSuccessorFollowingFactor_oldRow
case2SourceFollowingFactor_successorFollowingFactor_succ
case2DisplayedSourceSuccessorFollowingFactor_eq_original_of_width_next_eq
case2DisplayedSourceTerminalOriginalRows_successorFollowingFactor
case2DisplayedSourceTerminalCprimeCandidate_eq_originalRows_successorFollowingFactor
```

This is formula-level source-coordinate data.  It proves that the post-pivot
same-stage following restriction is unchanged, that actual next-width
exhaustion collapses the successor factor back to the original `C`, and that
the transported terminal rows are the original terminal rows of this
successor factor.  It is not chart production, source-produced recurrence or
exponent post-data, old-top/suffix production, chart coverage, successor
chart-family construction, transition invariance, Jacobian arithmetic, normal
crossings, pole order, or RLCT.

## 2026-06-22 Lean Case 2 successor following weighted handoff

Reproduction:
`reproduction-case2-successor-following-weighted-handoff-a4.md`.
Statement card:
`statement-card-a4-case2-successor-following-weighted-handoff.md`.
Review artifact:
`review-case2-successor-following-weighted-handoff-a4.md`.

Lean now rewrites the displayed paper-`C'` weighted lower-row handoff through
the formula-level successor following factor:

```text
sourceChartMap_paperCprimeWeightedLowerRows_withSuccFollowingFactorAndCorrectedData
sourceChartMap_paperCprimeWeightedLowerRows_mul_F_withSuccFollowingFactorAndCorrectedData
```

The only mathematical input beyond the older handoff theorem is
`case2SourceFollowingFactor_successorFollowingFactor_succ`: after moving from
`J` to `J+1`, the following-factor restriction starts at row `J+2`, so it
does not see the replaced row `J+1`.  The supplied-`F` theorem keeps `F`
arbitrary and supplied.

This is still lower-row formula algebra.  It does not add next-center
nonemptiness, source production of `F`, old-top rows, suffix production, full
successor `C'^(S+1)`, chart production, chart coverage, transition
invariance, Jacobian arithmetic, normal crossings, pole order, termination,
RLCT, or repair of the printed Case 2 vector mismatch.

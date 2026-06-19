# A4 repair report - blow-up transition certificate

Status: blocked/source gap.  This replaces the first draft's width bookkeeping
with source-faithful notation and records the Case 2 mismatch confirmed by two
xhigh rechecks.  It is not a full reproduction certificate.

Source used: Aoyagi 2023 PDF pp. 14-23, inspected both as text and page images.

Independent rechecks:

- Source-fidelity scout `Russell the 2nd`: verdict printed-vector
  mismatch/source gap, not a misread.
- Pen-and-paper scout `Hume the 2nd`: verdict the prefix-minimum repaired
  vector is the one compatible with the terminal exponent formula.
- Pen-and-paper scout `McClintock the 2nd`: verdict the `P` regularity
  obligation reduces to one elementary tail-product lemma for monomial
  recurrences, with the source's `b'_i`/standalone-`u` display requiring a
  normalization choice.

## Notation lock

The source uses two different width notions.

- Actual reduced layer widths:

  ```text
  n_s := M^(s),          s = 1, ..., L+1.
  ```

- Prefix minima:

  ```text
  mu_S := M(S) := min { M^(q) | 1 <= q <= S },    S = 1, ..., L+1.
  ```

These must not be collapsed.  At a state `(S,J)`, the diagonal has length
`mu_S`, but the active residual block has actual column width `n_(S+1)`:

```text
D_J = (d_ij),       J+1 <= i <= mu_S,     J+1 <= j <= n_(S+1),
size(D_J) = (mu_S - J) x (n_(S+1) - J).
```

The advance test is different:

```text
J + 1 <= mu_(S+1) = min(mu_S, n_(S+1)).
```

If this fails, then the current residual block has one remaining row or one
remaining column, and the process advances to `(S+1,0)`.

The source labels are also actual-width indexed:

```text
(s,k),      1 <= s <= L,     1 <= k <= n_(s+1).
```

At stage `(S,J)`, the already introduced exceptional variables are

```text
u_(s,k),  1 <= s <= S-1, 1 <= k <= n_(s+1),
u_(S,k),  1 <= k <= J.
```

Using `mu_(s+1)` for these ranges undercounts labels whenever
`n_(s+1) > mu_(s+1)`.

Lean status: the actual-width label convention is formalised in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` as `prefixMinNat`,
`actualWidthLabel`, `prefixWidthLabel`,
`actualWidthLabel_of_prefixWidthLabel`,
`actualWidthLabel_not_prefixWidthLabel_of_prefixMinNat_lt_width`,
`actualWidthLabel_case2_new`, `prefixWidthLabel_case2_new`,
`correctedCase2PivotVector`, and
`terminalExponent_correctedCase2PivotVector`.

The introduced-variable convention is formalised by `introducedLabel`,
`introducedLabel_mono_J`, `not_introducedLabel_case2_new_before`, and
`introducedLabel_case2_new_after`.

## Corrected invariant shape

For `1 <= S <= L` and the displayed step range where `J` lies inside the
current residual block, the source invariant should be read as

```text
< prod_{s=1}^L C^(s) >
  =
< diag(b_1, ..., b_(mu_S))
    * blockdiag(E_J, D_J)
    * prod_{s=S+1}^L C^(s) >.
```

Here `D_J` has rows through `mu_S` and columns through actual `n_(S+1)`.
Continuation states after a pivot use the source test
`J <= mu_(S+1) = min(mu_S,n_(S+1))`.
The source says the initial case is obvious for `S = 0, J = 0`, but the
matrix display is directly inhabited by the normalized state

```text
S = 1, J = 0, D_0 = C^(1), b_i = 1.
```

This reindexing should be kept unless a source-faithful convention for `M(0)`
is recovered.

The monomial recurrence is

```text
b_0 = 1,
b_i = (prod_{tilde_t_(s,k) = i-1} u_(s,k)) * b_(i-1),
     i = 1, ..., mu_S.
```

This recurrence is the intended source of divisibility facts for the row
operation matrix `P`.

## Case 1 source repair

Case 1 assumes a first jump after the current processed block:

```text
b_(J+1) = ... = b_(J+J1),
b_(J+J1+1) != b_(J+J1),
{ tilde_t_(s,k) = i } is empty for i = J+1, ..., J+J1-1.
```

Choose `u_(s,k)` with `tilde_t_(s,k) = J+J1` and minimal vector among that
level in the componentwise order.

The blow-up center is

```text
d_ij = 0,  i = J+1, ..., J+J1,  j = J+1, ..., n_(S+1),
u_(s,k) = 0.
```

Lean status: the finite generator symbols for this Case 1 center are packaged
as `Case1CenterGenerator` and `case1CenterGenerators`.  The `Unit` branch
represents the chosen old exceptional generator after that label has been
chosen externally; it does not encode actual-width validity, level `J+J1`,
minimality, or comparability.  The row-strip entries use actual active column
width `n_(S+1)`, and the displayed pivot-entry membership theorem assumes only
the finite entry bounds, not full row-strip source validity.

Lean also proves the finite row-strip containment needed for source validity:
`case1StripRows_subset_case2ResidualBlockRows` and
`case1StripEntries_subset_case2ResidualBlockPivotEntries` require the explicit
row bound `J+J1 <= mu_S`. This is weaker than the full Case 1 first-jump
hypothesis and is only an entry-set containment statement.

Lean now also packages the finite first-jump and selected-label assumptions as
`Case1FirstJumpHypotheses`. This records `1 <= J1`, the strict nonterminal
boundary `J+J1 < mu_S`, the selected introduced label `(s,k)`, the selected
level `tilde_t_(s,k)=J+J1`, the empty intermediate level gap, and
componentwise minimality on `1..L`. The strict boundary is a finite proxy for
the existence of `b_(J+J1+1)` inside the current recurrence range; it is not a
proof of the monomial inequality `b_(J+J1+1) != b_(J+J1)`. The source level is
Nat-valued in Lean, with only the selected-level cast to the integer convention
proved; identifying it with certificate `leastValue` remains an invariant
obligation.

### Case 1(1): selected `u_(s,k)` chart

The whole `J1 x (n_(S+1)-J)` row strip is divided by `u_(s,k)`.

The corrected updates are

```text
t_(s,k)^(S) = t_(s,k)^(S+1) = ... = t_(s,k)^L = J,
tilde_t_(s,k) = J,
b'_(J+1), ..., b'_(J+J1) are multiplied by u_(s,k),
M'_(s,k) = M_(s,k) + J1 * (n_(S+1) - J).
```

The increment uses the actual active column count `n_(S+1)-J`, not
`mu_(S+1)-J`.

Lean status: the pure terminal-exponent arithmetic for this update is proved
as `lowerTailVector`,
`terminalExponent_lowerTailVector_of_flatFromPred`, and
`terminalExponent_lowerTailVector_of_flatFromPred_add`. The theorem assumes the
old vector is flat from `S-1` through `L` at the level being lowered; proving
that a Case 1 selected label has this property remains a separate invariant
obligation. The component/least-value facts for the lowered vector and the
one-label certificate transformer
`LabelExponentCertificate.lowerTailVector_of_flatFromPred_add` are also proved,
but the transformer assumes the old least value is `J+J1` and that
`J <= J+J1`; it is not a chart transition or all-label invariant update.

Lean now also proves the conditional same-domain package update
`IntroducedLabelExponentCertificates.case1_selectedLowerTail_sameDomain`. This
reassembles an all-introduced-label certificate package at the same state
`(S,J)` when the selected label is replaced by its lower-tail certificate and
all non-selected introduced labels are assumed unchanged. It assumes the
bridges `leastValue = level` and `FlatTailFromPred` for the selected label and
assumes the post-chart selected vector, numerator, and least value. It does not
construct the chart, prove row-strip division, prove `b'_i` recurrence
bookkeeping, or advance the domain.

The convenience theorem `case1_selectedLowerTail_updateData` instantiates this
same-domain update using total assignment overrides
`updateSelectedLabelVector` and `updateSelectedLabelScalar`. These helpers are
syntactic post-data functions only; values outside the introduced-label domain
are formal and irrelevant.

Lean also packages the conditional level/tail bridge
`IntroducedLabelLevelTailInvariants`: `leastValue=level` is assumed for every
introduced label, while `FlatTailFromPred` is assumed only for labels above the
current pivot, `J < level`. The selected Case 1 label is above the pivot by
`Case1FirstJumpHypotheses.lt_selectedLevel`, so
`case1_selectedLowerTail_of_levelTailInvariants` feeds the same-domain
lower-tail update. This is an assumed bridge, not a proof that the recursion
establishes or preserves the bridge, and it deliberately does not claim
flat-tail for all introduced labels.

This branch keeps `(S,J)` and decreases the number of labels at
`tilde_t = J+J1`.

### Case 1(2): displayed pivot chart

The source displays the chart with pivot `d_(J+1,J+1)`:

```text
strip = u_(S,J+1) * strip',
strip'_(J+1,J+1) = 1,
u_(s,k) = u_(S,J+1) * u'_(s,k).
```

The new label `(S,J+1)` inherits old earlier coordinates from the chosen
minimal vector and is set to `J` from `S` onward:

```text
t_(S,J+1)^i = t_(s,k)^i,       i = 1, ..., S-1,
t_(S,J+1)^S = ... = t_(S,J+1)^L = J,
tilde_t_(S,J+1) = J.
```

The monomials and Jacobian numerator update as

```text
b'_(J+1), ..., b'_(mu_S) are multiplied by u_(S,J+1),
M'_(S,J+1) = M_(s,k) + J1 * (n_(S+1) - J).
```

The residual variable `u'_(s,k)` from `u_(s,k)=u_(S,J+1)u'_(s,k)` is not
spelled out in the source's vector bookkeeping.  It should retain the old
label data for `(s,k)` if the `b_i` recurrence is to remain true.  This is a
repair obligation, not a source-displayed formula.

After the displayed `Q` and `P` transformations, the active block becomes
`blockdiag(1,D_(J+1))`.  If `J+1 <= mu_(S+1)`, the state continues as
`(S,J+1)`.  If `J+1 > mu_(S+1)`, the one-row or one-column remainder is
absorbed into a new matrix `C'^(S+1)` of size `mu_(S+1) x n_(S+2)`, and the
state advances to `(S+1,0)`.

## Case 2 source repair

Case 2 assumes there is no later jump inside the current diagonal length:

```text
b_(J+1) = ... = b_(mu_S),
{ tilde_t_(s,k) = i } is empty for i = J+1, ..., mu_S - 1.
```

The blow-up center is the full remaining residual block

```text
d_ij = 0,  i = J+1, ..., mu_S,  j = J+1, ..., n_(S+1).
```

The source again displays only the pivot chart with pivot `d_(J+1,J+1)`:

```text
D_J = u_(S,J+1) * D'_J,    D'_J(J+1,J+1) = 1.
```

The PDF prints the new vector with actual earlier widths:

```text
t_(S,J+1)^i = n_(i+1),     i = 1, ..., S-1,
t_(S,J+1)^S = ... = t_(S,J+1)^L = J,
tilde_t_(S,J+1) = J.
```

The numerator update is

```text
M'_(S,J+1) = (mu_S - J) * (n_(S+1) - J).
```

The first factor is the remaining row count; the second is the actual remaining
column count.  This is not `(mu_S-J)(mu_(S+1)-J)`.

There is a serious compatibility issue with the source's later terminal
exponent formula.  If the printed vector

```text
t_(S,J+1)^i = n_(i+1) for i < S,    t_(S,J+1)^q = J for q >= S
```

is substituted into

```text
M_(s,k) =
  (n_1 - t^1)(n_2 - t^1)
  + sum_{j=2}^L (t^(j-1)-t^j)(n_(j+1)-t^j),
```

the terms before `S` telescope to zero and the jump at `S` contributes

```text
(n_S - J) * (n_(S+1) - J),
```

not the source's Case 2 update `(mu_S-J)*(n_(S+1)-J)` unless `mu_S=n_S`.
Page-image inspection confirms that this is what the PDF prints: the Case 2
vector on PDF p. 20 uses actual widths `M^(i+1)`, the transition condition on
PDF p. 21 still defines `M(S+1)=min{M(S),M^(S+1)}`, and the terminal exponent
formula on PDF p. 22 uses actual widths `M^(j)`.

Replacing earlier entries by prefix minima repairs the calculation:

```text
t_(S,J+1)^i = mu_(i+1) = M(i+1),    i = 1, ..., S-1,
t_(S,J+1)^q = J,                    q = S, ..., L.
```

For this corrected vector, the source line `tilde_t_(S,J+1)=J` follows from
the state bound `J <= mu_S`: prefix minima are antitone in the prefix index, so
all earlier entries `mu_(i+1)` for `i<S` are at least `mu_S`, hence at least
`J`, while every entry from `S` onward is exactly `J`.

Lean status: the finite minimum certificate is formalised as
`prefixMinNat_antitone`, `correctedCase2PivotVector_eq_prefix_of_lt`,
`correctedCase2PivotVector_eq_J_of_le`,
`le_correctedCase2PivotVector_of_le_prefixMinNat`, and
`correctedCase2PivotVector_min_certificate`. The finite source-range version
is `correctedCase2PivotVector_isLeast_valueSet_Icc`. The one-label packaging
for the corrected Case 2 new label is
`CorrectedCase2NewLabelCertificate`, with constructors
`correctedCase2NewLabelCertificate_of_actualBound_of_stateBound` and
`correctedCase2NewLabelCertificate_of_prefixBound`; it deliberately packages
only `(S,J+1)` and not a state invariant over all labels.

Substitution gives

```text
(n_1-mu_2)(n_2-mu_2)
  + sum_{j=2}^{S-1} (mu_j-mu_(j+1))(n_(j+1)-mu_(j+1))
  + (mu_S-J)(n_(S+1)-J).
```

Every pre-`S` term vanishes because
`mu_(j+1)=min(mu_j,n_(j+1))`, so one factor is zero.  The surviving term is
the printed update:

```text
(mu_S-J)(n_(S+1)-J).
```

This is a mathematical repair, not a verbatim reproduction of the printed
Case 2 vector.  A formal development should therefore split:

- `Printed`: source-faithful data, including the mismatch lemma
  `E(T_printed)=(n_S-J)(n_(S+1)-J)`.
- `CorrectedCertificate`: prefix-minimum `T` data with actual-width label
  ranges, proving the terminal exponent recurrence.

Do not mix these two invariants.  In particular, repairing only the Case 2
new vector inside the otherwise printed recursion can break pairwise
comparability with older source-style vectors.  The corrected certificate must
use prefix-minimum vector data coherently while keeping the source label
universe `(s,k)` with `1 <= k <= n_(s+1)`.

The same `Q/P` algebra gives `blockdiag(1,D_(J+1))`.  The same continuation
criterion applies: either continue with `(S,J+1)` when
`J+1 <= mu_(S+1)`, or advance to `(S+1,0)` and absorb the one-dimensional
remainder into `C'^(S+1)`.

Lean status: the corrected Case 2 new-label certificate is now usable as a
generic `LabelExponentCertificate`, and
`IntroducedLabelExponentCertificates` gives a Prop-valued container for
terminal-exponent/minimum certificates over the introduced-label domain.  Its
extension lemmas are only domain bookkeeping: old label assignments must be
supplied as unchanged, and no chart transition is proved.  The Case 2
residual-block center is also recorded as the finite product set
`case2ResidualBlockPivotEntries`, with rows `J+1..mu_S` and columns
`J+1..n_(S+1)`; the displayed source pivot belongs under the continuation
bound.  This is not a chart-cover theorem.

## Divisibility obligation for `P`

Both pivot branches define a lower-unitriangular matrix `P` with entries

```text
-(b'_i / b'_(J+1)) * d''_(i,J+1),     i = J+2, ..., mu_S.
```

For this to be a regular coordinate operation, the quotient must be a regular
monomial.  A formal proof should derive:

```text
b'_(J+1) divides b'_i,     for i = J+2, ..., mu_S.
```

The intended reason is the recurrence

```text
b'_i = (prod_{tilde_t' = i-1} u') * b'_(i-1).
```

In Case 1, the gap
`{tilde_t = i} = empty` for `i = J+1, ..., J+J1-1` makes the quotient trivial
up to `J+J1`; after that it is a product of later recurrence factors.  In
Case 2, the gap extends to `mu_S-1`, so every quotient is trivial after the
common multiplication by the pivot variable.  This needs a precise monomial
divisibility lemma before Lean work treats `P` as regular.

There is also a source-display ambiguity in the pivot branches: the PDF defines
`b'_i = u * b_i` and then writes a standalone factor `u` before `diag(b')` in
the displayed algebra.  A formal certificate should define the post-chart
`b'_i` by the monomial recurrence and then prove the displayed ideal equality,
rather than taking both the printed `b'_i` line and the printed standalone
factor literally.

### Elementary recurrence lemma

The part that can already be made precise is purely monomial arithmetic.  Let
`m_i` be the product of all variables with `tilde_t=i`; write the recurrence as

```text
b_0 = 1,
b_(r+1) = m_r * b_r.
```

For any `a <= b`, induction on `b-a` gives

```text
b_b = (m_(b-1) * ... * m_a) * b_a,
```

with the factors taken over the levels `a, ..., b-1`.  Hence `b_a` divides
`b_b`, and the quotient is a monomial.  In the notation needed by `P`, this
says

```text
b_(J+1) divides b_i,       for every i >= J+1.
```

If a pivot chart multiplies the whole displayed tail by a new exceptional
variable `u`, then

```text
b'_(J+1) = u * b_(J+1),
b'_i     = u * b_i
```

still satisfies `b'_(J+1) | b'_i`, because common multiplication preserves
divisibility in a commutative monoid:

```text
b_i = b_(J+1) * q
=> u*b_i = (u*b_(J+1)) * q.
```

For Case 1(2), the source's gap
`{tilde_t=i}=empty` for `i=J+1,...,J+J1-1` says the first tail factors after
`J` are `1`; the quotient is trivial up to the strip level and then continues
as the product of later recurrence factors.  For Case 2, the gap extends to
`mu_S-1`, so the quotient is `1` for all displayed `i <= mu_S` after the
common pivot multiplication.  The general recurrence-divisibility lemma is
slightly more general than this equality/gap use and is the safe Lean target:
it proves regularity of the quotient as a monomial without relying on the
disputed Case 2 vector.

Independent check: xhigh pen-and-paper scout `McClintock the 2nd` confirmed
the same tail-product quotient.  In Case 1(2), the equality
`b_(J+1)=...=b_(J+J1)` only makes the early quotient factors `1`; the
inequality `b_(J+J1+1) != b_(J+J1)` is not needed for divisibility.  In
Case 2, all factors in the relevant quotient range are `1`, so the `P`
first-column entries reduce to `-d''_(i,J+1)` under a consistent
normalization.

Lean status: this arithmetic is formalised in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` as
`monomialRec`, `monomialTail`, `monomialRec_add_eq_tail_mul`,
`monomialRec_dvd_of_le`, `monomialRec_pivot_dvd`,
`mul_left_dvd_mul_left_of_dvd`, and `pivotMul_monomialRec_dvd_of_le`.

### Normalized `P` row-operation algebra

After choosing a consistent normalization for the common pivot factor, the
displayed `P` identity is elementary block algebra.  Reindex the displayed
pivot block so the pivot row and column are indexed by `0`, and the remaining
rows and columns are indexed separately.  Write the `Q`-normalised block as

```text
D'' = [ 1  0
       x  D ],
```

where the top row zeros are the output of the `Q` operation.  Let the diagonal
weights be

```text
B = diag(b'_0, b'_lower),
```

and suppose quotient witnesses `q_i` satisfy

```text
b'_i = q_i * b'_0
```

for every lower row `i`.  Define

```text
P = [ 1   0
     -q_i*x_i   I ].
```

Then, for the first column and lower row `i`,

```text
(P B D'')_(i,0)
  = -(q_i*x_i)*(b'_0*1) + b'_i*x_i
  = 0.
```

For a lower-right entry `(i,j)`, the top-row zero gives

```text
(P B D'')_(i,j)
  = -(q_i*x_i)*(b'_0*0) + b'_i*D_ij
  = b'_i*D_ij.
```

The top row is unchanged.  Thus

```text
P * B * D'' = B * [ 1  0
                   0  D ].
```

This proof is independent of the Case 2 printed-vector mismatch: it uses only the
already-normalised local matrix `D''`, quotient witnesses, and the decision to
count the common pivot factor once.  It applies verbatim to Case 1(2) and
Case 2; only the source of the quotient witnesses differs.

Independent check: xhigh scout `Gauss the 2nd` reproduced the same normalized
row-operation certificate from PDF pp. 17-21 and confirmed that the printed
outside `u` versus `b'_i=u*b_i` display must be resolved by a single
normalization choice.

Lean status: the normalized block theorem is formalised as
`weightedPivotBlockRowOp_mul_diagonal_mul` in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`, with helper definitions
`weightedPivotBlockRowOp`, `weightedPivotBlockMatrix`,
`weightedPivotClearedBlock`, and `weightedPivotDiagonal`.

### Normalized `Q` column-operation algebra

The source displays the same `Q` operation in Case 1(2) and Case 2.  After
normalising the pivot entry to `1` and reindexing the pivot row/column first,
write the pre-`Q` block as

```text
D' = [ 1  y
      x  D ],
```

where `y` is the rest of the pivot row and `x` is the lower part of the pivot
column.  Define

```text
Q    = [ 1  -y ],
       [ 0   I ]

Q^-1 = [ 1   y ].
       [ 0   I ]
```

Then block multiplication gives

```text
D' Q = [ 1  0
         x  D - x*y ].
```

Thus `Q` clears the pivot row away from the pivot.  Replacing the following
factor `C` by `Q^-1 C` preserves the product:

```text
(D' Q)(Q^-1 C) = D'(Q Q^-1)C = D'C.
```

This is independent of the Case 2 printed-vector mismatch, because it uses only the local
block entries of `D'` and the following factor `C`.  It applies verbatim to
Case 1(2) and Case 2.

Independent check: xhigh source-fidelity scout `Franklin the 2nd` reproduced
this `Q` algebra from PDF pp. 17-21 and confirmed the following-factor
replacement `C'_J^(S+1)=Q^-1 C_J^(S+1)`.

Lean status: this algebra is formalised in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` as `pivotPreQBlock`,
`pivotQ`, `pivotQinv`, `pivotPostQBlock`, `pivotPreQBlock_mul_pivotQ`,
`pivotQ_mul_pivotQinv`, `pivotQinv_mul_pivotQ`, and
`pivotPreQBlock_mul_eq_postQ_mul_Qinv_mul`.

### Combined normalized pivot-step algebra

The two displayed operations compose without adding any new analytic input.
The post-`Q` block

```text
[ 1 0
  x D - x*y ]
```

has the exact shape required by the normalized `P` theorem after reading the
one-column matrix `x` as the function `i ↦ x_i`. Hence the local identity is:

```text
P * diag(b0,b) * (D' Q)
  = diag(b0,b) * [ 1 0
                   0 D - x*y ],
```

where `P` is built from quotient witnesses `b_i=q_i*b0`. With the following
factor included, the product-preserving form is:

```text
(P * diag(b0,b) * D') * C
  = (diag(b0,b) * [ 1 0
                    0 D - x*y ]) * (Q^-1 C).
```

This remains a finite matrix identity. It does not prove that the pivot chart
exists, that these substitutions are regular polynomial coordinate changes with
unit Jacobian, or that the exponent bookkeeping is correct.

Lean status: this algebra is formalised as
`pivotPostQBlock_eq_weightedPivotBlockMatrix`,
`weightedPivotBlockRowOp_mul_diagonal_mul_pivotPostQBlock`,
`weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul_pivotQ`, and
`weightedPivotBlockRowOp_mul_diagonal_mul_pivotPreQBlock_mul`.

## Pivot-chart coverage obligation

The source displays only the chart where the pivot entry is `d_(J+1,J+1)`.
The full blow-up of the displayed center has additional charts for every
generator in the center:

- the selected exceptional-variable chart in Case 1(1);
- pivot charts for every entry in the blown-up `D` strip/block.

For formalisation, choose one of two routes:

1. Prove a permutation/symmetry lemma reducing every nonzero pivot entry to the
   displayed `(J+1,J+1)` chart, with the same ideal and exponent update after
   relabelling rows/columns.
2. Formalize a family of pivot charts indexed by the chosen pivot and prove the
   `Q/P` elimination for that general pivot.

The first route is likely shorter, but only if row/column permutations preserve
the monomial `b_i` order or the proof explicitly permutes the active rows and
then restores them.

Lean status: the generic selected-entry substitution algebra is now packaged
as `selectedEntryChartMap`, with pivot/non-pivot value lemmas, divisibility by
the selected variable, and a finite value-set witness.  The Case 2 displayed
pivot specialization is
`case2_displayedPivot_selectedEntryChartMap_value_mem`.  This is not a chart
cover theorem and does not prove the non-displayed selected entries satisfy the
displayed `Q/P` transition formulas.

Lean also records arbitrary selected-entry finite-center facts for the Case 1
and Case 2 centers. If a chosen pivot belongs to the finite center, `u` occurs
in the finite substitution value set, witnessed by that pivot, and every
transformed finite-center generator is divisible by `u`. This is chart-index
bookkeeping only; it is not an affine blow-up atlas, non-displayed transition
theorem, or row/column permutation argument.

## Termination repair target

The previous lexicographic measure is unstable because Case 1(1) can exhaust
the current jump level and reveal a later jump.  A more faithful finite
measure should track the multiset of unprocessed `tilde_t` levels above `J`
inside the current state.

One candidate from the repair scout:

```text
P(S,J) =
  (mu_(S+1) - J) + sum_{q=S+1}^L mu_(q+1),

Phi(S,J) =
  sum over active labels a of max(tilde_t_a - J, 0),

Measure = (P(S,J), Phi(S,J)).
```

ordered lexicographically.  This is not yet checked.  It must prove:

- Case 1(1) strictly decreases the count at the first nonempty level.
- Case 1(2) and Case 2 either increase `J` while preserving `S`, or advance
  `S` when the current interface is exhausted; in either branch `P(S,J)`
  decreases by one performed pivot.
- The source's off-by-one convention for the advance test is coherent:
  after a pivot the text says continue if `J+1 <= mu_(S+1)` and advance if
  `J+1 > mu_(S+1)`.  Dimensionally, exhaustion occurs when the just-created
  pivot reaches the smaller side, so this needs a repaired convention before
  the measure can be made formal.

## Current blockers

- Full pivot-chart coverage is still not reproduced.
- The recurrence divisibility and normalized displayed `Q/P` matrix identities,
  including their combined local pivot-step identity and the existential
  pivot-first wrappers that choose quotient witnesses, are proved narrowly. The
  source-displayed Case 2 top-left pivot `Q/P` product identity is also proved
  under flat displayed row weights, and the following factor's pivot-first
  reindexing is proved. The full polynomial-coordinate pivot chart
  construction, full source-variable coordinate/weight transport, arbitrary
  selected-entry pivots, and chart-family coverage are not proved.
- The printed Case 2 vector update is incompatible with the terminal exponent
  formula for arbitrary widths.  The prefix-minimum vector repairs the
  arithmetic but is a corrected certificate, not source-faithful printed data.
- The source's `b'_i`/standalone-`u` display in the pivot algebra needs a
  recurrence-based repair.
- The termination measure above is only a repair target.
- Boundary cases remain to check: `J=0`, `J+1=mu_(S+1)`, rectangular
  `mu_S < n_(S+1)` and `mu_S > n_(S+1)`, `S=L`, and the advance to
  `S=L+1`.

Lean formalisation should not start before these blockers are either proved or
split into named assumptions with a narrow certificate target.

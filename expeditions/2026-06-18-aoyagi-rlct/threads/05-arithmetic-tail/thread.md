# Thread 05 - arithmetic tail

Type: formalisation. Status: blocked.

## Task

Formalise Aoyagi's finite minimisation and pole-order arithmetic once the
exponent vectors are stable.

## Output contract

- Lean definitions for the relevant finite candidate set and exponent ratios.
- Proofs of the minimisation and order-count lemmas.
- Boundary-case tests/examples for small dimension vectors.

## Controller notes

This should be mostly finite arithmetic. If a proof becomes a long brittle
calculation, consider a small exact certificate generator, but Lean remains the
final authority.

## 2026-06-18 check result

Draft reproduction: `reproduction-draft.md`. Independent checker: `Planck`,
saved at `reproduction-check.md`.

Status: not formalisation-ready. The next arithmetic reproduction must split
Lemma 3 endpoint cases, preserve Aoyagi's `\tilde t_{s,k}=0` restriction, prove
feasibility of the floor/ceil minimisers, and reproduce Lemma 5's
chart-family/order-count construction.

## 2026-06-20 Lean Lemma 3 endpoint arithmetic

Reproduction:
`reproduction-lemma3-endpoint-arithmetic-a5.md`.
Statement card:
`statement-card-a5-lemma3-endpoint-arithmetic.md`.
Review artifact:
`review-lemma3-endpoint-arithmetic-a5.md`.

Lean now proves the isolated integer numerator algebra for Aoyagi's Lemma 3 in
`lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean`.  The main identity is

```text
A(b) = a ell (ell-a) + ell^2 (b-a)(b-a+1),
```

and the endpoint-corrected minimum theorem says that, under
`1 <= ell` and `0 <= a <= ell`, the least value over integer
`0 <= b <= ell-1` is `a ell (ell-a)`.  This repairs the endpoint issue for
`a=0` and `a=ell`.

The full A5 claim remains blocked.  This sub-slice does not prove the
terminal candidate set, the `\tilde t_{s,k}=0` restriction, feasibility of
minimising exponent chains, Lemma 4, Lemma 5, pole order, normal crossings, or
RLCT extraction.

## 2026-06-20 Lean Lemma 3 equality cases

Reproduction:
`reproduction-lemma3-equality-cases-a5.md`.
Statement card:
`statement-card-a5-lemma3-equality-cases.md`.
Review artifact:
`review-lemma3-equality-cases-a5.md`.

Lean now also proves the exact equality cases for the same isolated integer
numerator.  If `ell != 0`, then

```text
A(b) = a ell (ell-a) iff b = a or b = a-1.
```

After intersecting with the source interval `0 <= b <= ell-1`, equality is
equivalent to

```text
(b = a and a <= ell-1) or (b = a-1 and 1 <= a).
```

Endpoint corollaries name the remaining candidates at `a=0` and `a=ell`.
This is still only integer polynomial arithmetic and source-interval
bookkeeping.  The full A5 claim remains blocked by the terminal candidate set,
the `\tilde t_{s,k}=0` restriction, exponent-chain feasibility, Lemmas 4-5,
pole order, normal crossings, and RLCT extraction.

## 2026-06-20 Lean Lemma 3 equality count

Reproduction:
`reproduction-lemma3-equality-count-a5.md`.
Statement card:
`statement-card-a5-lemma3-equality-count.md`.
Review artifact:
`review-lemma3-equality-count-a5.md`.

Lean now defines the finite equality set
`aoyagiLemma3AMinimizerSet ell a` as the integer source interval
`0 <= b <= ell-1` filtered by equality with the isolated lower bound.  It proves
the set is `{0}` at `a=0`, `{ell-1}` at `a=ell`, and `{a-1,a}` in the strict
interior `0<a<ell`.  The combined cardinality theorem is

```text
card = 1 + if 0 < a and a < ell then 1 else 0
```

under `1 <= ell` and `0 <= a <= ell`.

This is not Lemma 5's pole-order count.  It counts only integer `b` values for
the isolated Lemma 3 numerator equality, not terminal variables, exponent-chain
feasibility, chart-family coordinates, or RLCT data.

## 2026-06-20 Lean Lemma 5 interval-excess arithmetic

Reproduction:
`reproduction-lemma5-interval-excess-a5.md`.
Statement card:
`statement-card-a5-lemma5-interval-excess.md`.
Review artifact:
`review-lemma5-interval-excess-a5.md`.

Lean now proves the elementary interval-size sum used in Aoyagi's Lemma 5 in
`lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`.  The closed excess
formula is

```text
min(j, ell-j, a, ell-a),
```

encoded as nested `min`s.  It is identified with fibers of the rectangle
`range a x range (ell-a)` under the level map `(p,q) |-> p+q+1`, and summing
these fibers proves

```text
1 + sum_{j=1}^{ell-1} (intervalSize(ell,a,j)-1) = a(ell-a)+1
```

under `1 <= ell` and `a <= ell`.

This is still not Lemma 5.  It proves only finite interval-excess arithmetic,
not the chart-family constructions, admissibility, coverage, pole-order
interpretation, normal crossings, or RLCT extraction.

## 2026-06-20 Lean Lemma 4 two-value count

Reproduction:
`reproduction-lemma4-two-value-count-a5.md`.
Statement card:
`statement-card-a5-lemma4-two-value-count.md`.
Review artifact:
`review-lemma4-two-value-count-a5.md`.

Lean now proves the finite count used in Aoyagi's Lemma 4 in
`lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`.  If an `ell`-indexed
integer family takes only values `M-1` and `M`, and its sum is

```text
ell*(M-1)+a,
```

then exactly `a` entries are `M` and exactly `ell-a` entries are `M-1`.
The theorem also records that these hypotheses force `a <= ell`.

This is only finite count arithmetic.  The source bridge from `H_ell=0` to the
sum identity, the `H_0` convention for `F_1`, vector inequalities,
correspondence to `lambda`, Lemma 5, pole order, normal crossings, and RLCT
extraction remain open.

## 2026-06-20 Lean Lemma 4 source sum bridge

Reproduction:
`reproduction-lemma4-sum-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma4-sum-bridge.md`.
Review artifact:
`review-lemma4-sum-bridge-a5.md`.

Lean now proves the finite telescoping bridge that was left open in the
previous Lemma 4 count slice.  With selected widths
`m : Fin (ell+1) -> Z`, extended `H : Fin (ell+1) -> Z`, the convention
`H 0 = m 0` for Aoyagi's hidden `H_0 := M(S_1)`, and terminal condition
`H (Fin.last ell) = 0`, the theorem
`aoyagiLemma4F_sum_eq_selectedSum` proves

```text
sum_j F_j = sum_j m_j,
```

where `F_j = H_(j-1) - H_j + M(S_(j+1))` in zero-indexed Lean form.  The
wrapper `aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a` combines this with
Definition 3's selected-width sum `sum m = ell*(M-1)+a`.  The source-shaped
count wrapper `aoyagiLemma4_twoValueCount_of_terminalH` then proves the
two-value count without assuming `sum F_j = ell*(M-1)+a` directly.

This is still not Aoyagi Lemma 4.  It assumes the selected-width sum, terminal
`H` convention, and the two-value increment hypothesis.  It does not prove
the vector inequalities `Ttilde <= T <= Ttilde'`, the two-value hypothesis from
those inequalities, the endpoint-corrected Lemma 3 minimisation bridge,
correspondence to `lambda`, Lemma 5, pole order, normal crossings, or RLCT
extraction.

## 2026-06-20 Lean Lemma 4 free-count bridge

Reproduction:
`reproduction-lemma4-free-count-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma4-free-count-bridge.md`.
Review artifact:
`review-lemma4-free-count-bridge-a5.md`.

Lean now proves the finite bridge from Lemma 4's all-increment count to the
free count used in Lemma 3.  For a family indexed by `Fin (n+1)`, the theorem
`highCount_castSucc_add_last_eq_total` splits the total high count into the
first `n` positions plus the last-position indicator.  Consequently, if the
total high count is `a`, then

```text
b = #{j : Fin n | v(j.castSucc)=M}
```

satisfies, over integers,

```text
b = a or b = a-1.
```

The theorem `aoyagiLemma4_freeHighCount_lemma3A_eq_min_of_totalCount` feeds
this alternative into the already-proved Lemma 3 equality-case theorem, proving
the isolated numerator equality

```text
A(b) = a*ell*(ell-a)
```

for `ell=n+1`.  The source-shaped wrapper
`aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min` combines this with the
terminal-`H` sum bridge and two-value increment hypothesis.

This is still finite arithmetic only.  It does not prove the two-value
increment hypothesis from `Ttilde <= T <= Ttilde'`, vector admissibility,
terminal exponent rewriting into the Lemma 3 quadratic, correspondence to
`lambda`, Lemma 5, pole order, normal crossings, or RLCT extraction.

## 2026-06-20 Lean Lemma 4 endpoint squeeze

Reproduction:
`reproduction-lemma4-endpoint-squeeze-a5.md`.
Statement card:
`statement-card-a5-lemma4-endpoint-squeeze.md`.
Review artifact:
`review-lemma4-endpoint-squeeze-a5.md`.

Lean now proves the terminal endpoint arithmetic used in Aoyagi's Lemma 4
proof.  The common endpoint expression for the displayed `Htilde_ell` and
`Htilde'_ell` is

```text
sum_j M(S_j) - (a*M + (ell-a)*(M-1)).
```

Under `a <= ell` and Definition 3's selected-width sum, this endpoint is zero.
The theorem `aoyagiLemma4_Hlast_eq_zero_of_terminalEndpoint_bounds` then says
that a terminal `H_ell` squeezed between the two endpoint values is zero.
Wrappers `aoyagiLemma4_twoValueCount_of_terminalEndpointBounds` and
`aoyagiLemma4_terminalEndpointBounds_freeHighCount_lemma3A_eq_min` replace the
previous explicit `H_ell=0` hypothesis by supplied endpoint inequalities.

This is still finite arithmetic only.  It does not prove the full `Htilde` or
`Htilde'` chains, the vector inequality `Ttilde <= T <= Ttilde'`, that vector
inequality implies the endpoint sandwich, the two-value increment hypothesis,
vector admissibility, terminal exponent rewriting into the Lemma 3 quadratic,
correspondence to `lambda`, Lemma 5, pole order, normal crossings, or RLCT
extraction.

## 2026-06-20 Lean Lemma 4 same-coordinate bridge

Reproduction:
`reproduction-lemma4-same-coordinate-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma4-same-coordinate-bridge.md`.
Review artifact:
`review-lemma4-same-coordinate-bridge-a5.md`.

Source check: Aoyagi's Definition 4 defines componentwise order on vectors but
does not define a unique endpoint-selection map from a vector `T` to the
sequence `(H_j),(S_j)`.  Therefore the source sentence
`Ttilde <= T <= Ttilde'` and `Htilde_ell=Htilde'_ell=0` imply `H_ell=0` is not
formalised from Definition 4 alone.

Lean now proves the conservative same-coordinate replacement.  If the lower
vector, middle vector, and upper vector all read their terminal endpoint from
the same coordinate `p`, and `Tlo <= T <= Thi` componentwise, then
`H_ell` is squeezed between the lower and upper terminal endpoint values.
Combined with the endpoint-zero calculation, this gives `H_ell=0`, and the
wrappers `aoyagiLemma4_twoValueCount_of_sameCoordinate` and
`aoyagiLemma4_sameCoordinate_freeHighCount_lemma3A_eq_min` feed the result into
the finite Lemma 4 count and Lemma 3 bridge.

This is still finite order arithmetic only.  It does not prove the source
`T -> (H_j),(S_j)` correspondence, that Aoyagi's displayed
`Ttilde <= T <= Ttilde'` supplies the same-coordinate hypotheses, the full
`Htilde` or `Htilde'` chains, the two-value increment hypothesis, vector
admissibility, terminal exponent rewriting into the Lemma 3 quadratic,
correspondence to `lambda`, Lemma 5, pole order, normal crossings, or RLCT
extraction.

## 2026-06-20 Lean Htilde chain arithmetic

Reproduction:
`reproduction-htilde-chain-arithmetic-a5.md`.
Statement card:
`statement-card-a5-htilde-chain-arithmetic.md`.
Review artifact:
`review-htilde-chain-arithmetic-a5.md`.

Lean now formalises the finite arithmetic of Aoyagi's displayed extremal
`Htilde` and `Htilde'` chains in
`lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`.  The lower chain
subtracts

```text
j*(M-1) + min(j,a)
```

from the selected-width prefix, so its increments are `M` first and then
`M-1`.  The upper chain subtracts the low-first high-count prefix, so its
increments are `M-1` first and then `M`.  Both chains start at the source
convention `H_0=M(S_1)`, and both terminal values equal the previously named
common endpoint `aoyagiLemma4TerminalEndpoint`.  The pointwise gap
`Htilde'_j-Htilde_j` is the Lemma 5 interval-excess formula
`aoyagiLemma5IntervalExcess`.

This removes the narrow "full displayed chain arithmetic" gap left by the
endpoint-squeeze slice, but it is still finite arithmetic only.  It does not
prove the source `T -> (H_j),(S_j)` correspondence, that Aoyagi's displayed
`Ttilde <= T <= Ttilde'` supplies the same-coordinate hypotheses, the
two-value increment hypothesis for arbitrary intermediate vectors, vector
admissibility, terminal exponent rewriting into the Lemma 3 quadratic,
correspondence to `lambda`, Lemma 5 chart-family admissibility/coverage/order
count, pole order, normal crossings, or RLCT extraction.

## 2026-06-20 Lean Htilde interval bounds

Reproduction:
`reproduction-htilde-interval-bounds-a5.md`.
Statement card:
`statement-card-a5-htilde-interval-bounds.md`.
Review artifact:
`review-htilde-interval-bounds-a5.md`.

Lean now proves the same-coordinate interval consequences of the displayed
`Htilde` chains.  Since

```text
Htilde'_j - Htilde_j = aoyagiLemma5IntervalExcess ell a j,
```

the lower chain is pointwise below the upper chain, and the finite value set

```text
{Htilde_j + r | 0 <= r <= aoyagiLemma5IntervalExcess ell a j}
```

has cardinality `aoyagiLemma5IntervalSize ell a j`.  Membership in this set is
equivalent to the same-coordinate bounds `Htilde_j <= H_j <= Htilde'_j`.

Under the selected-width sum, both displayed chains have terminal value zero.
Thus an intermediate `H`-chain squeezed between them in the same coordinates
has `H_ell=0`; the existing Lemma 4 count and Lemma 3 free-count bridge can
then be applied under the still-explicit two-value increment hypothesis.

This remains conditional finite arithmetic.  It does not prove the source
`T -> (H_j),(S_j)` correspondence, that Aoyagi's displayed
`Ttilde <= T <= Ttilde'` supplies the same chain coordinates, the two-value
increment hypothesis for arbitrary vectors, vector admissibility,
correspondence to `lambda`, Lemma 5 chart-family admissibility/coverage/order
count, pole order, normal crossings, or RLCT extraction.

## 2026-06-20 Lean Lemma 4 binary prefix delta

Reproduction:
`reproduction-lemma4-binary-prefix-delta-a5.md`.
Statement card:
`statement-card-a5-lemma4-binary-prefix-delta.md`.
Review artifact:
`review-lemma4-binary-prefix-delta-a5.md`.

Lean now proves a conditional bridge for Lemma 4's two-value increment
hypothesis.  For an arbitrary chain, define

```text
D_j = P(j) - H_j - j*(M-1).
```

Then

```text
F_j = (M-1) + (D_(j+1)-D_j).
```

Thus a supplied binary-delta hypothesis `D_(j+1)-D_j in {0,1}` gives
`F_j in {M-1,M}`.  The bridge feeds the existing terminal-`H` and
same-coordinate `Htilde`-chain-bound count wrappers.

This is still conditional finite arithmetic.  It does not prove that source
exponent vectors imply binary prefix deltas, that chain bounds imply binary
prefix deltas, vector-coordinate correspondence, vector admissibility,
correspondence to `lambda`, Lemma 5 chart-family admissibility/coverage/order
count, pole order, normal crossings, or RLCT extraction.

## 2026-06-20 Lean Lemma 4 prefix-delta endpoint count

Reproduction:
`reproduction-lemma4-prefix-delta-endpoint-count-a5.md`.
Statement card:
`statement-card-a5-lemma4-prefix-delta-endpoint-count.md`.
Review artifact:
`review-lemma4-prefix-delta-endpoint-count-a5.md`.

Lean now names the endpoint bookkeeping for the prefix-delta interface.
With

```text
D_j = P(j)-H_j-j*(M-1),
Delta_j = D_(j+1)-D_j,
```

the source convention `H_0=m_0` gives `D_0=0`, while terminal `H_ell=0`
and the selected-width sum give `D_ell=a`.  The delta sum telescopes to
`D_ell-D_0`, hence `sum_j Delta_j=a`.  If the deltas are binary, then exactly
`a` deltas are `1` and exactly `ell-a` are `0`.

This is still conditional finite arithmetic.  It does not prove that source
exponent vectors imply binary prefix deltas, that chain bounds imply binary
prefix deltas, vector-coordinate correspondence, vector admissibility,
correspondence to `lambda`, Lemma 5 chart-family admissibility/coverage/order
count, pole order, normal crossings, or RLCT extraction.

## 2026-06-20 Lean Htilde value-set count

Reproduction:
`reproduction-htilde-value-set-count-a5.md`.
Statement card:
`statement-card-a5-htilde-value-set-count.md`.
Review artifact:
`review-htilde-value-set-count-a5.md`.

Lean now proves the finite source-facing count for same-coordinate value sets
between the displayed `Htilde` and `Htilde'` chains:

```text
aoyagiHtildeIntervalValueSetNat
aoyagiHtildeIntervalValueSetNat_card_of_lt
aoyagiHtildeIntervalValueSetNat_card
aoyagiHtildeIntervalValueSetNat_excess_sum_Icc
```

The Nat-indexed wrapper is explicitly empty outside the source coordinate
range, and the source interval sum proves

```text
1 + sum_{j=1}^{ell-1} (|I_j|-1) = a(ell-a)+1.
```

This is still only finite value-set arithmetic.  It does not prove Aoyagi
Lemma 5's chart-family admissibility, coverage, displayed vector
constructions, pole-order interpretation, normal crossings, or RLCT
extraction.

## 2026-06-20 Lean Lemma 4 same-coordinate binary-delta free count

Reproduction:
`reproduction-lemma4-same-coordinate-binary-delta-free-count-a5.md`.
Statement card:
`statement-card-a5-lemma4-same-coordinate-binary-delta-free-count.md`.
Review artifact:
`review-lemma4-same-coordinate-binary-delta-free-count-a5.md`.

Lean now packages two existing conditional interfaces into the finite
Lemma 4-to-Lemma 3 free-count bridge:

```text
aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta
aoyagiLemma4_sameCoordinateChain_binaryIncrementPrefixDelta_freeHighCount_lemma3A_eq_min
```

The first theorem is the named-delta form of the binary prefix-delta bridge:
if `Delta_j = D_(j+1)-D_j` is `0` or `1`, then
`F_j = (M-1)+Delta_j` is `M-1` or `M`.

The second theorem takes a supplied coordinate map from vector entries to the
`H`-chain, componentwise bounds `Tlo <= T <= Thi`, and coordinate identities
with the displayed `Htilde` chains.  These hypotheses give the same-coordinate
chain bounds, while the binary deltas give the two-value increment hypothesis;
the existing free-count bridge then proves that the first `ell-1` high count
attains the isolated Lemma 3 numerator minimum.

This remains conditional finite arithmetic.  It does not prove Aoyagi's
source `T -> (H_j),(S_j)` correspondence, binary prefix deltas from source
vectors, vector admissibility, terminal exponent rewriting, correspondence to
`lambda`, Lemma 5 chart-family admissibility/coverage/order count, pole order,
normal crossings, or RLCT extraction.  The source-facing next target is the
displayed-family realisation in Aoyagi Lemma 5, especially equations `(3)` and
`(4)` on pp. 26-27.

## 2026-06-20 Lean Lemma 5 equation (4) own-coordinate sanity

Reproduction:
`reproduction-lemma5-eq4-own-coordinate-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-own-coordinate.md`.
Blocked audit:
`blocked-audit-lemma5-displayed-family-realisation-a5.md`.
Review artifact:
`review-lemma5-eq4-own-coordinate-a5.md`.

Lean now proves the finite chain arithmetic needed for Aoyagi Lemma 5 equation
`(4)` at its own source label:

```text
aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min
aoyagiHtildeUpperNat_sub_index_eq_lowerNat_of_le_min
```

If `p <= a` and `p <= ell-a`, then the interval excess at `p` is exactly `p`.
Since the gap between the displayed upper and lower `Htilde` chains is that
interval excess, the printed own-coordinate value satisfies

```text
Htilde'_p - p = Htilde_p.
```

This is only an own-coordinate arithmetic sanity check.  It records that the
source's printed guard `j0 <= a` is not enough by itself; the additional guard
`j0 <= ell-a` is needed for equation `(4)` to match `t^(s)=k-1` at
`s=S_(j0+1)-1`.

The companion blocker audit records that the full displayed-family
realisation is not yet formalisation-ready: legal source-label bounds,
terminal/tail conventions for `tilde t=0`, the missing equation `(4)` index
guards, and the Case 1(2) chart sequence remain open.

## 2026-06-20 Lean Lemma 5 equation (4) guard arithmetic

Reproduction:
`reproduction-lemma5-eq4-guard-arithmetic-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-guard-arithmetic.md`.
Blocked audit:
`blocked-audit-lemma5-displayed-family-realisation-a5.md`.
Review artifact:
`review-lemma5-eq4-guard-arithmetic-a5.md`.

Lean now records three guard facts for equation `(4)`:

```text
aoyagiLemma5IntervalExcess_eq_self_of_le_min
aoyagiLemma5Eq4_selectedIndexGuard_iff
aoyagiHtildeLowerNat_add_one_labelBounds_iff_prefixCrossing
```

The selected-index cutoff `S_(p+ell-a+2)` lies in the Definition 3 selected
list exactly when `p+1<=a`, so the printed `p<=a` guard is one unit too weak
at the boundary `p=a`.

The label bounds for `k=Htilde_p+1` are exactly a prefix-crossing condition:
the threshold `pM` must lie after the previous selected-width prefix and no
later than the current prefix.  This isolates the real missing
nonnegativity/admissibility datum for `Htilde_p`.

This remains only finite guard arithmetic.  It does not construct the
displayed equation `(4)` vector, prove source-label legality from Definition
3 alone, prove `tilde t=0`, or prove Lemma 5.

## 2026-06-20 Lean Lemma 5 equation (3) guard arithmetic

Reproduction:
`reproduction-lemma5-eq3-guard-arithmetic-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-guard-arithmetic.md`.
Blocked audit:
`blocked-audit-lemma5-displayed-family-realisation-a5.md`.
Review artifact:
`review-lemma5-eq3-guard-arithmetic-a5.md`.

Lean now records three guard facts for equation `(3)`:

```text
aoyagiLemma5Eq3_selectedIndexGuard_iff
aoyagiHtildeUpperNat_one_sub_lowerNat_one_of_pos_of_lt
aoyagiHtildeUpperNat_one_add_one_labelBounds_iff_widthGuards
```

The special cutoff `S_(ell-a+2)` lies in Definition 3's selected list exactly
when `1<=a`.  In the interior case `1<=a` and `a<ell`, the first Htilde gap
`Htilde'_1-Htilde_1` is `1`.  The label bounds for `k=Htilde'_1+1` are exactly
the two width guards `M-1<=W_1+W_2` and `W_1+2<=M`.

This remains only finite guard arithmetic.  It does not construct the
displayed equation `(3)` vector, prove source-label legality from Definition
3 alone, prove `tilde t=0`, or prove Lemma 5.

## 2026-06-20 Lean Definition 3 selected-width upper label bound

Reproduction:
`reproduction-definition3-selected-width-upper-label-a5.md`.
Statement card:
`statement-card-a5-definition3-selected-width-upper-label.md`.
Review artifact:
`review-definition3-selected-width-upper-label-a5.md`.

Lean now proves that Definition 3's strict selected-width inequality forces
each selected width to satisfy `W_i<=M-1`:

```text
aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
```

From this, Lean proves the previous-prefix inequality `P_p+1<=pM` for
`1<=p`, and therefore the upper equation `(4)` label bound
`Htilde_p+1<=W_(p+1)` under `p<=a`:

```text
aoyagiPrefixSum_sub_current_add_one_le_mul_of_selectedWidth_le_pred
aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_selectedWidth_le_pred
aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_sourceSelectedInequality
```

This discharges only the upper half of equation `(4)` label legality from
Definition 3.  A later checkpoint below discharges the lower half by applying
the same selected-width bound to the tail after `P_(p+1)`.

## 2026-06-20 Lean Definition 3 selected-width full label bounds

Reproduction:
`reproduction-definition3-selected-width-label-bounds-a5.md`.
Statement card:
`statement-card-a5-definition3-selected-width-label-bounds.md`.

Lean now proves the lower equation `(4)` label bound from Definition 3 as
well:

```text
aoyagiPrefixSum_mul_le_of_selectedWidth_le_pred
aoyagiPrefixSum_mul_le_of_sourceSelectedInequality
aoyagiHtildeLowerNat_add_one_pos_of_selectedWidth_le_pred
aoyagiHtildeLowerNat_add_one_pos_of_sourceSelectedInequality
aoyagiHtildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
```

The missing arithmetic move was to use `W_i<=M-1` on the tail after
`P_(p+1)`.  Since the tail has `ell-p` terms,

```text
P_(p+1) >= ell*(M-1)+a - (ell-p)(M-1) = p*(M-1)+a >= pM,
```

using `p<=a`.  Together with the previous-prefix estimate, this proves
`1<=Htilde_p+1<=W_(p+1)` under `1<=p`, `p<=a`, and Definition 3's
selected-width hypotheses.

This is still only equation `(4)` label arithmetic.  Equation `(4)` still
needs the selected-index guard `p+1<=a`, the own-coordinate guard
`p<=ell-a`, terminal `tilde t=0`, and full displayed-family realisation.
Equation `(3)`'s one-unit slack guard and full Lemma 5 order count remain
open.

## 2026-06-20 Lean Lemma 5 equation `(4)` local data

Reproduction:
`reproduction-lemma5-eq4-local-data-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-local-data.md`.
Review artifact:
`review-lemma5-eq4-local-data-a5.md`.

Lean now packages the corrected local arithmetic data for equation `(4)`:

```text
aoyagiLemma5Eq4_localData_of_sourceSelectedInequality
```

Under Definition 3's selected-width hypotheses and guards
`1<=p`, `p+1<=a`, and `p<=ell-a`, it proves:

```text
p + (ell-a) + 2 <= ell+1,
Htilde'_p - p = Htilde_p,
1 <= Htilde_p+1 <= W_(p+1).
```

This combines the selected-index repair, own-coordinate repair, and full
label legality into one handoff theorem.  It is deliberately still not a
displayed-vector theorem: terminal `tilde t=0`, vector admissibility,
source vector-to-chain correspondence, chart-family coverage, and the Lemma 5
order count remain open.

## 2026-06-20 Lean Lemma 5 equation `(4)` piecewise certificate

Reproduction:
`reproduction-lemma5-eq4-piecewise-certificate-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-piecewise-certificate.md`.
Review artifact:
`review-lemma5-eq4-piecewise-certificate-a5.md`.

Lean now has a conditional source-vector-facing file
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.

The new objects are:

```text
AoyagiSelectedCutpoints
AoyagiSelectedCutpoints.point
AoyagiSelectedCutpoints.block
AoyagiSelectedCutpoints.leftEndpoint_mem_block
AoyagiLemma5Eq4PiecewiseSourceVector
aoyagiLemma5Eq4_boundaryIndex_le_ell_of_piecewiseSourceVector
aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
```

This introduces supplied selected cutpoints and a supplied equation `(4)`
piecewise branch certificate.  If a function `T` satisfies that certificate,
then under the repaired guards and Definition 3 selected-width hypotheses,
Lean proves the own-coordinate value

```text
T(S_(p+1)-1) = Htilde_p
```

and the legal label bounds for `k=Htilde_p+1`.

The supplied certificate carries the source-boundary guards `a<=ell` and
`p+1<=a`.  Lean records their finite consequence
`p+(ell-a)+1<=ell`, so the special boundary is an in-range selected cutpoint,
not only a value of the totalized `point` accessor.

This remains conditional.  It does not construct the displayed vector, prove
total source-layer coverage, terminal `tilde t=0`, vector admissibility,
source vector-to-chain correspondence, the Case 1(2) chart sequence, or Lemma
5 order count.

The selected-block bookkeeping support for this certificate has also landed.
Reproduction:
`reproduction-selected-block-bookkeeping-a5.md`.
Review artifact:
`review-selected-block-bookkeeping-a5.md`.
Lean proves selected cutpoint monotonicity, selected-block uniqueness, and
uniqueness of a selected block's left endpoint:

```text
AoyagiSelectedCutpoints.cut_strictMono
AoyagiSelectedCutpoints.point_strict_of_lt
AoyagiSelectedCutpoints.point_le_of_le
AoyagiSelectedCutpoints.block_index_unique
AoyagiSelectedCutpoints.block_leftEndpoint_iff
```

These lemmas support branch disambiguation for equations `(3)` and `(4)`.
They do not claim total source-layer coverage or put the terminal selected
cutpoint into a block.

The selected-span coverage support has also landed.  Reproduction:
`reproduction-selected-block-coverage-a5.md`.  Review artifact:
`review-selected-block-coverage-a5.md`.  Lean proves:

```text
AoyagiSelectedCutpoints.block_mem_selectedSpan
AoyagiSelectedCutpoints.exists_block_of_mem_selectedSpan
AoyagiSelectedCutpoints.exists_block_iff_mem_selectedSpan
```

These theorems say that the selected blocks cover exactly the half-open span

```text
S_1-1 <= S < S_(ell+1)-1.
```

They deliberately do not cover source layers before `S_1-1`, at
`S_(ell+1)-1`, or after it.

The selected-span branch-value classifier for equation `(4)` has now landed.
Reproduction:
`reproduction-lemma5-eq4-selected-span-branch-value-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-selected-span-branch-value.md`.
Review artifact:
`review-lemma5-eq4-selected-span-branch-value-a5.md`.
Lean proves:

```text
AoyagiSelectedCutpoints.block_leftEndpoint_lt_of_ne
AoyagiSelectedCutpoints.leftEndpoint_lt_of_lt_block
AoyagiLemma5Eq4SelectedSpanBranchValue
aoyagiLemma5Eq4_branchValue_of_block
aoyagiLemma5Eq4_selectedSpan_branchValue
```

This says only that a supplied equation `(4)` branch certificate gives one of
the advertised branch values for each source index in the selected span
`S_1-1 <= S < S_(ell+1)-1`.  It keeps the boundary singleton
`S_(p+ell-a+2)-1` separate from the tail branch, and it does not claim that
the terminal endpoint `S_(ell+1)-1` lies in a selected block.  It still does
not construct the displayed vector, prove total source coverage, terminal
`tilde t=0`, vector admissibility, source vector-to-chain correspondence, the
Case 1(2) chart sequence, or Lemma 5 order count.

The terminal endpoint boundary audit has now landed.  Reproduction:
`reproduction-lemma5-eq4-terminal-endpoint-boundary-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-terminal-endpoint-boundary.md`.
Review artifact:
`review-lemma5-eq4-terminal-endpoint-boundary-a5.md`.
Lean proves:

```text
aoyagiHtildeLowerNat_last_eq_zero_of_selectedSum
aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum
AoyagiSelectedCutpoints.not_block_terminalEndpoint
aoyagiLemma5Eq4_prefix_leftEndpoint
aoyagiLemma5Eq4_middle_leftEndpoint
aoyagiLemma5Eq4_tail_leftEndpoint_of_cutoff_lt
aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension
```

The source audit still blocks a terminal displayed-vector theorem: Aoyagi's
compressed Case 1(2) sentence does not specify the chart sequence, repeated
gap checks, terminal endpoint convention, or proof of `tilde t=0`.  The new
endpoint theorem is therefore conditional: if a future record supplies
`T(S_(ell+1)-1)=Htilde'_ell`, then the selected-sum identity gives
`T(S_(ell+1)-1)=0`.  It is not vector construction or Lemma 5 order-count
coverage.

The equation `(4)` actual-width label bridge has now landed.  Reproduction:
`reproduction-lemma5-eq4-actual-width-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-actual-width-label.md`.
Review artifact:
`review-lemma5-eq4-actual-width-label-a5.md`.
Lean proves:

```text
aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility
```

This theorem converts the already-proved selected-width label bounds
`1<=Htilde_p+1<=W_(p+1)` into `actualWidthLabel` only after explicitly
supplying source-layer range, width compatibility
`n(S_(p+1))=W_(p+1)`, and Nat/Int label compatibility.  It does not construct
the displayed vector, prove introduced-label status, terminal exponent data,
or `tilde t=0`.

## 2026-06-20 Lean Lemma 5 equation `(3)` local data and label bridge

Reproduction:
`reproduction-lemma5-eq3-local-data-and-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-local-data-and-label.md`.
Review artifact:
`review-lemma5-eq3-local-data-and-piecewise-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq3_localData_of_widthGuards
aoyagiHtildeUpperNat_one_add_one_labelBounds_of_sourceSelectedInequality_and_slack
aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack
aoyagiLemma5Eq3_actualWidthLabel_of_widthCompatibility
aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack
```

This packages the safe equation `(3)` local arithmetic.  Under `1<=a`,
`a<ell`, and explicit width guards, Lean proves the selected-index cutoff,
the first Htilde gap `Htilde'_1-Htilde_1=1`, and the selected label bounds for
`k=Htilde'_1+1`.  In the source-shaped version, Definition 3 supplies
`M-1<=W_1+W_2`, but the one-unit slack `W_1+2<=M` remains an explicit
hypothesis.

The actual-width bridge converts this selected label into `actualWidthLabel`
only under source-layer range, selected-width/actual-width compatibility, and
Nat/Int label compatibility.  The xhigh source audit found a genuine
Definition 3 counterexample to label legality without the slack, so this is
not a missing Lean lemma.  This still does not construct the displayed
equation `(3)` vector, prove introduced-label status, terminal `tilde t=0`,
chart-family coverage, or Lemma 5 order count.

## 2026-06-20 Lean Lemma 5 equation `(3)` piecewise certificate

Reproduction:
`reproduction-lemma5-eq3-piecewise-certificate-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-piecewise-certificate.md`.
Review artifact:
`review-lemma5-eq3-local-data-and-piecewise-a5.md`.

Lean now proves:

```text
AoyagiLemma5Eq3PiecewiseSourceVector
AoyagiLemma5Eq3SelectedSpanBranchValue
aoyagiLemma5Eq3_branchValue_of_block
aoyagiLemma5Eq3_selectedSpan_branchValue
aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
```

This is the equation `(3)` analogue of the supplied equation `(4)` branch
certificate.  The classifier covers only the half-open selected span
`S_1-1 <= S < S_(ell+1)-1`, separates the special boundary
`S_(ell-a+2)-1` from the strict tail, and keeps the branch data supplied.
Under `1<=a`, `a<ell`, Definition 3 selected-width hypotheses, and the slack
`W_1+2<=M`, the supplied certificate gives
`T(S_2-1)=Htilde'_1` plus the selected label bounds for
`k=Htilde'_1+1`.

This still does not construct the displayed vector, cover the terminal
selected endpoint, prove terminal `tilde t=0`, prove introduced-label status,
or prove Lemma 5's chart-family/order-count theorem.

Landed-patch review:
`review-lemma5-eq3-local-data-and-piecewise-a5.md`.
The reviewer found that the supplied piecewise record should carry the source
guards for the boundary cutpoint.  This was addressed by adding `a<=ell` and
`1<=a` fields to `AoyagiLemma5Eq3PiecewiseSourceVector`.

## 2026-06-20 Lean Lemma 5 equation `(3)` terminal obstruction

Reproduction:
`reproduction-lemma5-eq3-terminal-obstruction-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-terminal-obstruction.md`.
Review artifact:
`review-lemma5-eq3-terminal-obstruction-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq3_terminalEndpoint_one_of_one
```

For a supplied equation `(3)` branch certificate with `a=1`, the special
boundary is the terminal selected endpoint `S_(ell+1)-1`, and Definition 3's
selected-sum identity gives `Htilde'_ell=0`.  Therefore the supplied equation
`(3)` boundary assignment gives `T(S_(ell+1)-1)=1`.

This records a concrete obstruction to a uniform terminal-zero theorem from
the printed equation `(3)` display.  It is not a construction of the displayed
vector and does not prove terminal `tilde t=0`, introduced-label status,
chart coverage, or Lemma 5 order count.

## 2026-06-20 Lean Lemma 5 equation `(4)` terminal collision

Reproduction:
`reproduction-lemma5-eq4-terminal-collision-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-terminal-collision.md`.
Review artifact:
`review-lemma5-eq4-terminal-collision-a5.md`.

Lean now proves:

```text
aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum
aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary
aoyagiLemma5Eq4_terminalEndpoint_zero_iff_lastWidth_of_predBoundary
```

If the equation `(4)` boundary reaches the terminal selected endpoint, i.e.
`p+1=a`, then the supplied branch value is

```text
M - W_(ell+1) - p + 1.
```

Thus terminal zero at that supplied boundary is equivalent to the extra
compatibility condition `W_(ell+1)=M-p+1`.  Definition 3 does not force this;
for instance `ell=3`, `a=2`, `p=1`, `M=3`, and all selected widths equal to
`2` satisfy the selected-sum and strict selected-width inequalities, but the
displayed terminal-collision value is `1`.

This is finite endpoint arithmetic only.  It does not construct equation
`(4)`'s displayed vector, prove terminal `tilde t=0`, or prove Lemma 5's
chart-family/order-count theorem.

## 2026-06-20 Lean Lemma 5 equation `(4)` boundary split

Reproduction:
`reproduction-lemma5-eq4-boundary-split-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-boundary-split.md`.
Review artifact:
`review-lemma5-eq4-boundary-split-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_boundaryIndex_lt_ell_iff
aoyagiLemma5Eq4_boundaryIndex_eq_ell_iff
aoyagiLemma5Eq4_boundaryEndpoint_mem_block_of_strictGuard
aoyagiLemma5Eq4_boundaryEndpoint_mem_selectedSpan_of_strictGuard
aoyagiLemma5Eq4_boundaryEndpoint_eq_terminal_of_predBoundary
aoyagiLemma5Eq4_boundaryEndpoint_not_block_of_predBoundary
```

Under `a<=ell`, the equation `(4)` boundary index
`p+(ell-a)+1` is strictly before the terminal selected index exactly when
`p+1<a`, and it is terminal exactly when `p+1=a`.  For a supplied equation
`(4)` certificate, the strict case puts the boundary point in selected block
`p+(ell-a)+1` and hence inside the half-open selected span.  The terminal case
identifies the boundary with `S_(ell+1)-1` and excludes it from all selected
blocks.

This is finite boundary bookkeeping only.  It does not construct equation
`(4)`'s displayed vector, prove terminal `tilde t=0`, or prove Lemma 5's
chart-family/order-count theorem.

## 2026-06-20 Lean Lemma 5 equation `(4)` terminal extension obstruction

Reproduction:
`reproduction-lemma5-eq4-terminal-extension-obstruction-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-terminal-extension-obstruction.md`.
Review artifact:
`review-lemma5-eq4-terminal-extension-obstruction-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary
aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary
```

In the terminal-collision case `p+1=a`, a supplied equation `(4)` certificate
assigns the terminal selected endpoint the value
`M-W_(ell+1)-p+1`.  If a separate terminal extension also supplies
`T(S_(ell+1)-1)=Htilde'_ell`, then Definition 3's selected-sum identity gives
`Htilde'_ell=0`, so Lean proves `W_(ell+1)=M-p+1`.  If that compatibility
fails, the supplied equation `(4)` branch certificate cannot also satisfy the
terminal extension.

This is finite compatibility arithmetic only.  It does not construct equation
`(4)`'s displayed vector, prove the terminal convention, or prove Lemma 5's
chart-family/order-count theorem.

## 2026-06-20 Lean Lemma 5 equation `(4)` terminal compatibility counterexample

Reproduction:
`reproduction-lemma5-eq4-terminal-compatibility-counterexample-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-terminal-compatibility-counterexample.md`.
Review artifact:
`review-lemma5-eq4-terminal-compatibility-counterexample-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_lastWidthCompatibility_not_forced_by_selectedWidthHypotheses_example
```

For `ell=3`, `a=2`, `p=1`, `M=3`, and all selected widths equal to `2`, the
range guards, terminal-collision guard `p+1=a`, selected-sum identity, and
strict selected-width inequalities all hold.  But the terminal-collision
compatibility `W_(ell+1)=M-p+1` fails, since `W_4=2` and `M-p+1=3`.

This is a closed finite counterexample to that compatibility being a
Definition 3 consequence.  It does not construct a supplied equation `(4)`
branch certificate or a terminal extension.

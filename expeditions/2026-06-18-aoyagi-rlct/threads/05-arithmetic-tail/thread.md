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
aoyagiLemma5Eq3_slack_not_forced_by_selectedWidthHypotheses_example
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
Nat/Int label compatibility.  Lean now records a closed Definition 3
counterexample to label legality without the slack, so this is not a missing
Lean lemma.  This still does not construct the displayed
equation `(3)` vector, prove introduced-label status, terminal `tilde t=0`,
chart-family coverage, or Lemma 5 order count.

Counterexample reproduction:
`reproduction-lemma5-eq3-slack-counterexample-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-slack-counterexample.md`.

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

## 2026-06-20 Lean Lemma 5 equation `(3)` boundary split

Reproduction:
`reproduction-lemma5-eq3-boundary-split-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-boundary-split.md`.
Review artifact:
`review-lemma5-eq3-boundary-split-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq3_boundaryIndex_le_ell_of_piecewiseSourceVector
aoyagiLemma5Eq3_boundaryIndex_lt_ell_iff
aoyagiLemma5Eq3_boundaryEndpoint_mem_block_of_two_le
aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le
aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_iff_two_le
aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one
aoyagiLemma5Eq3_boundaryEndpoint_not_block_of_one
aoyagiLemma5Eq3_no_terminalEndpointZero_of_one
```

Under the supplied guards `a<=ell` and `1<=a`, the equation `(3)` boundary
index `ell-a+1` is in range.  It is strictly before the terminal selected
index exactly when `2<=a`; in that case the special boundary lies at the left
endpoint of selected block `ell-a+1` and is inside the half-open selected
span.  In the boundary case `a=1`, the special boundary is the terminal
selected endpoint, lies in no half-open selected block, and cannot also be
assigned value zero under the selected-sum identity.

This is finite boundary bookkeeping only.  It does not construct equation
`(3)`'s displayed vector, prove terminal `tilde t=0`, introduced-label status,
Case 1(2) chart sequence, or Lemma 5's chart-family/order-count theorem.

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

## 2026-06-21 Lean Lemma 5 equation `(4)` p=1 terminal extension obstruction

Reproduction:
`reproduction-lemma5-eq4-p1-terminal-extension-obstruction-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-p1-terminal-extension-obstruction.md`.
Review artifact:
`review-lemma5-eq4-p1-terminal-extension-obstruction-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_no_terminalUpperNatExtension_of_p1_sourceSelectedInequality
```

In the `p=1` terminal-collision equation `(4)` case, a supplied terminal
upper-chain extension would force `W_(ell+1)=M`.  Definition 3's selected-width
hypotheses force `W_(ell+1)<=M-1`.  Therefore any supplied equation `(4)`
certificate satisfying those source-selected hypotheses is incompatible with
the supplied terminal upper-chain extension.

This is finite supplied-data arithmetic only.  It does not construct a
supplied equation `(4)` branch certificate, construct a terminal extension,
prove terminal `tilde t=0`, or prove Lemma 5.

## 2026-06-21 Lean Lemma 5 equation `(4)` terminal extension forces p

Reproduction:
`reproduction-lemma5-eq4-terminal-extension-forces-p-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-terminal-extension-forces-p.md`.
Review artifact:
`review-lemma5-eq4-terminal-extension-forces-p-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_terminalExtension_forces_two_le_p_of_sourceSelected
aoyagiLemma5Eq4_no_terminalExtension_of_sourceSelected_of_p_lt_two
```

In the terminal-collision equation `(4)` case, a supplied terminal upper-chain
extension would force `W_(ell+1)=M-p+1`.  Definition 3's selected-width
hypotheses force `W_(ell+1)<=M-1`.  Therefore such an extension forces
`2<=p`; under the same supplied-certificate and source-selected hypotheses,
`p<2` rules it out.

The theorem is stated for the totalized supplied-certificate API.  The `p=0`
edge is a Lean-totalized supplied-certificate consequence, not an additional
printed source case.  This is finite supplied-data arithmetic only; it does
not construct a supplied equation `(4)` branch certificate, construct a
terminal extension, prove terminal `tilde t=0`, or prove Lemma 5.

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

## 2026-06-21 Lean Lemma 5 equation `(4)` no terminal upper extension example

Reproduction:
`reproduction-lemma5-eq4-no-terminal-upper-extension-example-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-no-terminal-upper-extension-example.md`.
Review artifact:
`review-lemma5-eq4-no-terminal-upper-extension-example-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_terminalEndpoint_values_ell3_a2_p1_allWidthsTwo
aoyagiLemma5Eq4_no_terminalUpperNatExtension_ell3_a2_p1_allWidthsTwo
```

For `ell=3`, `a=2`, `p=1`, `M=3`, and all selected widths equal to `2`, any
supplied equation `(4)` certificate is incompatible with the supplied terminal
upper-chain extension
`T(S_(ell+1)-1)=Htilde'_ell`.  In this tuple the printed terminal-collision
branch value is `1`, while `Htilde'_ell=0`.

This combines the existing terminal-extension obstruction with the closed
Definition 3-shaped counterexample.  It does not construct a supplied equation
`(4)` branch certificate, construct a terminal extension, prove terminal
`tilde t=0`, or prove Lemma 5.

## 2026-06-20 Lean Lemma 5 equation `(3)` interval obstruction

Reproduction:
`reproduction-lemma5-eq3-interval-obstruction-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-interval-obstruction.md`.
Review artifact:
`review-lemma5-eq3-interval-obstruction-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq3_boundaryValue_gt_upperNat
aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat
aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat_of_two_le
```

For a supplied equation `(3)` certificate, the special boundary value is
`Htilde'_(ell-a+1)+1`, hence strictly above the upper endpoint of the
same-coordinate interval at coordinate `ell-a+1`.  Therefore it is not in the
Nat-indexed same-coordinate interval value set.  In the strict boundary case
`2<=a`, this says the selected-span boundary singleton is outside the interval
family counted by the `Htilde` value-set layer.

This is finite interval bookkeeping only.  It does not construct equation
`(3)`'s displayed vector, prove terminal `tilde t=0`, introduced-label
status, vector admissibility, Case 1(2) chart sequence, Lemma 5 order count,
normal crossings, or RLCT extraction.

## 2026-06-20 Lean Lemma 5 equation `(4)` interval classifier

Reproduction:
`reproduction-lemma5-eq4-interval-classifier-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-interval-classifier.md`.
Review artifact:
`review-lemma5-eq4-interval-classifier-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_iff_two_mul_le
aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_of_two_mul_le
aoyagiLemma5Eq4_boundaryValue_not_mem_intervalValueSetNat_of_lt_two_mul
```

For a supplied equation `(4)` certificate in the strict boundary case
`1<=p`, `p+1<a`, and `p<=ell-a`, the special boundary value
`T(C.point (p+(ell-a)+1)-1)` belongs to the same-coordinate interval value set
at coordinate `p+(ell-a)` exactly when `2*p<=a+1`.  The proof uses the
supplied boundary value `Htilde'_(p+ell-a)-p+1` and the already-formalised
interval excess formula
`Htilde'_(j)-Htilde_(j)=min(j,ell-j,a,ell-a)`.  At `j=p+(ell-a)`, this excess
reduces to `min(ell-a,a-p)`, so membership is equivalent to
`p-1<=min(ell-a,a-p)`, hence to `2*p<=a+1`.

This is a classifier, not a uniform obstruction.  It does not construct
equation `(4)`'s displayed vector, prove terminal `tilde t=0`,
introduced-label status, vector admissibility, Case 1(2) chart sequence,
Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-20 Lean Lemma 5 equation `(4)` boundary-coordinate window

Reproduction:
`reproduction-lemma5-eq4-boundary-coordinate-window-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-boundary-coordinate-window.md`.
Review artifact:
`review-lemma5-eq4-boundary-coordinate-window-a5.md`.

Lean now proves:

```text
aoyagiHtildeUpperNat_succ_eq_add_selectedWidthNat_sub_increment
aoyagiLemma5Eq4_boundaryCoordinate_intervalExcess_eq_min
aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate
aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow
aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow_min
aoyagiLemma5Eq4_boundaryValue_gt_boundaryUpper_of_p1_sourceSelected
aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_p1_sourceSelected
```

For a supplied equation `(4)` certificate in the strict boundary case
`p+1<a`, the special boundary point lies in selected block
`r=p+(ell-a)+1`.  At that boundary block's own coordinate, the value
`T(C.point r-1)=Htilde'_(r-1)-p+1` belongs to the same-coordinate interval
exactly when the selected width `W_r` lies in the window

```text
M-p+1 <= W_r <= M-p+1+excess(ell,a,r).
```

The excess at this coordinate reduces to `min(ell-a,a-p-1)`.  The source
`p=1` corollary combines this with Definition 3's selected-width upper bound
`W_r<=M-1`, proving the boundary value is strictly above the upper endpoint
and hence not in the boundary-coordinate interval.

This is finite supplied-branch and interval arithmetic only.  It does not
construct equation `(4)`'s displayed vector, prove terminal `tilde t=0`,
introduced-label status, vector admissibility, Case 1(2) chart sequence,
Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 equation `(4)` boundary membership forces `p`

Reproduction:
`reproduction-lemma5-eq4-boundary-membership-forces-p-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-boundary-membership-forces-p.md`.
Review artifact:
`review-lemma5-eq4-boundary-membership-forces-p-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_forces_two_le_p_of_sourceSelected
aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_sourceSelected_of_p_lt_two
```

For a supplied equation `(4)` certificate in the strict boundary case
`p+1<a`, if the special boundary value belongs to its own
boundary-coordinate interval, then Definition 3's selected-width hypotheses
force `2<=p`.  The proof combines the already-proved lower edge of the
boundary-coordinate width window,

```text
M-p+1 <= W_r,
```

with the source-selected upper bound

```text
W_r <= M-1.
```

The companion wrapper says that `p<2` rules out boundary-coordinate
membership.  This is a necessary condition only; it does not prove membership
for `p>=2`, construct equation `(4)`'s displayed vector, prove terminal
`tilde t=0`, introduced-label status, vector admissibility, Case 1(2) chart
sequence, Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 equation `(4)` p=2 membership guardrail

Reproduction:
`reproduction-lemma5-eq4-boundary-membership-p2-example-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-boundary-membership-p2-example.md`.
Review artifact:
`review-lemma5-eq4-boundary-membership-p2-example-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_example
aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_sourceSelected_example
```

For the concrete selected-width tuple

```text
ell=5, a=4, p=2, M=5, W_i=4 for all i,
```

any supplied equation `(4)` certificate puts the strict boundary value in its
boundary-coordinate interval.  The width window is `4<=W_r<=5` at
`r=p+(ell-a)+1=4`, and `W_r=4`.

The source-selected wrapper also Lean-packages the selected-width sum and
strict selected-width inequalities for the same constant tuple, while keeping
the membership conclusion conditional on a supplied equation `(4)` certificate.

This is a guardrail for the previous obstruction: `2<=p` is only a necessary
condition for boundary-coordinate membership, not a theorem that membership
always fails for `p>=2`.  The example intentionally does not satisfy the older
own-coordinate guard `p<=ell-a`; that guard belongs to the classifier at
coordinate `p+(ell-a)`, not the boundary-coordinate theorem.  The checkpoint
does not construct the supplied certificate or displayed vector, prove
terminal `tilde t=0`, introduced-label status, vector admissibility, Case
1(2) chart sequence, Lemma 5 order count, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` own-coordinate offset

Reproduction:
`reproduction-lemma5-eq5-own-coordinate-offset-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-own-coordinate-offset.md`.
Review artifact:
`review-lemma5-eq5-own-coordinate-offset-a5.md`.

Lean now proves:

```text
AoyagiLemma5Eq5OwnCoordinateBranch
aoyagiLemma5Eq5OffsetValueSet
aoyagiLemma5Eq5_offsetValue_injective
aoyagiLemma5Eq5OffsetValueSet_card
aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat
aoyagiLemma5Eq5_ownCoordinate_value
aoyagiLemma5Eq5_ownCoordinate_eq_label_pred
aoyagiLemma5Eq5_ownCoordinate_mem_intervalValueSetNat
aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet
```

For Aoyagi Lemma 5 equation `(5)`, Lean now records a supplied
own-coordinate branch.  The paper's `j0` is Lean coordinate `p`; the own
coordinate lies in block `C.block p s`, corresponding to paper block
`j=j0+1`.  The supplied branch gives

```text
T(s)=Htilde'_p-alpha.
```

Under the supplied label relation

```text
k=Htilde'_p+1-alpha,
```

this rewrites to `T(s)=k-1`.  If `alpha<=Htilde'_p-Htilde_p`, encoded by
`alpha<=aoyagiLemma5IntervalExcess ell a p`, the value belongs to the
same-coordinate interval value set at coordinate `p`.  The finite offset
values for `1<=alpha<=min(excess(ell,a,p),p-1)` have cardinality
`min(excess(ell,a,p),p-1)`.

This is supplied own-coordinate branch arithmetic only.  It does not
construct equation `(5)`'s displayed vector, prove source-label legality for
`k`, classify the whole selected span, prove terminal `tilde t=0`, prove
vector admissibility, build the Case 1(2) chart sequence, prove Lemma 5 order
count, normal crossings, or RLCT extraction.  A full selected-span equation
`(5)` classifier still needs the selected-range guard
`p+(a-alpha)+1<=ell` for the final cutoff.

## 2026-06-21 Lean Lemma 5 equation `(5)` piecewise certificate

Reproduction:
`reproduction-lemma5-eq5-piecewise-certificate-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-piecewise-certificate.md`.
Review artifact:
`review-lemma5-eq5-piecewise-certificate-a5.md`.

Lean now proves:

```text
AoyagiLemma5Eq5PiecewiseSourceVector
AoyagiLemma5Eq5SelectedSpanBranchValue
aoyagiLemma5Eq5_branchValue_of_block
aoyagiLemma5Eq5_selectedSpan_branchValue
aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
```

This extends the previous own-coordinate Eq(5) offset slice to a full supplied
branch certificate.  The paper block variable `j` is represented by Lean block
`b=j-1`, and paper `j0` is Lean coordinate `p`.  The supplied certificate
stores the five displayed Eq5 branches in zero-based form:

```text
first:      S < S_2-1;
preAlpha:  2 <= j <= alpha-1;
alphaToP:  alpha <= j <= j0;
postP:     j0 < j <= j0+(a-alpha)+1;
tail:      S >= S_(j0+(a-alpha)+2)-1.
```

Lean classifies any point in a selected block, and therefore any point in the
half-open selected span, into one of these supplied branch alternatives.  The
full supplied certificate also implies the narrower
`AoyagiLemma5Eq5OwnCoordinateBranch`, so the existing own-coordinate offset
and interval-membership lemmas apply.

This is still supplied branch bookkeeping only.  It does not construct
equation `(5)`'s displayed vector, prove source-label legality for `k`, prove
terminal `tilde t=0`, cover the terminal selected endpoint, prove vector
admissibility, build the Case 1(2) chart sequence, prove Lemma 5 order count,
normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` source label

Reproduction:
`reproduction-lemma5-eq5-source-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-source-label.md`.
Review artifact:
`review-lemma5-eq5-source-label-a5.md`.

Lean now proves:

```text
aoyagiHtildeLowerIncrementPrefix_le_prefixSum_of_selectedWidth_le_pred
aoyagiHtildeLowerNat_add_one_pos_any_of_sourceSelectedInequality
aoyagiPrefixSum_sub_current_le_mul_pred_of_selectedWidth_le_pred
aoyagiHtildeUpperNat_le_selectedWidth_of_selectedWidth_le_pred
aoyagiHtildeUpperNat_le_selectedWidth_of_sourceSelectedInequality
aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality
aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility
aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel
```

For equation `(5)`'s own-coordinate label

```text
k = Htilde'_p+1-alpha,
```

Definition 3's selected-width hypotheses and the supplied offset guard
`1<=alpha<=excess(ell,a,p)` prove

```text
1<=k<=W_p.
```

With explicit source-layer range and actual-width compatibility

```text
n((C.point p-1)+1)=W_p,
```

Lean proves `actualWidthLabel L n (C.point p-1) k`.  A supplied full Eq5
piecewise certificate also gives the own-coordinate value

```text
T(C.point p-1)=k-1.
```

This is conditional source-label arithmetic only.  It does not construct the
equation `(5)` displayed vector, prove arbitrary-point label legality across
the whole selected block, prove terminal `tilde t=0`, vector admissibility,
the Case 1(2) chart sequence, Lemma 5 order count, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` block source label

Reproduction:
`reproduction-lemma5-eq5-block-source-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-block-source-label.md`.
Review artifact:
`review-lemma5-eq5-block-source-label-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_actualWidthLabel_at_of_widthCompatibility
aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_block
aoyagiLemma5Eq5_sourceIndex_pos_of_ownBlock
aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_ownBlock_widthCompatibility
```

The previous source-label bridge was stated at the block's left endpoint
`C.point p-1`.  This refinement handles an arbitrary source index `S`.  The
theorem keeps the required actual-width bridge explicit:

```text
n(S+1)=W_p.
```

With `1<=S<=L`, the existing label bounds give
`actualWidthLabel L n S k`.  If a supplied Eq5 piecewise certificate and
`C.block p S` are also given, Lean proves

```text
T(S)=k-1
```

and the same actual-label conclusion.

The source-shaped wrapper derives the lower source-layer bound `1<=S` from
the Eq5 guards `1<=alpha<p`, selected-cutpoint positivity and monotonicity,
and the own-block lower endpoint.  It still keeps `S<=L` and `n(S+1)=W_p`
explicit.

This still does not prove actual-width compatibility for arbitrary block
points, upper source range, construct the displayed vector, prove terminal `tilde t=0`, vector
admissibility, the chart sequence, Lemma 5 order count, normal crossings, or
RLCT extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` source range and width bound

Reproduction:
`reproduction-lemma5-eq5-source-range-width-bound-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-source-range-width-bound.md`.
Review artifact:
`review-lemma5-eq5-source-range-width-bound-a5.md`.

Lean now proves:

```text
AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_terminalEndpoint_le
AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_lastPoint_le
AoyagiSelectedCutpoints.block_sourceIndex_le_of_terminalEndpoint_le
AoyagiSelectedCutpoints.block_sourceIndex_le_of_lastPoint_le
aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound
aoyagiLemma5Eq5_piecewise_block_actualWidthLabel_of_widthBound
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_widthBound
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthCompatibility
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
```

The selected-cutpoint helpers derive the upper source-layer range for a
selected-block member from the source-shaped compatibility
`C.point ell<=L+1`.  The Eq5 source-label bridge is also weakened from the
equality-shaped width hypothesis `n(S+1)=W_p` to the sufficient bound
`W_p<=n(S+1)`.  Combining these, a supplied Eq5 piecewise certificate and
`C.block p S` prove both `T(S)=k-1` and `actualWidthLabel L n S k` under
`C.point ell<=L+1` and `W_p<=n(S+1)`.

This still does not prove the width bound from Definition 3, construct the
displayed vector, prove terminal `tilde t=0`, vector admissibility, the Case
1(2) chart sequence, Lemma 5 order count, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` block width dominance

Reproduction:
`reproduction-lemma5-eq5-block-width-dominance-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-block-width-dominance.md`.
Review artifact:
`review-lemma5-eq5-block-width-dominance-a5.md`.

Lean now proves:

```text
AoyagiSelectedCutpoints.block_sourceLayer_mem_Ico
AoyagiSelectedCutpoints.block_sourceLayer_eq_left_or_between
AoyagiSelectedCutpoints.point_ne_of_between_adjacent
AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block
AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min
AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected
AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected_lt
aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_blockWidth
aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_leftMin
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected_lt
```

The new cutpoint helper turns `C.block p S` into the source-layer interval
`C.point p <= S+1 < C.point(p+1)`.  Therefore a block-local actual-width lower
bound gives the Eq5 width hypothesis `W_p<=n(S+1)`.  The Eq5 wrappers combine
this with the previous last-cutpoint source-range theorem and the supplied
own-block value `T(S)=k-1`.

The source check records an obstruction to deriving this width bound from
Definition 3 alone: Definition 3's non-selected condition is value-level, so
an unselected layer with a duplicate selected width value is not controlled by
that condition.  The Lean theorem therefore keeps explicit block-local
dominance, left-endpoint-minimum, or index-level off-selected dominance
hypotheses.

This still does not prove block-local width dominance from Definition 3,
construct the displayed vector, prove terminal `tilde t=0`, vector
admissibility, the Case 1(2) chart sequence, Lemma 5 order count, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` width-bound counterexample

Reproduction:
`reproduction-lemma5-eq5-width-bound-counterexample-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-width-bound-counterexample.md`.
Review artifact:
`review-lemma5-eq5-width-bound-counterexample-a5.md`.

Lean now proves the duplicate-width obstruction as a closed guardrail:

```text
aoyagiLemma5Eq5_blockWidthBound_not_forced_by_selectedWidthHypotheses_example
```

The witness has selected cutpoints `1,3,5,7`, selected widths `1,2,2,2`,
actual widths matching these at the selected cutpoints, and actual width
`n(6)=1`.  With `p=2` and `S=5`, the selected block condition `C.block p S`
holds, but the Eq5 width bound fails:

```text
not aoyagiSelectedWidthNat 3 m p <= n(S+1).
```

The theorem also includes the value-level non-selected-width condition.  This
records the source issue precisely: the bad layer has width value `1`, which
is already a selected value, so Aoyagi Definition 3's value-level
non-selected condition does not control it.

This is a guardrail, not a construction theorem.  It does not refute the
conditional block-width dominance bridges; it explains why their extra
index-level hypotheses are explicit.

## 2026-06-21 Lean Lemma 5 equation `(5)` offset/excess decomposition

Reproduction:
`reproduction-lemma5-eq5-offset-excess-decomposition-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-offset-excess-decomposition.md`.
Review artifact:
`review-lemma5-eq5-offset-excess-decomposition-a5.md`.

Lean now proves:

```text
aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator
aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min
```

The first theorem decomposes the interval excess at coordinate `p` into the
cardinality of the Eq5 strict-offset value set plus one rising-coordinate
indicator:

```text
excess(ell,a,p)
  = card(Eq5OffsetValueSet p)
    + if 1<=p and p<=a and p<=ell-a then 1 else 0.
```

The second theorem identifies the missing value in the rising case as finite
set bookkeeping: when `p<=a` and `p<=ell-a`, the lower endpoint `Htilde_p` is
not in the Eq5 strict-offset value set, since reaching it from `Htilde'_p`
would require the forbidden offset `alpha=p`.

This is only count scaffolding below Lemma 5.  It does not show that equation
`(3)` or `(4)` realises the extra value, construct any displayed vector,
prove source-label legality, terminal `tilde t=0`, vector admissibility,
chart sequence, pole order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 equations `(3)`/`(4)` own-coordinate actual-label adapters

Reproduction:
`reproduction-lemma5-eq3-eq4-own-coordinate-actual-label-adapters-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-eq4-own-coordinate-actual-label-adapters.md`.
Review artifact:
`review-lemma5-eq3-eq4-own-coordinate-actual-label-adapters-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_widthCompatibility
aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_sourceSelected_slack
aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
```

These are thin adapters over existing results.  For supplied equation `(4)`
piecewise data, the theorem combines the own-coordinate value
`T(C.point p-1)=Htilde_p` with the actual-label bridge for
`k=Htilde_p+1`.  For supplied equation `(3)` piecewise data, the theorem
combines the own-coordinate value `T(C.point 1-1)=Htilde'_1` with the
actual-label bridge for `k=Htilde'_1+1`, keeping the explicit slack
`W_1+2<=M`.

The last-cutpoint wrappers replace the manual upper source-range hypothesis by
`C.point ell<=L+1`.  They keep actual-width compatibility explicit.

These theorems do not construct the displayed vectors, derive actual-width
compatibility from Definition 3, remove the Eq3 slack, prove terminal
`tilde t=0`, vector admissibility, chart sequence, pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` interval and introduced-label wrappers

Reproduction:
`reproduction-lemma5-eq5-interval-introduced-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-interval-introduced-label.md`.
Review artifact:
`review-lemma5-eq5-interval-introduced-label-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt
aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min
aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_subset_intervalValueSetNat_of_le_min
aoyagiLemma5Eq5_insertLower_offsetCard_add_one_eq_intervalCard_of_le_min
aoyagiLemma5Eq5_piecewise_ownBlock_intervalValue_introducedLabel_of_lastPoint_widthBound
```

The finite-set wrappers work in the rising region
`1<=p`, `p<=a`, `p<=ell-a`.  They insert the lower endpoint into the strict
Eq5 offset-value set and prove that the inserted set has cardinality equal to
the interval excess, lies inside the same-coordinate interval value set, and
is one value short of the full interval.

The source-label wrapper combines supplied Eq5 own-block data with the
last-cutpoint/width-bound actual-label wrapper.  It proves `T S` is in the
same-coordinate interval, `T S=k-1`, and
`introducedLabel L n S k S k` in the post-advance state `(S,k)`.

This still does not construct the displayed vector, prove that equations
`(3)` or `(4)` realise the remaining interval value, derive
`W_p<=n(S+1)` from Definition 3 alone, prove terminal `tilde t=0`, vector
admissibility, chart sequence, pole order, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 equations `(3)`/`(4)` own-coordinate introduced-label wrappers

Reproduction:
`reproduction-lemma5-eq3-eq4-own-coordinate-introduced-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-eq4-own-coordinate-introduced-label.md`.
Review artifact:
`review-lemma5-eq3-eq4-own-coordinate-introduced-label-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint
aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint
```

These are post-advance wrappers over the existing Eq3/Eq4 last-point
actual-label adapters.  For the own coordinate `S`, they prove `T S=k-1` and
`introducedLabel L n S k S k`.  The state is deliberately `(S,k)`, matching
the fact that the branch value is `k-1` after label `k` has been introduced.

The wrappers keep the existing actual-width compatibility hypotheses.  Eq3
also keeps the explicit slack `W_1+2<=M`.  They do not construct displayed
vectors, prove terminality, vector admissibility, chart sequence, pole order,
normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` interval erase-upper equality

Reproduction:
`reproduction-lemma5-eq5-interval-erase-upper-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-interval-erase-upper.md`.
Review artifact:
`review-lemma5-eq5-interval-erase-upper-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
aoyagiLemma5Eq5_upperEndpoint_not_mem_insert_lowerEndpoint_offsets_of_le_min
aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
```

In the rising region `1<=p`, `p<=a`, `p<=ell-a`, the lower endpoint plus the
strict Eq5 offset values is exactly the same-coordinate interval value set
with the upper endpoint erased.  The proof uses the previous subset and
cardinality bridge, plus a new upper-endpoint nonmembership proof: the upper
endpoint is not the lower endpoint because the gap is `p>=1`, and it is not a
strict offset value because that would force offset `alpha=0`.

This is still finite-set count scaffolding.  It does not prove that equations
`(3)` or `(4)` realise the erased upper endpoint, construct any displayed
vector, prove source-label legality, terminality, vector admissibility, chart
coverage, Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 introduced-label finite-domain adapters

Reproduction:
`reproduction-lemma5-introduced-label-finset-adapters-a5.md`.
Statement card:
`statement-card-a5-lemma5-introduced-label-finset-adapters.md`.
Review artifact:
`review-lemma5-introduced-label-finset-adapters-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound
```

These are finite-domain versions of the existing introduced-label wrappers.
They keep the same hypotheses and convert the existing
`introducedLabel L n S k S k` conclusion into
`Sigma.mk S k ∈ introducedLabelFinset L n S k` using
`mem_introducedLabelFinset.mpr`.  The Eq5 wrapper also carries forward the
same-coordinate interval membership already proved by the introduced-label
wrapper.

This is API cleanup only.  It does not provide `LabelExponentCertificate`
fields, terminal exponents, least values, displayed-vector construction,
terminality, admissibility, chart sequence, Lemma 5 order count, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 interval-size profile

Reproduction:
`reproduction-lemma5-interval-size-profile-a5.md`.
Statement card:
`statement-card-a5-lemma5-interval-size-profile.md`.
Review artifact:
`review-lemma5-interval-size-profile-a5.md`.

Lean now proves:

```text
aoyagiLemma5IntervalSize_eq_succ_of_le_min
aoyagiLemma5IntervalSize_eq_min_succ_of_min_le_of_le_max
aoyagiLemma5IntervalSize_eq_falling_of_max_le
aoyagiLemma5IntervalSize_sourcePiecewise
```

These theorem names reproduce the three-region interval-cardinality profile
displayed in Aoyagi Lemma 5.  They work only with
`aoyagiLemma5IntervalSize ell a j = 1 + min(j,ell-j,a,ell-a)`, under `a<=ell`
and `j<=ell` for the combined piecewise theorem.

This is still finite arithmetic below Lemma 5.  It does not construct the
displayed source vectors, prove that the counted values are realised by
admissible vectors, prove terminality, chart sequence, Lemma 5 order count,
normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 equation `(5)` offset finset adapter

Reproduction:
`reproduction-lemma5-eq5-offset-finset-adapter-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-offset-finset-adapter.md`.
Review artifact:
`review-lemma5-eq5-offset-finset-adapter-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_ownBlock_offsetValue_mem_introducedLabelFinset_of_lastPoint_widthBound
```

For one supplied Eq5 piecewise certificate and one own-block source index, the
branch value is simultaneously a strict Eq5 offset value, a same-coordinate
interval value, equal to `k-1`, and a member of `introducedLabelFinset L n S k`
as `Sigma.mk S k`.

This is a conjunction adapter over existing facts.  It does not construct the
Eq5 displayed vector, quantify over all `alpha` at once, derive the explicit
actual-width lower bound from Definition 3, prove terminality, chart sequence,
Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq4 lower endpoint and Eq5 erase-upper set

Reproduction:
`reproduction-lemma5-eq4-lower-endpoint-eq5-erase-upper-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-lower-endpoint-eq5-erase-upper.md`.
Review artifact:
`review-lemma5-eq4-lower-endpoint-eq5-erase-upper-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min
```

For a supplied Eq4 piecewise certificate in the rising region, the Eq4
own-coordinate value can replace the abstract lower endpoint in the Eq5
lower-plus-strict-offset equality:

```text
insert (T(C.point p-1)) Eq5OffsetValueSet_p
  = HtildeIntervalValueSet_p.erase Htilde'_p.
```

This is a finite-set substitution wrapper only.  It does not realise the
erased upper endpoint, construct Eq4 or Eq5 displayed vectors, prove
terminality, chart sequence, Lemma 5 order count, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 Eq5 offsets erase both endpoints

Reproduction:
`reproduction-lemma5-eq5-offsets-erase-endpoints-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-offsets-erase-endpoints.md`.
Review artifact:
`review-lemma5-eq5-offsets-erase-endpoints-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min
```

In the rising region, the strict Eq5 offset finite set is exactly the
same-coordinate interval after erasing both endpoints:

```text
Eq5OffsetValueSet_p
  = (HtildeIntervalValueSet_p.erase Htilde'_p).erase Htilde_p.
```

This is derived from the existing lower-plus-offset erase-upper equality and
the existing proof that the lower endpoint is not a strict Eq5 offset.  It is
finite-set bookkeeping only and does not construct displayed vectors, realise
the endpoints, prove terminality, chart sequence, Lemma 5 order count, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq3/Eq4 interval finset adapters

Reproduction:
`reproduction-lemma5-eq3-eq4-interval-finset-adapters-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-eq4-interval-finset-adapters.md`.
Review artifact:
`review-lemma5-eq3-eq4-interval-finset-adapters-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint
aoyagiLemma5Eq3_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint
```

For supplied Eq4/Eq3 piecewise certificates, the own-coordinate branch value is
packaged as a same-coordinate interval value, a label predecessor `k-1`, and a
member of `introducedLabelFinset L n S k`.

This is a conjunction adapter over existing endpoint interval-membership and
introduced-label finite-domain facts.  It keeps Eq3's explicit slack and Eq4's
repaired guards.  It does not construct displayed vectors, provide terminal
exponent/least-value data, prove terminality, chart sequence, Lemma 5 order
count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 one-step introduced domain insert

Reproduction:
`reproduction-lemma5-eq5-domain-insert-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-domain-insert.md`.
Review artifact:
`review-lemma5-eq5-domain-insert-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_succ_eq_insert_of_lastPoint_widthBound
```

For one supplied Eq5 own-block branch whose label is `J+1`, advancing the
introduced-label finite domain from `(S,J)` to `(S,J+1)` inserts exactly
`Sigma.mk S (J+1)`.

This is finite-domain bookkeeping only.  It uses the existing Eq5 actual-label
wrapper and the generic `introducedLabelFinset_succ_eq_insert` theorem.  It
does not construct Eq5 vectors, quantify over all `alpha`, provide
terminal-exponent or least-value data, prove terminality, chart sequence,
Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 one-step introduced domain cardinality

Reproduction:
`reproduction-lemma5-eq5-domain-card-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-domain-card.md`.
Review artifact:
`review-lemma5-eq5-domain-card-a5.md`.

Lean now proves:

```text
introducedLabelFinset_card_succ_eq_succ
aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_card_succ_eq_succ_of_lastPoint_widthBound
```

For one supplied Eq5 own-block branch whose label is `J+1`, advancing the
introduced-label finite domain from `(S,J)` to `(S,J+1)` increases the finite
domain cardinality by exactly one.

This is the cardinality form of the preceding insert wrapper.  It uses the
generic insert equality, the generic proof that `(S,J+1)` was not previously
introduced at stage `J`, and the existing Eq5 actual-label wrapper.  It does
not construct Eq5 vectors, quantify over all `alpha`, provide
terminal-exponent or least-value data, prove terminality, chart sequence,
Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 erased-endpoints finset adapter

Reproduction:
`reproduction-lemma5-eq5-interval-erase-endpoints-finset-adapter-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-interval-erase-endpoints-finset-adapter.md`.
Review artifact:
`review-lemma5-eq5-interval-erase-endpoints-finset-adapter-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_ownBlock_eraseEndpoints_mem_introducedLabelFinset_of_lastPoint_widthBound
```

For one supplied Eq5 own-block branch in the rising region, the branch value
lies in the same-coordinate interval with both endpoints erased, equals
`k-1`, and has `Sigma.mk S k` in the introduced-label finite domain.

This is a one-branch adapter over the existing strict-offset finite-domain
wrapper and the existing finite-set equality identifying Eq5 strict offsets
with the interval after erasing both endpoints.  It does not package all Eq5
branches, realise the erased endpoints by Eq3/Eq4, construct displayed
vectors, provide terminal-exponent or least-value data, prove terminality,
chart sequence, Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq3/Eq4 one-step domain insert and cardinality

Reproduction:
`reproduction-lemma5-eq3-eq4-domain-insert-card-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-eq4-domain-insert-card.md`.
Review artifact:
`review-lemma5-eq3-eq4-domain-insert-card-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_ownCoordinateFinset_succ_eq_insert_of_lastPoint
aoyagiLemma5Eq4_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint
aoyagiLemma5Eq3_ownCoordinateFinset_succ_eq_insert_of_lastPoint
aoyagiLemma5Eq3_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint
```

For supplied Eq4/Eq3 endpoint branches whose label is `J+1`, advancing the
introduced-label finite domain from `J` to `J+1` inserts the endpoint label and
increases finite-domain cardinality by one.

This is finite-domain bookkeeping only.  Eq4 keeps the repaired guards and
actual-width compatibility explicit; Eq3 keeps the one-unit slack and
actual-width compatibility explicit.  It does not construct displayed vectors,
provide terminal-exponent or least-value data, prove terminality, chart
sequence, Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 Case 2 recurrence weight update

Reproduction:
`reproduction-lemma5-eq5-case2-weight-update-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-case2-weight-update.md`.
Review artifact:
`review-lemma5-eq5-case2-weight-update-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_ownBlock_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_widthBound
```

For one supplied Eq5 own-block branch whose label is `J+1`, a supplied Case 2
recurrence post-state with the standard new-label data has
`post.weight i = u * pre.weight i` for every row `i` with `J+1 <= i`.

This is conditional recurrence bookkeeping only.  It uses the existing Eq5
actual-label wrapper and the generic supplied-post-data recurrence theorem.  It
does not prove that a blow-up chart produces the post-state, construct Eq5
vectors, quantify over all `alpha`, provide terminal-exponent or least-value
data, prove terminality, chart sequence, Lemma 5 order count, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq3/Eq4 Case 2 recurrence weight update

Reproduction:
`reproduction-lemma5-eq3-eq4-case2-weight-update-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-eq4-case2-weight-update.md`.
Review artifact:
`review-lemma5-eq3-eq4-case2-weight-update-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint
aoyagiLemma5Eq3_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint
```

For one supplied Eq4 or Eq3 endpoint branch whose label is `J+1`, a supplied
Case 2 recurrence post-state with the standard new-label data has
`post.weight i = u * pre.weight i` for every row `i` with `J+1 <= i`.

This is conditional recurrence bookkeeping only.  It uses the existing Eq3/Eq4
actual-label wrappers and the generic supplied-post-data recurrence theorem.
Eq4's repaired guards, Eq3's explicit slack, actual-width compatibility, and
the supplied post-data package remain explicit.  It does not prove that a
blow-up chart produces the post-state, construct Eq3/Eq4 vectors, provide
terminal-exponent or least-value data, prove terminality, chart sequence,
Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 supplied exponent-domain extension

Reproduction:
`reproduction-lemma5-supplied-exponent-domain-extension-a5.md`.
Statement card:
`statement-card-a5-lemma5-supplied-exponent-domain-extension.md`.
Review artifact:
`review-lemma5-supplied-exponent-domain-extension-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint
aoyagiLemma5Eq3_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint
aoyagiLemma5Eq5_ownBlock_extendExponentDomain_succ_current_of_lastPoint_widthBound
```

For one supplied Eq4, Eq3, or Eq5 branch whose label is `J+1`, the source-label
wrappers supply the new label's `introducedLabel` field at state `(S,J+1)`.
If the terminal-exponent equality and least-value proof for the new label are
also supplied, the generic one-step theorem extends
`IntroducedLabelExponentCertificates` from `(S,J)` to `(S,J+1)`.

This is a supplied-certificate boundary.  It does not compute the terminal
exponent or least value for any branch.  Eq3 keeps the explicit slack and Eq5
keeps the explicit own-block width bound.  It does not construct displayed
vectors, prove terminality, chart sequence, Lemma 5 order count, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 first-interval supplied-shaped coverage

Reproduction:
`reproduction-lemma5-first-interval-supplied-shaped-coverage-a5.md`.
Statement card:
`statement-card-a5-lemma5-first-interval-supplied-shaped-coverage.md`.
Review artifact:
`review-lemma5-first-interval-supplied-shaped-coverage-a5.md`.

Lean now proves:

```text
aoyagiLemma5_suppliedEq3Upper_Eq4_firstInterval_insertOwnCoordinates_eq_intervalValueSetNat
```

For the first same-coordinate interval, a supplied Eq4 lower endpoint and a
separately supplied Eq3-shaped upper endpoint fill the two endpoints missing
from the strict Eq5 offset set.  The proof combines the existing Eq4/Eq5
erase-upper equality with the separately supplied Eq3-shaped own-coordinate
upper endpoint and `Finset.insert_erase`.  The printed equation `(3)` excludes
`(S_2-1,Htilde'_1+1)`, so this is not claimed to be source-backed by the
printed Eq3 branch.

This is only first-interval finite-set coverage for supplied branch
certificates.  Eq3 keeps its explicit slack and the rising-region guard
`1 <= ell-a` remains explicit.  The theorem does not construct displayed
vectors, prove source-label legality, cover all intervals, package all branch
families, prove Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 supplied upper and Eq4 interval coverage

Reproduction:
`reproduction-lemma5-supplied-upper-eq4-interval-coverage-a5.md`.
Statement card:
`statement-card-a5-lemma5-supplied-upper-eq4-interval-coverage.md`.
Review artifact:
`review-lemma5-supplied-upper-eq4-interval-coverage-a5.md`.

Lean now proves:

```text
aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_le_min
```

For any one coordinate in the rising range, a supplied upper endpoint value
and a supplied Eq4 lower own-coordinate value fill the endpoints missing from
the strict Eq5 offset set.  The upper equality is an explicit hypothesis; this
is not a claim that printed Eq3 supplies an upper endpoint or source label.

This is one-interval finite-set bookkeeping only.  It keeps the rising-region
guards `1 <= p`, `p <= a`, and `p <= ell-a` explicit.  It does not construct
displayed vectors, prove source-label legality, cover all intervals, package
all branch families, prove Lemma 5 order count, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 Eq3-shaped component interval coverage

Reproduction:
`reproduction-lemma5-eq3-shaped-component-interval-coverage-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-shaped-component-interval-coverage.md`.
Review artifact:
`review-lemma5-eq3-shaped-component-interval-coverage-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap
aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat
```

For one coordinate in the rising range, the supplied Eq3-shaped component
value is the upper endpoint, and this instantiates the supplied-upper interval
coverage wrapper with the supplied Eq4 lower endpoint and strict Eq5 offsets.

This is component-value and one-interval finite-set bookkeeping only.  It does
not prove source-label legality or introduced-label status for the Eq3-shaped
component, construct displayed vectors, cover all intervals, package all
branch families, prove Lemma 5 order count, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 Eq3-shaped component supplied label bounds

Reproduction:
`reproduction-lemma5-eq3-shaped-component-supplied-label-bounds-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-shaped-component-supplied-label-bounds.md`.
Review artifact:
`review-lemma5-eq3-shaped-component-supplied-label-bounds-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_mem_introducedLabelFinset_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_intervalValue_mem_introducedLabelFinset_of_lastPoint_labelBounds
```

For one Eq3-shaped upper component, supplied actual-width compatibility and
supplied label bounds package the component as an actual source label,
introduced label, finite introduced-label member, and interval value.

This is source-label packaging under supplied bounds only.  It does not derive
p-general Eq3 label legality from Definition 3, construct displayed vectors,
cover all intervals, package all branch families, prove Lemma 5 order count,
normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq3 component domain/recurrence/exponent wrappers

Reproduction:
`reproduction-lemma5-eq3-component-domain-recurrence-exponent-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-component-domain-recurrence-exponent.md`.
Review artifact:
`review-lemma5-eq3-component-domain-recurrence-exponent-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq3_componentFinset_succ_eq_insert_of_lastPoint_labelBounds
aoyagiLemma5Eq3_componentFinset_card_succ_eq_succ_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_extendExponentDomain_succ_current_of_lastPoint_labelBounds
```

For one Eq3-shaped upper component with supplied actual-width compatibility
and supplied label bounds, the component feeds the generic one-step
introduced-domain insert, domain-cardinality, Case 2 recurrence-weight, and
supplied exponent-domain extension APIs.

This is API bookkeeping under supplied bounds.  It does not derive the label
bounds from Definition 3, compute terminal exponents or least values,
construct displayed vectors, cover all intervals, package all branch families,
prove Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 strict-offset rising count

Reproduction:
`reproduction-lemma5-eq5-strict-offset-rising-count-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-strict-offset-rising-count.md`.
Review artifact:
`review-lemma5-eq5-strict-offset-rising-count-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min
```

In the rising region `1<=p`, `p<=a`, and `p<=ell-a`, the strict equation `(5)`
offset-value set has cardinality `p-1`.  The proof rewrites the existing
offset-cardinality theorem by the rising-region interval-excess equality
`excess=p`.

This is one-coordinate finite count bookkeeping only.  It does not construct
Eq5 displayed vectors, prove source-label legality, realise endpoints, sum
over all coordinates, package all branches, prove Lemma 5 order count, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq4 lower plus Eq5 offset count

Reproduction:
`reproduction-lemma5-eq4-lower-plus-eq5-offset-count-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-lower-plus-eq5-offset-count.md`.
Review artifact:
`review-lemma5-eq4-lower-plus-eq5-offset-count-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_le_min
```

In the rising region, a supplied Eq4 lower own-coordinate value adds one value
to the strict Eq5 offset-value set.  The proof rewrites the supplied Eq4 value
to the abstract lower endpoint, uses the existing lower-plus-offset
cardinality theorem, and compares with the strict Eq5 rising count.

This is one-coordinate finite count bookkeeping only.  It does not prove
source-label legality, construct Eq4 or Eq5 displayed vectors, realise the
upper endpoint, aggregate over all coordinates, package all branches, prove
Lemma 5 order count, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq3/Eq4 interval cardinality

Reproduction:
`reproduction-lemma5-eq3-eq4-interval-cardinality-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-eq4-interval-cardinality.md`.
Review artifact:
`review-lemma5-eq3-eq4-interval-cardinality-a5.md`.

Lean now proves:

```text
aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_card_eq_intervalSize
aoyagiLemma5_suppliedEq3Upper_Eq4_insertComponents_card_eq_offsetCard_add_two
```

For one rising-coordinate interval, a supplied Eq3-shaped upper component,
supplied Eq4 lower endpoint, and strict Eq5 offsets have cardinality equal to
the interval size; equivalently, in the rising region, they have the strict
Eq5 offset-set cardinality plus two.

This is one-coordinate finite cardinality bookkeeping only.  It does not prove
source-label legality, construct displayed vectors, aggregate over all
coordinates, package all branches, prove Lemma 5 order count, normal crossings,
or RLCT extraction.

## 2026-06-21 Source reconstruction of Lemma 5 chart-family gap

Reproduction:
`reproduction-lemma5-source-chart-family-reconstruction-a5.md`.
Review artifact:
`review-lemma5-source-chart-family-reconstruction-a5.md`.

The remaining source-facing Lemma 5 gap is now recorded as an obligation table
rather than a Lean target.  A source-backed order-count theorem would need, for
each displayed branch family, legal source labels, vectorwise
`Ttilde<=T<=Ttilde'` bounds, Lemma 4 increment checks, a concrete Case 1(2)
chart sequence, terminal `tilde t=0`, and a nonduplication/coverage argument.

Existing Lean proves finite counts and many supplied one-coordinate wrappers,
but the PDF's final sentence does not spell out the Case 1(2) chart sequence.
Do not start a source-backed Lemma 5 Lean theorem until the vectorwise bounds
and Lemma 4 increment checks have been reproduced under explicit guards.

## 2026-06-21 Lemma 5 printed equations fail Lemma 4 witness checks

Reproduction:
`reproduction-lemma5-printed-equations-lemma4-obstructions-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-printed-lower-bound-obstruction.md`.
Review artifact:
`review-lemma5-printed-equations-lemma4-obstructions-a5.md`.

Xhigh equation-specific source passes checked equations `(3)`, `(4)`, and
`(5)` against Lemma 4's requirements.  The result is stronger than the prior
obligation table: each printed equation has a concrete obstruction to being a
complete Lemma 4 witness as printed.

Equation `(3)` assigns `Htilde'_(ell-a+1)+1` at the special endpoint, so the
componentwise upper bound `T<=Ttilde'` fails there.  Away from the terminal
edge, the adjacent increment also becomes `M+1`.

Equation `(4)`'s special one-point line gives the increment
`W_(q+1)-1`, where `q=j0+ell-a+1`.  Definition 3 gives
`W_(q+1)<=M-1`, so this increment is at most `M-2`, not `M-1` or `M`.

Equation `(5)` needs additional guards beyond the printed ones.  Lean now
records a concrete conditional supplied-certificate obstruction:

```text
aoyagiLemma5Eq5_piecewise_belowLowerCounterexample_allWidthsFour
aoyagiLemma5Eq5_piecewise_not_lowerBounded_allWidthsFour
```

For `ell=6`, `a=4`, all selected widths `4`, `M=5`, `p=2`, and `alpha=1`,
the supplied branch value at selected coordinate `4` is `-1`, while the lower
chain there is `0`.

Do not use equations `(3)`, `(4)`, or `(5)` as source-backed all-branch Lemma
4 witnesses in their printed form.  The next route must be either corrected
formula search or a supplied chart-family boundary.

## 2026-06-21 Lean Lemma 5 printed increment obstructions

Statement card:
`statement-card-a5-lemma5-printed-increment-obstructions.md`.
Review artifact:
`review-lemma5-printed-increment-obstructions-a5.md`.

Lean now records the finite increment part of the printed-equation obstruction
checkpoint:

```text
aoyagiLemma5Eq3_specialNextIncrement_eq_succ
aoyagiLemma5Eq3_specialNextIncrement_not_twoValue
aoyagiLemma5Eq4_specialIncrement_eq_selectedWidth_sub_one
aoyagiLemma5Eq4_specialIncrement_lt_pred_of_sourceSelected
aoyagiLemma5Eq4_specialIncrement_not_twoValue_of_sourceSelected
```

For Eq `(3)`, supplied adjacent `H`-values matching the nonterminal printed
special boundary make the next Lemma 4 increment equal to `M+1`.  For Eq
`(4)`, supplied adjacent `H`-values matching the special one-point line make
the corresponding increment equal to the next selected width minus one; under
Definition 3's selected-width hypotheses this is strictly below `M-1`.

These are conditional finite-chain theorems only.  They do not construct
displayed vectors, prove source-label legality, or search for corrected
formulas.

## 2026-06-21 Lean Lemma 5 supplied chart-family count boundary

Reproduction:
`reproduction-lemma5-supplied-chart-family-count-boundary-a5.md`.
Statement card:
`statement-card-a5-lemma5-supplied-chart-family-count-boundary.md`.
Review artifact:
`review-lemma5-supplied-chart-family-count-boundary-a5.md`.

The corrected-formula route is not recoverable from Aoyagi's PDF alone, so the
next honest Lean theorem is a supplied-data boundary.  Lean now defines

```text
AoyagiLemma5SuppliedNonbaseFamily
AoyagiLemma5SuppliedAdmissibleNonbaseFamily
```

and proves:

```text
aoyagiLemma5SuppliedNonbaseFamily_branch_card_eq_interval_card_sub_one
aoyagiLemma5SuppliedNonbaseFamily_count
aoyagiLemma5SuppliedNonbaseFamily_biUnion_count
AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_twoValueCount
```

The nonbase family carries, for each interior coordinate, a supplied base value
in the same-coordinate interval, an injective value map from supplied branches
onto the interval with that base erased, and cross-coordinate disjointness for
the finite-union count.  The admissible nonbase extension carries explicit
branchwise Lemma 4 obligations: `H_0=m_0`, lower/upper `Htilde` chain bounds,
two-value increments, and same-coordinate value equality.

This proves only the aggregate finite consequence of supplied coverage:

```text
1 + sum_j |branches j| = a*(ell-a)+1
1 + |union_j branches j| = a*(ell-a)+1
```

under the existing interval-count hypotheses.  It does not construct the
supplied branch family, prove that Aoyagi's printed equations `(3)`, `(4)`, or
`(5)` satisfy the fields, prove source-label legality, reconstruct the Case
1(2) chart sequence, prove terminal `tilde t=0`, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 full supplied family base branch

Reproduction:
`reproduction-lemma5-full-supplied-family-base-branch-a5.md`.
Statement card:
`statement-card-a5-lemma5-full-supplied-family-base-branch.md`.
Review artifact:
`review-lemma5-full-supplied-family-base-branch-a5.md`.

Lean now turns the leading `1` in the supplied Lemma 5 count into an explicit
supplied base branch.  The full branch set is

```text
{none} union union_j {some b : b in branches j}.
```

New Lean names:

```text
AoyagiLemma5SuppliedNonbaseFamily.fullBranches
AoyagiLemma5SuppliedNonbaseFamily.none_mem_fullBranches
AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_of_mem
AoyagiLemma5SuppliedNonbaseFamily.fullBranches_card
AoyagiLemma5SuppliedAdmissibleFamily
AoyagiLemma5SuppliedAdmissibleFamily.fullBranches
AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card
AoyagiLemma5SuppliedAdmissibleFamily.base_twoValueCount
```

The finite count uses the previous supplied nonbase union count, injectivity of
`some`, and disjointness of `none` from the `some` image.  The admissible full
family adds only the supplied base branch's Lemma 4 fields: `baseH`,
`baseH0`, lower/upper `Htilde` chain bounds, and two-value increments.

This is still a supplied-data boundary.  It does not construct the base branch
or nonbase family from Aoyagi's printed equations, prove source-label legality,
reconstruct the Case 1(2) chart sequence, prove terminal `tilde t=0`, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 full supplied family branchwise admissibility

Reproduction:
`reproduction-lemma5-full-supplied-family-branchwise-admissibility-a5.md`.
Statement card:
`statement-card-a5-lemma5-full-supplied-family-branchwise-admissibility.md`.
Review artifact:
`review-lemma5-full-supplied-family-branchwise-admissibility-a5.md`.

Lean now packages base and nonbase admissibility into a single tagged-branch
API:

```text
AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff
AoyagiLemma5SuppliedAdmissibleFamily.fullH
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_twoValueCount
```

The membership theorem characterizes `some b in fullBranches` as existence of
an interior coordinate `j` with `b in branches j`.  The branch chain is
definitionally `fullH none = baseH` and `fullH (some b) = H b`.  Under
`a<=ell` and the selected-width sum, every tagged branch in `fullBranches`
satisfies Lemma 4's finite two-value count, dispatching to the supplied base
fields or inherited nonbase fields.

This remains a supplied-data theorem only.  It does not infer membership,
admissibility, source labels, or chart construction from the printed equations,
and it does not prove normal crossings or RLCT extraction.

## 2026-06-21 Lean Lemma 5 full supplied family free-count minimum

Reproduction:
`reproduction-lemma5-full-supplied-family-free-count-minimum-a5.md`.
Statement card:
`statement-card-a5-lemma5-full-supplied-family-free-count-minimum.md`.
Review artifact:
`review-lemma5-full-supplied-family-free-count-minimum-a5.md`.

Lean now combines the full supplied branch API with the existing Lemma 4 to
Lemma 3 finite bridge:

```text
AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card_and_fullBranch_twoValueCount
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCount_lemma3A_eq_min
```

The first theorem bundles the supplied full branch count with the per-branch
two-value count.  The second theorem specializes to total increment length
`n+1` and proves that every tagged branch's free high-count parameter attains
the isolated Lemma 3 numerator minimum:

```text
A(n+1,a,b) = a*(n+1)*((n+1)-a).
```

Here `b` counts only the first `n` increments via `j.castSucc`; the final
increment is separated by the existing count-split theorem.

This is still a supplied-data theorem only.  It does not identify the numerator
with a terminal exponent or `lambda`, prove terminal `tilde t=0`, construct
source labels or displayed vectors, prove chart coverage, normal crossings, or
RLCT extraction.

## 2026-06-21 Lean Lemma 5 terminal minimum numerator bridge

Reproduction:
`reproduction-lemma5-terminal-minimum-numerator-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-minimum-numerator-bridge.md`.
Review artifact:
`review-lemma5-terminal-minimum-numerator-bridge-a5.md`.

Lean now connects the supplied Lemma 5 branch minimum to the generic
terminal-exponent certificate API in a new bridge file:

```text
lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```

The new Lean names are:

```text
aoyagiLemma4FreeHighCount
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCountMin
IntroducedLabelExponentCertificates.terminalExponent_eq_suppliedLemma5MinNumerator
```

The theorem remains conditional on a supplied numerator normalisation
`numerator s k = A(n+1,a,b_x)`.  It then combines the exponent certificate
equality `terminalExponent = numerator` with the supplied-branch Lemma 3
minimum theorem to prove

```text
terminalExponent L (widthZ width) (t s k)
  = a*(n+1)*((n+1)-a).
```

This does not prove terminal `tilde t=0`, derive the terminal-exponent
quadratic rewrite from the PDF, construct source labels or displayed vectors,
identify `lambda`, prove chart coverage, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 supplied terminal candidate family

Reproduction:
`reproduction-lemma5-supplied-terminal-candidate-family-a5.md`.
Statement card:
`statement-card-a5-lemma5-supplied-terminal-candidate-family.md`.
Review artifact:
`review-lemma5-supplied-terminal-candidate-family-a5.md`.

Lean now packages branchwise supplied terminal-candidate data in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily
AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches
AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card
AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalLeastValue_zero
AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalExponent_eq_minNumerator
AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalCandidateData
```

The structure attaches each tagged branch to supplied source-label maps
`branchS`, `branchK`, a supplied introduced-label proof, a supplied terminal
least-value-zero proof, and a supplied numerator normalisation to the Lemma 3
free-count expression.  The package then proves each tagged branch is
introduced, terminal in the least-value-zero sense, and has terminal exponent
equal to the isolated Lemma 3 minimum numerator.

This still does not construct labels from Aoyagi's printed equations, prove
terminal `tilde t=0` from the chart process, prove label injectivity or absence
of extra terminal minimizers, identify `lambda`, prove pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 branch-label image count

Reproduction:
`reproduction-lemma5-branch-label-image-count-a5.md`.
Statement card:
`statement-card-a5-lemma5-branch-label-image-count.md`.
Review artifact:
`review-lemma5-branch-label-image-count-a5.md`.

Lean now separates the tagged supplied branch count from the distinct supplied
source-label image count in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_mem_introducedLabelFinset
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_subset_introducedLabelFinset
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_eq_fullBranches_card_of_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_terminalCandidateData
```

The image count is conditional on an explicit hypothesis that `branchLabel` is
injective on `fullBranches`.  Under that hypothesis, the finite image has the
same cardinality as `fullBranches`, hence cardinality `a*(n+1-a)+1`.  Every
branch label belongs to `introducedLabelFinset`, the image is contained in
that finite introduced-label set, and every label in the image inherits the
branchwise introduced-label, least-value-zero, and terminal-exponent-minimum
data by unpacking image membership.

This is still not a pole-order theorem.  It does not prove source-backed label
injectivity, coverage of all terminal minimizers, absence of extra terminal
minimizers, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 terminal minimum label count

Reproduction:
`reproduction-lemma5-terminal-minimum-label-count-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-minimum-label-count.md`.
Review artifact:
`review-lemma5-terminal-minimum-label-count-a5.md`.

Lean now defines the finite exact-minimum label set inside
`introducedLabelFinset`:

```text
aoyagiLemma5MinNumerator
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels
AoyagiLemma5SuppliedTerminalCandidateFamily.mem_terminalMinimumLabels
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_subset_terminalMinimumLabels
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_noExtra
```

The set `terminalMinimumLabels` consists of introduced labels with
`leastValue=0` and terminal exponent equal to
`aoyagiLemma5MinNumerator n a = a*(n+1)*((n+1)-a)`.  Lean proves the supplied
branch-label image is contained in this set.  If the reverse containment is
supplied as the no-extra-minimizer boundary, and `branchLabel` is injective on
`fullBranches`, Lean proves

```text
terminalMinimumLabels.card = a*(n+1-a)+1.
```

This is still not a pole-order theorem.  It does not prove source-backed
no-extra-minimizer coverage, source-backed label injectivity, normal crossings,
or RLCT extraction.

## 2026-06-21 Lean Lemma 5 terminal minimum label exactness package

Reproduction:
`reproduction-lemma5-terminal-minimum-label-exactness-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-minimum-label-exactness.md`.
Review artifact:
`review-lemma5-terminal-minimum-label-exactness-a5.md`.

Lean now packages the two supplied exactness hypotheses used by
`terminalMinimumLabels_card_of_noExtra`:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumLabelExactness
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_exactness
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_exactness
```

The exactness structure contains branch-label injectivity on `fullBranches`
and the no-extra containment
`terminalMinimumLabels subset branchLabelImage`.  The wrapper theorem derives
the finset equality `terminalMinimumLabels = branchLabelImage` and the same
finite minimum-label count

```text
terminalMinimumLabels.card = a*(n+1-a)+1.
```

This is a convenience package for downstream finite handoff.  It does not
prove exactness from Aoyagi's printed equations and does not define or invoke a
normal-crossing-to-RLCT extraction theorem.

## 2026-06-21 Source audit for Lemma 5 terminal exactness

Source audit:
`reproduction-lemma5-terminal-exactness-source-audit-a5.md`.
Boundary card:
`statement-card-a5-lemma5-terminal-exactness-source-frontier.md`.
Review artifact:
`review-lemma5-terminal-exactness-frontier-and-bijon-a5.md`.

The exactness package exposed the no-extra field

```text
terminalMinimumLabels subset branchLabelImage.
```

A source pass over Aoyagi Lemma 5's upper-bound paragraph shows that the
promising source-backed direction is an upper classifier from terminal
lambda-vectors to the counted interval data.  The PDF asserts the
interval-count upper bound and invokes the Case 1(2) fact that `J` increases
by one, but this assertion has not yet been reproduced as a source-backed
classifier.  It does not yet supply the Lean bridge from
`terminalMinimumLabels` to those lambda-vectors or from counted interval data
back to `branchLabelImage`.

The current source obligations are:

```text
label-to-vector bridge
minimum-to-lambda bridge
interval classifier
Case 1(2) uniqueness / injection
back-to-label bridge
```

Until those are reproduced or explicitly supplied, terminal exactness remains
supplied finite data.  This audit does not change the Lean theorem status.

## 2026-06-21 Lean terminal minimum label bijection API

Reproduction:
`reproduction-lemma5-terminal-minimum-label-bijon-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-minimum-label-bijon.md`.
Review artifact:
`review-lemma5-terminal-exactness-frontier-and-bijon-a5.md`.

Lean now exposes the supplied terminal-exactness boundary in standard
`Set.BijOn` form:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_exactness
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_branchLabel_bijOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_branchLabel_bijOn
```

Exactness implies a bijection from supplied `fullBranches` to
`terminalMinimumLabels`; conversely a supplied bijection gives the exactness
fields.  The cardinality wrapper counts terminal minimum labels from such a
supplied bijection and `a<=n+1`.

This is only finite API packaging.  It does not prove the bijection from
Aoyagi's source equations, branch-label injectivity, no-extra containment,
normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 upper-bound classifier interface

Reproduction:
`reproduction-lemma5-upper-bound-classifier-interface-a5.md`.
Statement card:
`statement-card-a5-lemma5-upper-bound-classifier-interface.md`.
Review artifact:
`review-lemma5-upper-bound-classifier-interface-a5.md`.

Lean now names the no-extra direction as a supplied upper-bound classifier:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.UpperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_subset_branchLabelImage_of_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_branchLabelImage_card_of_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_upperBoundClassifier
```

`UpperBoundClassifier C` says that every label in `C.terminalMinimumLabels`
comes from some supplied branch label.  Lean derives the containment
`terminalMinimumLabels subset branchLabelImage`, the upper cardinal inequality
`terminalMinimumLabels.card <= a*(n+1-a)+1` under `a<=n+1` alone, and the
existing exactness package when branch-label injectivity is also supplied.

This does not prove the classifier from Aoyagi's PDF.  It leaves open the
label-to-vector bridge, minimum-to-lambda bridge, interval classifier, Case
1(2) uniqueness/injection, back-to-label bridge, pole order, normal crossings,
and RLCT extraction.

## 2026-06-21 Lean Lemma 5 counted datum set

Reproduction:
`reproduction-lemma5-counted-datum-set-a5.md`.
Statement card:
`statement-card-a5-lemma5-counted-datum-set.md`.
Review artifact:
`review-lemma5-counted-datum-set-a5.md`.

Lean now defines a label-free finite codomain for Aoyagi Lemma 5's
upper-bound interval count:

```text
AoyagiLemma5CountDatum
aoyagiLemma5CountDatumNonbaseSet
aoyagiLemma5CountDatumSet
none_mem_aoyagiLemma5CountDatumSet
some_mem_aoyagiLemma5CountDatumSet_iff
aoyagiLemma5CountDatumNonbaseSet_card
aoyagiLemma5CountDatumSet_card
```

The datum set consists of one base datum and tagged pairs `(j,H)` for
interior `j=1,...,ell-1`, with `H` in the same-coordinate interval value set
after erasing a supplied base value for that coordinate.  If every erased base
value lies in its interval, Lean proves the cardinality is
`a*(ell-a)+1`.

This only counts the codomain suggested by Aoyagi's upper-bound paragraph.  It
does not prove that source lambda-vectors classify into the set, does not
construct supplied branches, does not prove Case 1(2) uniqueness or
back-to-label coverage, and does not touch terminal labels, pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 counted datum classifier boundary

Reproduction:
`reproduction-lemma5-counted-datum-classifier-a5.md`.
Statement card:
`statement-card-a5-lemma5-counted-datum-classifier.md`.
Review artifact:
`review-lemma5-counted-datum-classifier-a5.md`.

Lean now packages the source-facing upper-bound classifier as supplied finite
data:

```text
AoyagiLemma5CountDatumClassifier
AoyagiLemma5CountDatumClassifier.image_subset_countDatumSet
AoyagiLemma5CountDatumClassifier.candidates_card_le
```

For an abstract finite candidate set, the classifier supplies a map into the
counted datum set, proof that the map lands in the set, and injectivity on the
candidate set.  Lean then proves the upper bound
`candidates.card <= a*(ell-a)+1`.

This is the honest source frontier for Aoyagi's Lemma 5 upper-bound paragraph.
It does not construct the candidate set, classify source vectors, prove the
Case 1(2) nonduplication sentence, prove back-to-label coverage, or connect to
terminal labels, pole order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 prefix-delta chain bounds

Reproduction:
`reproduction-lemma5-prefix-delta-chain-bounds-a5.md`.
Statement card:
`statement-card-a5-lemma5-prefix-delta-chain-bounds.md`.
Review artifact:
`review-lemma5-prefix-delta-chain-bounds-a5.md`.

Lean now proves the algebraic bridge from supplied prefix-delta bounds to
displayed `Htilde` chain bounds:

```text
aoyagiHtildeChainBounds_of_incrementPrefix_bounds
aoyagiHtilde_interval_mem_of_incrementPrefix_bounds
```

The first theorem says that if the prefix delta
`D_j = P_j - H_j - j*(M-1)` lies between the upper-chain high count
`min(a, j-(ell-a))` and the lower-chain high count `min(j,a)`, then
`Htilde <= H <= Htilde'`.  The second theorem adds `a<=ell` and converts those
chain bounds to membership in the same-coordinate interval value set.

This does not prove the prefix-delta bounds from binary increments or source
vectors.  It is only the algebraic landing point for the next binary-prefix
count step.

## 2026-06-21 Lean Lemma 5 binary prefix-delta bounds

Reproduction:
`reproduction-lemma5-binary-prefix-delta-bounds-a5.md`.
Statement card:
`statement-card-a5-lemma5-binary-prefix-delta-bounds.md`.
Review artifact:
`review-lemma5-binary-prefix-delta-bounds-a5.md`.

Lean now proves the elementary finite binary-prefix bounds and feeds them into
the existing `Htilde` interval API:

```text
aoyagiIntegerPrefix_binaryDelta_bounds
aoyagiLemma4IncrementPrefix_bounds_of_terminalH_binaryIncrementPrefixDelta
aoyagiHtildeChainBounds_of_terminalH_binaryIncrementPrefixDelta
aoyagiHtilde_interval_mem_of_terminalH_binaryIncrementPrefixDelta
```

For a prefix sequence with binary successive deltas, `D_0=0`, and
`D_ell=a`, Lean proves

```text
min(a, j-(ell-a)) <= D_j <= min(j,a)
```

with natural-number truncated subtraction.  The Aoyagi wrapper uses
`H_0=m_0`, terminal `H_ell=0`, and the selected-width sum to identify
`D_0=0` and `D_ell=a`; a supplied binary-delta hypothesis then yields the
displayed same-coordinate bounds `Htilde <= H <= Htilde'` and interval
membership.

This remains conditional finite arithmetic.  It does not prove that source
exponent vectors have binary prefix deltas, does not prove the source
`T -> (H_j),(S_j)` coordinate correspondence, and does not prove the Lemma 5
upper-bound classifier, Case 1(2) uniqueness, back-to-label coverage, pole
order, normal crossings, or RLCT extraction.

## 2026-06-21 Source probe - Lemma 5 classifier fields

Source probe:
`source-probe-lemma5-classifier-fields-a5.md`.

Ptolemy rechecked Aoyagi PDF pp. 25-27 against the open Lemma 5
upper-bound/no-extra classifier fields.  Verdict: the full classifier is not
proved by the printed paragraph.  The interval count plus the Case 1(2)
sentence that `J` increases by one does not supply a classifier, an injection,
or a back-to-label map.

Status by field:

```text
label-to-vector              conditional
minimum-to-lambda            conditional/obstructed from pp. 25-27 alone
interval classifier          mapsTo only, under explicit source-chain hypotheses
Case 1(2) uniqueness         obstructed
back-to-label                obstructed as printed
```

The recommended next formal direction is a narrow conditional interval
`mapsTo` theorem from terminal/binary chain data to the counted interval
codomain, not a full no-extra classifier.

## 2026-06-21 API probe - coordinate coverage classifier

API probe:
`api-probe-lemma5-coordinate-coverage-classifier-a5.md`.

Lovelace inspected the existing `Lemma5DisplayedVector`,
`Lemma5SuppliedFamily`, and `Lemma5TerminalBridge` APIs.  Recommended next
Lean slice: in `Lemma5SuppliedFamily.lean`, add a generic constructor from
coordinate-wise raw value coverage to `AoyagiLemma5SuppliedNonbaseFamily` by
filtering out the supplied base value, plus a counted-datum classifier bridge
from a supplied coordinate function on branches.

The probe also records the boundary: the equation `(3)`/`(4)`/`(5)` coverage
currently available in `Lemma5DisplayedVector.lean` is one-coordinate and
rising-region only.  It can feed coordinate-wise value-image hypotheses, but
it cannot construct full coverage for all `j=1,...,ell-1` without additional
supplied plateau/falling-coordinate data.

## 2026-06-21 Lean Lemma 5 binary supplied family

Reproduction:
`reproduction-lemma5-binary-supplied-family-a5.md`.
Statement card:
`statement-card-a5-lemma5-binary-supplied-family.md`.
Review artifact:
`review-lemma5-binary-supplied-family-a5.md`.

Lean now packages a narrower supplied-data boundary for Lemma 5 branch
families:

```text
AoyagiLemma5SuppliedBinaryNonbaseFamily
AoyagiLemma5SuppliedBinaryNonbaseFamily.toAdmissibleNonbaseFamily
AoyagiLemma5SuppliedBinaryFamily
AoyagiLemma5SuppliedBinaryFamily.fullBranches
AoyagiLemma5SuppliedBinaryFamily.fullH
AoyagiLemma5SuppliedBinaryFamily.toAdmissibleFamily
AoyagiLemma5SuppliedBinaryFamily.fullBranches_card_and_fullBranch_twoValueCount
```

Instead of directly supplying `Htilde <= H <= Htilde'` and the two-value
increment field for each branch, the binary structures supply `H_0=m_0`,
terminal `H_ell=0`, and binary prefix deltas.  Under `a<=ell` and the
selected-width sum, the conversion theorems derive the previous admissible
family boundary from the binary-prefix arithmetic.

This remains supplied-data assembly.  It does not construct Aoyagi's displayed
source vectors, prove binary deltas from source, prove source-label legality,
prove terminal `tilde t=0`, prove chart coverage, construct the Lemma 5
upper-bound classifier, prove pole order, prove normal crossings, or extract
RLCT data.

## 2026-06-21 Lean Lemma 5 coordinate coverage classifier

Reproduction:
`reproduction-lemma5-coordinate-coverage-classifier-a5.md`.
Statement card:
`statement-card-a5-lemma5-coordinate-coverage-classifier.md`.
Review artifact:
`review-lemma5-coordinate-coverage-classifier-a5.md`.

Lean now packages the next coordinate-coverage boundary in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`:

```text
finset_image_filter_value_ne_eq_erase_image
AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage
AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord
AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord
```

The constructor turns coordinate-wise raw value coverage into
`AoyagiLemma5SuppliedNonbaseFamily` by filtering out branches whose value is
the supplied base value.  The classifier bridge then maps `none` to the base
datum and a nonbase branch `b` to `(branchCoord b, F.value b)`, proving the
`mapsTo` field of `AoyagiLemma5CountDatumClassifier`.

This proves only finite supplied-data assembly.  Coordinate-wise coverage,
branch-coordinate correctness, and tagged-classifier injectivity remain
explicit hypotheses.  The source construction of Aoyagi's displayed family,
Case 1(2) nonduplication, back-to-label coverage, pole order, normal
crossings, and RLCT extraction remain open.

## 2026-06-21 Lean Lemma 5 counted datum injection

Reproduction:
`reproduction-lemma5-counted-datum-injection-a5.md`.
Statement card:
`statement-card-a5-lemma5-counted-datum-injection.md`.
Review artifact:
`review-lemma5-counted-datum-injection-a5.md`.

Lean now proves that the tagged counted-datum map is injective on a supplied
nonbase family once the branch-coordinate map is correct:

```text
AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord_injOn
AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord_of_branchCoord_eq
AoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumOfBranchCoord
AoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumClassifierOfBranchCoord
AoyagiLemma5SuppliedBinaryFamily.countDatumOfBranchCoord
AoyagiLemma5SuppliedBinaryFamily.countDatumClassifierOfBranchCoord
```

The proof uses only existing supplied family fields: membership in
`F.fullBranches` gives coordinate branch sets for two nonbase branches, the
counted datum equality gives equal supplied coordinates and values, and
per-coordinate injectivity of `F.value` gives equality of branches.  The binary
nonbase and full-family wrappers reuse the same underlying nonbase-family
proof.

This does not prove the supplied family fields from source.  In particular,
source value-injectivity, branch-coordinate correctness, and branch
coverage remain the real Aoyagi Lemma 5 construction frontier.

## 2026-06-21 Lean Lemma 5 Eq5 non-rising coverage

Reproduction:
`reproduction-lemma5-eq5-nonrising-coverage-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-nonrising-coverage.md`.
Review artifact:
`review-lemma5-eq5-nonrising-coverage-a5.md`.

Lean now proves the complementary finite-set coverage statement for equation
`(5)` offsets outside the strictly rising interval region:

```text
aoyagiLemma5Eq5_upperEndpoint_not_mem_offsetValueSet
aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred
aoyagiLemma5_suppliedUpper_Eq5_offsets_eq_intervalValueSetNat_of_excess_le_pred
aoyagiLemma5_suppliedEq3Upper_Eq5_offsets_eq_intervalValueSetNat_of_plateau
aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_plateau
```

If the interval excess at coordinate `p` satisfies `excess <= p-1`, then the
strict Eq5 offset set is exactly the same-coordinate interval with the upper
endpoint removed.  A separately supplied upper endpoint fills the interval.
In the plateau subcase `a<p<=ell-a`, a supplied Eq3-shaped component supplies
that upper endpoint value.

This is still finite set bookkeeping.  It does not prove Eq3/Eq5 source-label
legality, terminal `tilde t=0`, chart coverage, an all-coordinate branch
family, pole order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 endpoint deficit

Reproduction:
`reproduction-lemma5-eq5-endpoint-deficit-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-deficit.md`.
Review artifact:
`review-lemma5-eq5-endpoint-deficit-a5.md`.

Lean now packages the finite endpoint deficit of Eq5 strict offsets:

```text
aoyagiLemma5IntervalExcess_eq_self_iff_le_min
aoyagiLemma5IntervalExcess_le_pred_of_not_le_min
aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit
aoyagiLemma5Eq5_offsets_endpointDeficit_split
```

The interval excess equals the coordinate index exactly in the rising region
`p<=a` and `p<=ell-a`; outside that region, for `1<=p`, the excess is at most
`p-1`.  Consequently the interval cardinality is the Eq5 offset cardinality
plus one upper-endpoint deficit, plus one additional lower-endpoint deficit
exactly in the rising region.  The set-level split packages this as either
`Eq5Offsets = Interval.erase upper` or, in the rising region,
`Eq5Offsets = (Interval.erase upper).erase lower`.

This is an obligation split for endpoint realisation.  It does not construct
any source branch, prove source-label legality, prove terminality, prove chart
coverage, or prove the Lemma 5 order count.

## 2026-06-21 Lean Lemma 5 Eq5 supplied endpoint coverage

Reproduction:
`reproduction-lemma5-eq5-supplied-endpoint-coverage-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-supplied-endpoint-coverage.md`.
Review artifact:
`review-lemma5-eq5-supplied-endpoint-coverage-a5.md`.

Lean now turns the Eq5 endpoint-deficit split into a supplied endpoint coverage
split:

```text
aoyagiLemma5_suppliedUpperLower_Eq5_offsets_eq_intervalValueSetNat_of_le_min
aoyagiLemma5_suppliedEndpointCoverage_Eq5_offsets_split
```

In the rising region, supplied upper and lower endpoint values together with
the strict Eq5 offsets fill the same-coordinate interval.  For any positive
coordinate, the split theorem proves either that a supplied upper endpoint plus
Eq5 offsets fills the interval, or that we are in the rising region and a
supplied upper plus supplied lower endpoint plus Eq5 offsets fills it.

This is still supplied endpoint bookkeeping.  It does not prove Eq3, Eq4, or
Eq5 legally supplies the endpoint values, and it does not prove terminality,
chart coverage, branch-family coverage, pole order, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 Eq3 tail upper Eq5 coverage

Reproduction:
`reproduction-lemma5-eq3-tail-upper-eq5-coverage-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-tail-upper-eq5-coverage.md`.
Review artifact:
`review-lemma5-eq3-tail-upper-eq5-coverage-a5.md`.

Lean now records an ordinary-tail Eq3 upper endpoint instantiation:

```text
aoyagiLemma5Eq3_piecewise_tail_upperEndpoint_of_boundary_lt
aoyagiLemma5_suppliedEq3TailUpper_Eq5_offsets_eq_intervalValueSetNat_of_boundary_lt
```

If `ell-a+1 < p` and `p < ell`, then the selected-block left endpoint
`C.point p-1` is strictly after Eq3's special boundary and still inside
ordinary selected block `p`.  The supplied Eq3 tail clause therefore gives the
component value `Htilde'_p`.  Since this coordinate is outside the rising
region, Eq5 offsets miss only the upper endpoint, so inserting the Eq3 tail
component fills the same-coordinate interval.

This deliberately excludes the special boundary `p=ell-a+1` and terminal
endpoint `p=ell`.  It is component-value and finite-set bookkeeping only: no
own-source-label status, Eq3 source-label legality, introduced-label status,
displayed-vector construction, all-coordinate branch-family coverage, pole
order, normal crossings, or RLCT extraction is claimed.

## 2026-06-21 Lean Lemma 5 Eq3 upper away from boundary

Reproduction:
`reproduction-lemma5-eq3-upper-away-from-boundary-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-upper-away-from-boundary.md`.
Review artifact:
`review-lemma5-eq3-upper-away-from-boundary-a5.md`.

Lean now packages Eq3's upper component value away from the special boundary:

```text
aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_ne_boundary
aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_nonrising_ne_boundary
```

For `1<=p`, `p<ell`, and `p!=ell-a+1`, the proof splits on `p<=ell-a`.
On the left side, Eq3's ordinary upper clause gives the component value
`Htilde'_p`; on the right side, `p!=ell-a+1` upgrades `ell-a<p` to
`ell-a+1<p`, so the ordinary-tail clause gives the same component value.

With the additional non-rising hypothesis, Eq5 offsets miss only the upper
endpoint, so inserting this Eq3 component fills the same-coordinate interval.
This is a source-inventory/finite-set wrapper only.  The special boundary
`p=ell-a+1`, terminal endpoint `p=ell`, source-label legality,
own-source-label status, all-coordinate endpoint realisation, injection,
back-to-label coverage, pole order, normal crossings, and RLCT extraction
remain outside this claim.

## 2026-06-21 Lean Lemma 5 Eq3 boundary Eq5 obstruction

Reproduction:
`reproduction-lemma5-eq3-boundary-eq5-obstruction-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-boundary-eq5-obstruction.md`.
Review artifact:
`review-lemma5-eq3-boundary-eq5-obstruction-a5.md`.

Lean now packages the obstruction at Eq3's special boundary:

```text
aoyagiLemma5Eq3_boundaryValue_ne_upperEndpoint
aoyagiLemma5Eq3_boundaryValue_not_mem_Eq5_offsets
aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat
aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat_of_eq_boundary
```

At `p=ell-a+1`, the supplied Eq3 boundary clause gives
`T(C.point p-1)=Htilde'_p+1`, so the component is not the same-coordinate upper
endpoint and lies outside the interval.  Since Eq5 strict offsets are contained
in that interval, the boundary value is not an Eq5 offset; inserting it into
the Eq5 offset set cannot produce the interval.

This is an endpoint-inventory obstruction, not coverage.  It does not prove
source-label legality, own-source-label status, all-coordinate endpoint
realisation, injection, back-to-label coverage, pole order, normal crossings,
or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq4 rising-boundary gap

Reproduction:
`reproduction-lemma5-eq4-rising-boundary-gap-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-rising-boundary-gap.md`.
Review artifact:
`review-lemma5-eq4-rising-boundary-gap-a5.md`.

Lean now packages the Eq4 lower-endpoint gap at the rising boundary:

```text
aoyagiLemma5Eq4_no_piecewiseSourceVector_of_not_indexGuard
aoyagiLemma5Eq4_no_piecewiseSourceVector_of_eq_a
aoyagiLemma5Eq5_risingBoundary_eq_a_noEq4LowerEndpoint
```

The Eq4 source-shaped certificate carries the repaired guard `p+1<=a`, so at
`p=a` it would require `a+1<=a`, impossible.  Under `a<=ell`, `1<=a`, and
`a<=ell-a`, the same coordinate is still in Eq5's rising region, so Eq5
strict offsets are the same-coordinate interval with both endpoints erased.

This is a gap record, not a lower-endpoint replacement.  It does not prove
Eq4 source-label legality, construction of Eq4/Eq5 vectors, all-coordinate
endpoint realisation, injection, back-to-label coverage, pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 terminal Eq5 gap

Reproduction:
`reproduction-lemma5-terminal-eq5-gap-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-eq5-gap.md`.
Review artifact:
`review-lemma5-terminal-eq5-gap-a5.md`.

Lean now packages the terminal endpoint finite-set inventory:

```text
aoyagiLemma5Eq5OffsetValueSet_eq_empty_of_terminal
aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum
aoyagiLemma5Eq5_terminal_offsets_ne_intervalValueSetNat_of_selectedSum
aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat
aoyagiLemma5_suppliedTerminalUpper_Eq5_offsets_eq_intervalValueSetNat
```

At `p=ell`, Eq5's strict-offset set is empty because the interval excess has
the terminal factor `ell-ell=0`.  Under the selected-width sum and `a<=ell`,
the lower and upper Htilde terminal values are both zero, so the terminal
same-coordinate interval is `{0}`.  Thus Eq5 offsets alone do not fill the
terminal interval, while a separately supplied terminal zero does.  The
terminal-upper wrapper records the same coverage when the supplied equality is
written as `T(C.point ell-1)=Htilde'_ell`.

This is supplied endpoint bookkeeping, not source construction.  It does not
prove terminal source-label legality, terminal-label exactness,
all-coordinate endpoint realisation, injection, back-to-label coverage, pole
order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 supplied family terminal chain zero

Reproduction:
`reproduction-lemma5-supplied-family-terminal-chain-zero-a5.md`.
Statement card:
`statement-card-a5-lemma5-supplied-family-terminal-chain-zero.md`.
Review artifact:
`review-lemma5-supplied-family-terminal-chain-zero-a5.md`.

Lean now packages terminal chain value zero for supplied Lemma 5 branch
families:

```text
AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_terminalH_zero
AoyagiLemma5SuppliedAdmissibleFamily.base_terminalH_zero
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalH_zero
AoyagiLemma5SuppliedBinaryNonbaseFamily.branch_terminalH_zero
AoyagiLemma5SuppliedBinaryFamily.base_terminalH_zero
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalH_zero
```

For admissible families this is a direct application of the existing
`Htilde` terminal squeeze under `a<=ell` and the selected-width sum.  For
binary families it is a direct dispatch to the supplied `Hlast` and
`baseHlast` fields.

This is chain-coordinate endpoint bookkeeping only.  It does not construct a
terminal/base source branch, and it does not prove the source-coordinate
terminal equality `T(C.point ell-1)=0` needed by the terminal Eq5 finite-set
wrapper.  Source-label legality, terminal-label exactness, classifier
coverage, injection, back-to-label coverage, pole order, normal crossings, and
RLCT extraction remain outside this claim.

## 2026-06-21 Lean Lemma 5 Eq4 local lower endpoint

Reproduction:
`reproduction-lemma5-eq4-local-lower-endpoint-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-local-lower-endpoint.md`.
Review artifact:
`review-lemma5-eq4-local-lower-endpoint-a5.md`.

Lean now packages the source-legality-free lower endpoint carried by a supplied
Eq4 piecewise certificate:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_lowerEndpoint_of_le_min
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_piecewise
aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_piecewise
aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_piecewise
aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_eq_intervalValueSetNat
```

The first theorem uses `1<=p`, `p<=ell-a`, and the supplied Eq4 certificate;
the certificate itself carries the repaired guard `p+1<=a`.  It proves only
`T4(C.point p-1)=Htilde_p`.  The finite-set wrappers then fill Eq5's lower
endpoint deficit, and with a separately supplied upper endpoint fill the
same-coordinate interval.

This does not prove source-label legality for `Htilde_p+1`, Eq4 existence at
`p=a`, terminal-collision compatibility in the `p+1=a` case, all-coordinate
branch-family coverage, injection, back-to-label coverage, pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 terminal source-realisation bridge

Reproduction:
`reproduction-lemma5-terminal-source-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-source-bridge.md`.
Review artifact:
`review-lemma5-terminal-source-bridge-a5.md`.

Lean now packages the exact handoff from supplied branch terminal chain zero
to terminal Eq5 source-coordinate coverage:

```text
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_Eq5Coverage
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_Eq5Coverage
```

Both theorems require an explicit hypothesis
`T(C.point ell-1)=fullH x (Fin.last ell)`.  With that equality, the supplied
family terminal chain-zero theorem gives `T(C.point ell-1)=0`, and the existing
terminal Eq5 supplied-zero wrapper fills the terminal singleton interval.

This does not construct the source-realisation equality, a terminal/base
source branch, source-label legality, terminal-label exactness, classifier
coverage, injection, back-to-label coverage, pole order, normal crossings, or
RLCT extraction.

## 2026-06-21 Lean Lemma 5 terminal binary counted-datum maps-to

Reproduction:
`reproduction-lemma5-terminal-binary-counted-datum-maps-to-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-binary-counted-datum-maps-to.md`.
Review artifact:
`review-lemma5-classifier-boundary-a5.md`.

Lean now proves the one-branch counted-datum codomain membership theorem:

```text
aoyagiLemma5CountDatumSet_mem_of_terminalH_binaryIncrementPrefixDelta
```

For an interior coordinate `j`, a chain `H` with `H_0=m_0`,
`H_ell=0`, selected-width sum, and binary prefix deltas has
`H_j` in the same-coordinate Htilde interval.  If additionally
`H_j != baseValue j`, Lean packages
`some (j,H_j)` as a member of the counted datum set.  This is the `mapsTo`
half for one nonbase branch value only.  It does not construct source
branches, prove coordinate-wise coverage, prove classifier injectivity, or
give a back-to-label map.

## 2026-06-21 Lean Lemma 5 terminal-minimum counted-datum classifier

Reproduction:
`reproduction-lemma5-terminal-minimum-counted-datum-classifier-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-minimum-counted-datum-classifier.md`.
Review artifact:
`review-lemma5-classifier-boundary-a5.md`.

Lean now separates the source-facing upper-bound classifier from branch-label
exactness:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumClassifier
```

The classifier is supplied data from `terminalMinimumLabels` into
`aoyagiLemma5CountDatumSet (n+1) a M m C.family.baseValue`.  If such an
injective classifier is supplied, the existing counted-datum codomain count
gives

```text
C.terminalMinimumLabels.card <= a * (n + 1 - a) + 1.
```

This is only an upper-bound wrapper.  It does not prove the classifier from
Aoyagi's PDF, does not identify `terminalMinimumLabels` with `branchLabelImage`,
and does not prove source-label legality, injection, back-to-label coverage,
pole order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 upper-bound classifier equivalence

Reproduction:
`reproduction-lemma5-upper-bound-classifier-interface-a5.md`.
Statement card:
`statement-card-a5-lemma5-upper-bound-classifier-interface.md`.
Review artifact:
`review-lemma5-upper-bound-classifier-equivalence-a5.md`.

Lean now proves the reverse finite-set direction for the supplied upper-bound
classifier:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_terminalMinimumLabels_subset_branchLabelImage
AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_iff_terminalMinimumLabels_subset_branchLabelImage
```

The first theorem unpacks membership in `branchLabelImage` to recover the
classifier witness `x in fullBranches` with `branchLabel x = label`.  The
second theorem records that `UpperBoundClassifier` is exactly the no-extra
inclusion `terminalMinimumLabels ⊆ branchLabelImage`.  This is finite
bookkeeping for the supplied boundary only.  It does not prove that inclusion
from Aoyagi's source, nor source-label legality, injection, back-to-label
coverage, pole order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 counted-datum back-to-branch-label boundary

Reproduction:
`reproduction-lemma5-counted-datum-back-to-branch-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-counted-datum-back-to-branch-label.md`.
Review artifact:
`review-lemma5-counted-datum-back-to-branch-label-a5.md`.

Lean now records the next supplied boundary between the counted-datum
classifier and the branch-label no-extra classifier:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchCountDatumOfCoord
AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumBackToBranchLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_countDatumBackToBranchLabel
```

The bridge says that, for every terminal-minimum label, the datum assigned by
the supplied counted-datum classifier is realised by a supplied full branch
with the same `branchLabel`.  The resulting theorem derives the existing
`UpperBoundClassifier`; the proof uses only the supplied branch-label witness,
while retaining the counted-datum equality as the intended route through
Aoyagi's interval-count paragraph.

This is supplied finite data, not a source reconstruction.  It does not
construct the counted-datum classifier, branch-coordinate map, or
back-to-label bridge from Aoyagi's displayed equations, and it does not prove
source-label legality, injection, pole order, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 terminal source label

Reproduction:
`reproduction-lemma5-terminal-source-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-source-label.md`.
Review artifact:
`review-lemma5-terminal-source-label-a5.md`.

Lean now isolates source-label legality for the terminal singleton:

```text
aoyagiLemma5_terminalSourceIndex_pos
aoyagiLemma5_terminal_actualWidthLabel_of_lastPoint
aoyagiLemma5_terminal_intervalValue_mem_introducedLabelFinset_of_terminalZero
```

Under `1<=ell`, `C.point ell<=L+1`, and `1<=n(C.point ell)`, the terminal
source coordinate `C.point ell-1` is a legal source layer and `k=1` is a legal
actual-width label.  If the terminal source-coordinate value is separately
supplied as `T(C.point ell-1)=0`, then this value lies in the terminal
same-coordinate interval, equals `1-1`, and the label
`(C.point ell-1,1)` belongs to `introducedLabelFinset L n (C.point ell-1) 1`.

This is terminal source-label bookkeeping only.  It does not construct the
terminal source branch, prove source-realisation from a supplied branch chain,
prove terminal-label exactness, classifier coverage, branch-label injectivity,
back-to-label coverage, pole order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 post-p lower obstruction

Reproduction:
`reproduction-lemma5-eq5-postp-lower-obstruction-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-postp-lower-obstruction.md`.
Review artifact:
`review-lemma5-eq5-postp-lower-obstruction-a5.md`.

Lean now generalizes the existing all-widths-four Eq5 obstruction:

```text
aoyagiLemma5Eq5_postP_belowLower_of_intervalExcess_lt_offset
```

For a supplied equation `(5)` piecewise certificate, in the post-`p` range
`p<=b<=p+(a-alpha)`, the displayed value is

```text
T S = Htilde'_b - alpha + p - b
    = Htilde'_b - (alpha+b-p).
```

Since `Htilde'_b-Htilde_b` is the interval excess, the theorem proves that if

```text
aoyagiLemma5IntervalExcess ell a b < alpha + b - p,
```

then `T S < Htilde_b`.  This is a lower-bound obstruction for supplied Eq5
post-`p` data.  It does not construct the displayed source vector, prove all
Eq5 branches fail, supply a corrected Eq5 construction, prove source-label
legality, terminality, chart coverage, classifier coverage, pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq4 rising-guard exhaustion

Reproduction:
`reproduction-lemma5-eq4-rising-guard-exhaustion-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-rising-guard-exhaustion.md`.
Review artifact:
`review-lemma5-eq4-rising-guard-exhaustion-a5.md`.

Lean now proves the exact repaired Eq4 guard-failure arithmetic:

```text
aoyagiLemma5Eq4_risingGuardFailure_iff_eq_a
aoyagiLemma5Eq4_selectedIndexGuardFailure_iff_eq_a
```

Under `p<=a`, failure of the repaired guard `p+1<=a` is equivalent to `p=a`.
Under `a<=ell`, the same statement is available for the raw selected-index
guard `p+(ell-a)+2<=ell+1`, using the existing selected-index equivalence.

The displayed-vector wrapper

```text
aoyagiLemma5Eq4_risingGuardFailure_eq_a_and_no_piecewiseSourceVector
```

adds the existing supplied-certificate obstruction: if guard failure occurs in
the rising-side range, then `p=a` and no
`AoyagiLemma5Eq4PiecewiseSourceVector` of the repaired shape exists.  This is
only a guard-failure wrapper.  It does not prove the converse
`not Eq4PiecewiseSourceVector iff p=a`, construct Eq4 branches, fill the Eq5
lower endpoint at `p=a`, prove source-label legality, chart coverage, pole
order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 counted-datum back-to-branch-label card bound

Reproduction:
`reproduction-lemma5-counted-datum-back-to-branch-label-card-a5.md`.
Statement card:
`statement-card-a5-lemma5-counted-datum-back-to-branch-label-card.md`.
Review artifact:
`review-lemma5-counted-datum-back-to-branch-label-card-a5.md`.

Lean now proves the direct numeric upper-bound wrapper:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel
```

From a supplied counted-datum classifier and a supplied back-to-label bridge,
the theorem first obtains the existing `UpperBoundClassifier`, then applies
the existing upper-bound-cardinality theorem to get

```text
C.terminalMinimumLabels.card <= a * (n + 1 - a) + 1.
```

This is only finite bookkeeping from supplied data.  It does not construct the
counted-datum classifier, branch-coordinate map, or back-to-label bridge from
Aoyagi's source, and it does not prove exact cardinality, pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 terminal source realisation iff zero

Reproduction:
`reproduction-lemma5-terminal-source-realisation-iff-zero-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-source-realisation-iff-zero.md`.
Review artifact:
`review-lemma5-terminal-source-realisation-iff-zero-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_realisation_iff_terminalZero
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_realisation_iff_terminalZero
```

For any supplied full-family branch, branch-chain terminal zero rewrites the
terminal source-realisation equality

```text
T(C.point ell - 1) = F.fullH x (Fin.last ell)
```

as the simpler terminal source-zero equality

```text
T(C.point ell - 1) = 0.
```

This is only a reduction of supplied hypotheses.  It does not prove terminal
source zero, construct the terminal source branch, prove terminal-label
exactness, classifier coverage, pole order, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 counted-datum back-to-branch-label exactness

Reproduction:
`reproduction-lemma5-counted-datum-back-to-branch-label-exactness-a5.md`.
Statement card:
`statement-card-a5-lemma5-counted-datum-back-to-branch-label-exactness.md`.
Review artifact:
`review-lemma5-counted-datum-back-to-branch-label-exactness-a5.md`.

Lean now proves the exactness wrappers:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumBackToBranchLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumBackToBranchLabel
```

The first theorem packages a supplied counted-datum back-to-label bridge with
supplied branch-label injectivity to produce `TerminalMinimumLabelExactness`.
The second theorem combines that exactness with the selected-width sum to get

```text
C.terminalMinimumLabels.card = a * (n + 1 - a) + 1.
```

This is supplied finite exactness only.  It does not construct the
counted-datum classifier, branch-coordinate map, back-to-label bridge, or
branch-label injectivity from Aoyagi's source; it is not a pole-order,
normal-crossing, or RLCT theorem.

## 2026-06-21 Lean Lemma 5 terminal source endpoint payload

Reproduction:
`reproduction-lemma5-terminal-source-endpoint-payload-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-source-endpoint-payload.md`.
Review artifact:
`review-lemma5-terminal-source-endpoint-payload-a5.md`.

Lean now packages the terminal endpoint consequences of a realised supplied
full-family branch:

```text
aoyagiLemma5TerminalSourceEndpointPayload
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_terminalEndpointPayload
AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_terminalEndpointPayload
```

The payload combines terminal Eq5 finite-set coverage with terminal
source-label bookkeeping for `(C.point ell-1,1)`.  Both branch-family theorems
keep the source-realisation equality
`T(C.point ell-1)=F.fullH x (Fin.last ell)` explicit, and also require
terminal source range and width positivity for the introduced-label side.

This does not construct the terminal source branch, prove the source
realisation equality, prove terminal exactness, construct a classifier,
prove injection or back-to-label coverage, compute pole order, prove normal
crossings, or extract RLCT.

## 2026-06-21 Lean Lemma 5 Eq4 rising non-strict endpoint split

Reproduction:
`reproduction-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq4-rising-nonstrict-endpoint-split.md`.
Review artifact:
`review-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`.

Lean now packages the non-strict Eq4 endpoint inventory:

```text
aoyagiLemma5Eq4_risingNonStrictEndpoint_iff_predBoundary_or_eq_a
aoyagiLemma5Eq4_boundaryIndex_not_lt_ell_iff_predBoundary_or_eq_a
aoyagiLemma5Eq4_risingNonStrictEndpoint_predBoundary_or_no_piecewiseSourceVector
aoyagiLemma5Eq4TerminalCollisionPayload
aoyagiLemma5Eq4GuardFailurePayload
aoyagiLemma5Eq4_risingNonStrictEndpoint_split
```

Under `p<=a`, failure of the strict endpoint case `p+1<a` splits into
terminal collision `p+1=a` or repaired-guard failure `p=a`.  The
terminal-collision branch only gives consequences for every supplied Eq4
piecewise certificate; it does not prove such a certificate exists.  The
`p=a` branch records the existing Eq5 erased-endpoints deficit and absence of
the repaired Eq4 piecewise shape.

This does not construct displayed vectors, prove source coverage, fill the
`p=a` lower endpoint, prove terminal zero in the `p+1=a` branch without
last-width compatibility, prove classifier/injection/back-to-label coverage,
compute pole order, prove normal crossings, or extract RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 alpha-family value image

Reproduction:
`reproduction-lemma5-eq5-alpha-family-value-image-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-alpha-family-value-image.md`.
Review artifact:
`review-lemma5-eq5-alpha-family-value-image-a5.md`.

Lean now names the definitional equality

```text
aoyagiLemma5Eq5_alphaFamily_value_image_eq_offsetValueSet
```

between the strict equation `(5)` alpha-family image

```text
image (alpha |-> Htilde'_p - alpha)
  {alpha | 1 <= alpha <= min(excess(ell,a,p),p-1)}
```

and the existing finite set
`aoyagiLemma5Eq5OffsetValueSet ell a p M m`.

This is finite-set API naming only.  It does not construct equation `(5)`'s
displayed vector, prove source-label legality for `k`, prove selected-span
coverage, terminal `tilde t=0`, chart sequence, Lemma 5 order count, pole
order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 alpha-family source label

Reproduction:
`reproduction-lemma5-eq5-alpha-family-source-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-alpha-family-source-label.md`.
Review artifact:
`review-lemma5-eq5-alpha-family-source-label-a5.md`.

Lean now proves the strict alpha-domain guard equivalence and label adapter:

```text
aoyagiLemma5Eq5_alphaFamily_mem_iff_guards
aoyagiLemma5Eq5_alphaFamily_actualWidthLabel_at_of_widthBound
```

The first theorem rewrites membership in
`1<=alpha<=min(excess(ell,a,p),p-1)` as the three guards
`1<=alpha`, `alpha<=excess(ell,a,p)`, and `alpha<p`.  The second theorem uses
that membership to feed the existing Eq5 actual-label theorem under explicit
source-index bounds, actual-width dominance, selected-width hypotheses, and
the supplied label relation `k=Htilde'_p+1-alpha`.

This is source-label API cleanup only.  It does not construct an Eq5 vector,
prove branch existence, derive the cutoff guard, prove selected-span coverage,
terminal `tilde t=0`, chart sequence, classifier/injection/back-to-label
coverage, Lemma 5 order count, pole order, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 Eq5 alpha-indexed branch value image

Reproduction:
`reproduction-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-alpha-indexed-branch-value-image.md`.
Review artifact:
`review-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`.

Lean now proves the finite branch-image bridge

```text
aoyagiLemma5Eq5_alphaIndexedBranch_value_image_eq_offsetValueSet
```

If a supplied finite branch family has alpha projection exactly
`aoyagiLemma5Eq5AlphaDomain ell a p`, and every branch value is
`Htilde'_p-alphaOf b`, then the branch-value image is exactly
`aoyagiLemma5Eq5OffsetValueSet ell a p M m`.  The slice also names the strict
Eq5 alpha domain as `aoyagiLemma5Eq5AlphaDomain` and rewires the existing
alpha-family value-image and source-label statements through this domain.

This is finite-set image bookkeeping only.  It does not construct branch
records, equation `(5)` displayed vectors, source-label legality, cutoff
guards, selected-span coverage, terminal `tilde t=0`, injection, classifier,
back-to-label coverage, Lemma 5 order count, pole order, normal crossings, or
RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 post-p lower exact guard

Reproduction:
`reproduction-lemma5-eq5-postp-lower-exact-guard-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-postp-lower-exact-guard.md`.
Review artifact:
`review-lemma5-eq5-postp-lower-exact-guard-a5.md`.

Lean now proves the exact local interval-membership guard for the post-`p`
branch of a supplied Eq5 piecewise certificate:

```text
aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_iff_offset_le_intervalExcess
```

For a post-`p` block point, membership in the same-coordinate Htilde interval
is equivalent to

```text
alpha+b-p <= aoyagiLemma5IntervalExcess ell a b.
```

Lean also names the global guard predicate
`aoyagiLemma5Eq5PostPLowerGuard`, proves a sufficient terminal-room condition
`aoyagiLemma5Eq5PostPLowerGuard_of_terminalRoom`, gives positive wrappers,
and records a concrete counterexample showing that strict Eq5 alpha-domain
membership plus the post-`p` range does not imply the lower guard.

This is local finite arithmetic and admissibility bookkeeping only.  It does
not construct Eq5 vectors, prove the lower guard from source hypotheses,
prove source-label legality, cutoff coverage, terminal `tilde t=0`,
classifier/injection/back-to-label coverage, Lemma 5 order count, pole order,
normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 early and tail interval guards

Reproduction:
`reproduction-lemma5-eq5-early-tail-interval-guards-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-early-tail-interval-guards.md`.
Review artifact:
`review-lemma5-eq5-early-tail-interval-guards-a5.md`.

Lean now proves the exact same-coordinate interval guards for the remaining
Eq5 branch clauses:

```text
aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_iff_index_le_intervalExcess
aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_iff_predAlpha_le_intervalExcess
aoyagiLemma5Eq5_tail_mem_intervalValueSetNat
```

The `preAlpha` branch uses offset `b`; the `alphaToP` branch uses offset
`alpha-1`; the `tail` branch is automatically the lower endpoint.  Lean also
names early-branch guard predicates and proves that strict Eq5 alpha-domain
membership supplies them:

```text
aoyagiLemma5Eq5PreAlphaLowerGuard_of_alphaDomain
aoyagiLemma5Eq5AlphaToPLowerGuard_of_alphaDomain
```

This does not repair the post-`p` branch: the post-`p` lower guard remains the
separate condition from the exact-guard slice, and the existing counterexample
shows it is not implied by strict alpha-domain membership plus post-`p` range.
No Eq5 vector construction, source-label legality, terminal `tilde t=0`,
chart coverage, Lemma 5 order count, pole order, normal crossings, or RLCT
extraction follows.

## 2026-06-21 Lean Lemma 5 Eq5 nonfirst block admissibility

Reproduction:
`reproduction-lemma5-eq5-nonfirst-block-admissibility-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-nonfirst-block-admissibility.md`.
Review artifact:
`review-lemma5-eq5-nonfirst-block-admissibility-a5.md`.

Lean now assembles the Eq5 branch-local interval guards into the supplied
nonfirst-block wrapper

```text
aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_postPLowerGuard
```

For a supplied Eq5 piecewise certificate, if `alpha` is in the strict Eq5
alpha domain and the explicit post-`p` lower guard is supplied, then every
block point `C.block b S` with `1<=b` has

```text
T S in aoyagiHtildeIntervalValueSetNat ell a M m b.
```

The `b=0` first branch is intentionally excluded because its value is the
ambient layer width, not an Htilde-chain expression.  This theorem still does
not construct Eq5 source vectors, prove source-label legality, prove the
post-`p` lower guard from source hypotheses, prove terminal `tilde t=0`, chart
coverage, Lemma 5 order count, pole order, normal crossings, or RLCT
extraction.

## 2026-06-21 Lean Lemma 5 Eq5 terminal-room guard

Reproduction:
`reproduction-lemma5-eq5-terminal-room-guard-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-terminal-room-guard.md`.
Review artifact:
`review-lemma5-eq5-terminal-room-guard-a5.md`.

Lean now proves the exact finite-arithmetic characterization

```text
aoyagiLemma5Eq5PostPLowerGuard_iff_terminalRoom_of_alphaDomain
```

Under strict Eq5 alpha-domain membership, the global post-`p` lower guard is
equivalent to

```text
p + 2*a - alpha <= ell.
```

The proof evaluates the global guard at the terminal post-`p` coordinate
`b=p+(a-alpha)` for the reverse direction, and reuses the existing sufficient
terminal-room theorem for the forward direction.  Lean also adds

```text
aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_terminalRoom
```

which replaces the opaque post-`p` guard in the nonfirst-block admissibility
wrapper by this concrete inequality.

This is finite arithmetic for supplied Eq5 piecewise data.  It does not
construct Eq5 source vectors, prove terminal-room from source hypotheses, prove
source-label legality, prove terminal `tilde t=0`, chart coverage, Lemma 5
order count, pole order, normal crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 counted-datum back-to-label bijection

Reproduction:
`reproduction-lemma5-back-to-label-bijon-a5.md`.
Statement card:
`statement-card-a5-lemma5-back-to-label-bijon.md`.
Review artifact:
`review-lemma5-back-to-label-bijon-a5.md`.

Lean now exposes the supplied counted-datum back-to-label boundary as the
standard finite bijection

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumBackToBranchLabel
```

The theorem assumes the counted-datum classifier, the back-to-label bridge,
branch-label injectivity, `a<=n+1`, and the selected-width sum.  It composes
the existing supplied exactness wrapper with the existing
exactness-to-bijection theorem.

This remains supplied finite API.  It does not construct Aoyagi's classifier,
prove Case 1(2) nonduplication, construct the back-to-label map from equations
`(3)`, `(4)`, and `(5)`, prove source-label legality, pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 terminal exactness/bijection equivalence

Reproduction:
`reproduction-lemma5-terminal-exactness-bijon-equivalence-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-exactness-bijon-equivalence.md`.
Review artifact:
`review-lemma5-terminal-exactness-bijon-equivalence-a5.md`.

Lean now packages the two supplied-boundary formulations of terminal-minimum
exactness as an equivalence:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_bijOn
```

The forward direction still needs `a<=n+1` and the selected-width sum to show
that supplied branch labels land in the terminal-minimum label set.  The
reverse direction unpacks the `Set.BijOn` injection and surjection fields into
the existing exactness structure.

This is finite API bookkeeping only.  It does not construct exactness,
classifier data, a back-to-label map, source labels, source branches, pole
order, normal crossings, or RLCT extraction.

## 2026-06-22 Lean Lemma 5 upper-bound classifier exactness wrappers

Reproduction:
`reproduction-lemma5-upper-bound-classifier-exactness-a5.md`.
Statement card:
`statement-card-a5-lemma5-upper-bound-classifier-exactness.md`.
Review artifact:
`review-lemma5-upper-bound-classifier-exactness-a5.md`.

Lean now adds direct wrappers from the supplied upper-bound classifier:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_upperBoundClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_upperBoundClassifier
```

The finite-set calculation is: `UpperBoundClassifier C` is the no-extra
containment from `terminalMinimumLabels` to `branchLabelImage`, while the
existing supplied-candidate theorem gives the reverse containment under
`a<=n+1` and the selected-width sum.  Hence the finite label sets are equal.
Adding supplied branch-label injectivity gives the exactness package,
branch-label bijection, and exact finite count.

This remains supplied finite API.  It does not construct the classifier,
prove branch-label injectivity, build a counted-datum back-to-label map from
Aoyagi's source equations, prove pole order, prove normal crossings, or
extract RLCT.

## 2026-06-22 Lean Lemma 5 counted-datum classifier cardinal squeeze

Reproduction:
`reproduction-lemma5-counted-datum-classifier-cardinal-squeeze-a5.md`.
Statement card:
`statement-card-a5-lemma5-counted-datum-classifier-cardinal-squeeze.md`.
Review artifact:
`review-lemma5-counted-datum-classifier-cardinal-squeeze-a5.md`.

Lean now derives terminal-minimum exactness from a supplied counted-datum
classifier and supplied branch-label injectivity:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_countDatumClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumClassifier_and_branchLabel_injOn
```

The proof uses the finite squeeze `branchLabelImage.card = N`,
`branchLabelImage subset terminalMinimumLabels`, and
`terminalMinimumLabels.card <= N` from the supplied counted-datum classifier.
This avoids an explicit counted-datum back-to-label witness.

The counted-datum classifier and branch-label injectivity remain supplied
data.  This does not construct the classifier from Aoyagi's equations, prove
source-label legality, build the displayed branch family, prove pole order,
prove normal crossings, or extract RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 alpha-indexed branch source labels

Reproduction:
`reproduction-lemma5-eq5-alpha-indexed-branch-source-label-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-alpha-indexed-branch-source-label.md`.
Review artifact:
`review-lemma5-eq5-alpha-indexed-branch-source-label-a5.md`.

Lean now packages the strict Eq5 alpha-domain source-label theorem over a
supplied finite branch family:

```text
aoyagiLemma5Eq5_alphaIndexedBranch_actualWidthLabel_of_widthBound
aoyagiLemma5Eq5_alphaIndexedBranchLabel_mem_actualWidthLabelFinset_of_widthBound
aoyagiLemma5Eq5_alphaIndexedBranchLabel_injOn
```

The first two theorems are branchwise wrappers: if each supplied branch alpha
lies in the strict Eq5 alpha domain, its supplied Sigma label has source
coordinate in range, the selected width is bounded by the actual width at that
source coordinate, and the label is `Htilde'_p+1-alpha`, then the label is an
actual-width label and belongs to `actualWidthLabelFinset`.

The injectivity theorem is also supplied-boundary bookkeeping: if `alphaOf` is
injective on the supplied branch family, then the supplied Sigma-valued
`branchLabel` is injective on that family.  Do not infer this from alpha-domain
coverage alone.

This does not construct Eq5 branch records, prove alpha-domain coverage,
selected-span coverage, displayed-vector construction, terminal exactness,
classifier/back-to-label coverage, Lemma 5 order count, pole order, normal
crossings, or RLCT extraction.

## 2026-06-21 Lean Lemma 5 Eq5 alpha-indexed branch-label image

Reproduction:
`reproduction-lemma5-eq5-alpha-indexed-branch-label-image-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-alpha-indexed-branch-label-image.md`.
Review artifact:
`review-lemma5-eq5-alpha-indexed-branch-label-image-a5.md`.

Lean now packages the supplied alpha-indexed Eq5 branch-label family at image
level:

```text
aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_subset_actualWidthLabelFinset_of_widthBound
aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_of_alphaInj
```

Branchwise actual-width label legality gives
`branches.image branchLabel ⊆ actualWidthLabelFinset L n`, and supplied alpha
injectivity gives `(branches.image branchLabel).card = branches.card`.

This is finite supplied-image bookkeeping only.  It does not construct Eq5
branches, prove alpha-domain coverage, selected-span coverage, displayed
vectors, terminal exactness, classifier/back-to-label coverage, pole order,
normal crossings, or RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 alpha-indexed branch cardinal bound

Reproduction:
`reproduction-lemma5-eq5-alpha-indexed-branch-card-bound-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-alpha-indexed-branch-card-bound.md`.
Review artifact:
`review-lemma5-eq5-alpha-indexed-branch-card-bound-a5.md`.

Lean now packages the supplied alpha-indexed Eq5 branch-label image as
cardinality bounds:

```text
aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_le_actualWidthLabelFinset_card
aoyagiLemma5Eq5_alphaIndexedBranch_card_le_actualWidthLabelFinset_card
```

The image-card theorem uses only the already-proved image subset
`branches.image branchLabel ⊆ actualWidthLabelFinset L n`.  The branch-card
theorem adds supplied alpha injectivity to identify the image cardinality with
the supplied branch-family cardinality.

This is finite supplied-cardinality bookkeeping only.  It does not construct
Eq5 branches, prove alpha-domain coverage, selected-span coverage, displayed
vectors, terminal exactness, classifier/back-to-label coverage, pole order,
normal crossings, or RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 alpha-indexed offset cardinality

Reproduction:
`reproduction-lemma5-eq5-alpha-indexed-offset-card-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-alpha-indexed-offset-card.md`.
Review artifact:
`review-lemma5-eq5-alpha-indexed-offset-card-a5.md`.

Lean now packages supplied alpha-domain coverage for Eq5 strict offsets:

```text
aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_offsetValueSet_card
```

If the supplied alpha projection maps the branch family onto
`aoyagiLemma5Eq5AlphaDomain ell a p` and is injective, then the supplied
branch-label image has the same cardinality as
`aoyagiLemma5Eq5OffsetValueSet ell a p M m`.  This is cardinal equality only:
the branch-label image is Sigma-valued, while the offset-value set is an
integer value set.

This is finite supplied-cardinality bookkeeping only.  It does not construct
Eq5 branches, prove source-label legality or width compatibility, prove
coverage of actual-width or terminal-minimum labels, provide a classifier or
back-to-label map, prove pole order, normal crossings, or RLCT.

## 2026-06-21 Lean Lemma 5 terminal branch introduced-domain capacity

Reproduction:
`reproduction-lemma5-terminal-branch-introduced-domain-capacity-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-branch-introduced-domain-capacity.md`.
Review artifact:
`review-lemma5-terminal-branch-introduced-domain-capacity-a5.md`.

Lean now packages the supplied terminal-branch labels as finite capacity
statements inside the current introduced-label domain:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_introducedLabelFinset_card
AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_introducedLabelFinset_card_of_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_introducedLabelFinset_card_of_branchLabel_injOn
```

The first theorem is the cardinality form of the existing
`branchLabelImage_subset_introducedLabelFinset`.  The latter two add supplied
branch-label injectivity and the supplied family count to show
`a*(n+1-a)+1 <= (introducedLabelFinset L width S J).card`.

This is only a conditional capacity statement.  It does not construct terminal
branch labels, prove branch-label injectivity, prove no-extra terminal-minimum
coverage, compute terminal-minimum cardinality, prove pole order, normal
crossings, or RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 binary prefix delta

Reproduction:
`reproduction-lemma5-eq5-binary-prefix-delta-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-binary-prefix-delta.md`.
Review artifact:
`review-lemma5-eq5-binary-prefix-delta-a5.md`.

Lean now proves the terminal-room endpoint-profile and binary adjacent
prefix-delta theorem:

```text
aoyagiLemma5Eq5_endpointChain_incrementPrefix_profile_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom
```

For a supplied Eq5 piecewise vector, supplied endpoint-chain correspondence,
source endpoint `H_0=m_0`, terminal endpoint `H_ell=0`, selected-width sum,
and terminal room, every successive Lemma 4 increment-prefix delta is `0` or
`1`.  The proof records the four adjacent ranges: initial rise, alpha plateau,
post-`p` rise, and final plateau.  This is endpoint arithmetic only.  It does
not construct Eq5 vectors, prove endpoint realisation, terminality,
classifier data, order count, pole order, normal crossings, or RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 two-value wrappers

Reproduction:
`reproduction-lemma5-eq5-two-value-wrapper-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-two-value-wrapper.md`.
Review artifact:
`review-lemma5-eq5-two-value-wrapper-a5.md`.

Lean now packages the supplied Eq5 terminal-room binary-prefix deltas into
the existing Lemma 4 APIs:

```text
aoyagiLemma5Eq5_endpointChain_F_twoValue_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_twoValueCount_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefix_count_eq_of_terminalRoom
aoyagiLemma5Eq5_endpointChain_HtildeChainBounds_of_terminalRoom
```

These wrappers prove two-value increments, two-value counts, binary-prefix
counts, and displayed Htilde chain bounds for the supplied Eq5 endpoint chain
under the same explicit source, terminal, selected-sum, endpoint-chain, and
terminal-room hypotheses.  This is API packaging only.  It does not construct
Eq5 vectors, prove endpoint realisation, terminality, counted-datum
membership, classifier data, order count, pole order, normal crossings, or
RLCT.

## 2026-06-21 Lean Lemma 5 terminal minimum lower bound

Reproduction:
`reproduction-lemma5-terminal-minimum-lower-bound-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-minimum-lower-bound.md`.
Review artifact:
`review-lemma5-terminal-minimum-lower-bound-a5.md`.

Lean now packages the easy lower-bound direction for the supplied terminal
candidate family:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_terminalMinimumLabels_card
AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_terminalMinimumLabels_card_of_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_terminalMinimumLabels_card_of_branchLabel_injOn
```

The first theorem is the cardinality form of the existing
`branchLabelImage_subset_terminalMinimumLabels`.  The latter two add supplied
branch-label injectivity and the supplied family count to show
`a*(n+1-a)+1 <= C.terminalMinimumLabels.card`.

This is only the supplied-candidates-attain-minimum direction.  It does not
prove no-extra terminal-minimum coverage, the upper bound, exact
terminal-minimum cardinality, pole order, normal crossings, or RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 nonfirst block explicit bounds

Reproduction:
`reproduction-lemma5-eq5-nonfirst-block-bounds-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-nonfirst-block-bounds.md`.
Review artifact:
`review-lemma5-eq5-nonfirst-block-bounds-a5.md`.

Lean now unwraps the already proved nonfirst Eq5 interval-membership theorem
into explicit same-coordinate Htilde bounds:

```text
aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_postPLowerGuard
aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_terminalRoom
```

Under a supplied Eq5 piecewise certificate, strict alpha-domain membership,
`1<=b`, and `C.block b S`, the first theorem uses the explicit post-`p` lower
guard to prove `Htilde_b <= T S <= Htilde'_b`.  The second theorem replaces
that guard by the terminal-room inequality `p+2*a-alpha<=ell`.

This is only interval-membership unwrapping.  It does not construct Eq5
vectors, prove source-label legality, produce the post-`p` guard from source
hypotheses, prove terminality, selected-span exactness,
classifier/injection/back-to-label coverage, Lemma 5 order count, pole order,
normal crossings, or RLCT.

## 2026-06-21 Lean Lemma 5 counted-datum maps-to adapters

Reproduction:
`reproduction-lemma5-counted-datum-maps-to-adapters-a5.md`.
Statement card:
`statement-card-a5-lemma5-counted-datum-maps-to-adapters.md`.
Review artifact:
`review-lemma5-counted-datum-maps-to-adapters-a5.md`.

Lean now exposes the primitive counted-datum maps-to step in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`:

```text
aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat
aoyagiLemma5CountDatumSet_mem_of_HtildeBounds
```

At an interior coordinate, interval membership plus a supplied non-base-value
inequality gives `some (j,H)` membership in the counted-datum codomain.  The
bounds variant first converts explicit Htilde lower/upper bounds into interval
membership.  This is finite codomain bookkeeping only.  It does not construct
a source branch, Eq3/Eq4/Eq5 vector, classifier, injection, back-to-label map,
terminal-minimum exactness, order count, pole order, normal crossings, or
RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 counted-datum bridge

Reproduction:
`reproduction-lemma5-eq5-counted-datum-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-counted-datum-bridge.md`.
Review artifact:
`review-lemma5-eq5-counted-datum-bridge-a5.md`.

Lean now packages the exact handoff from supplied Eq5 nonfirst interval
admissibility to the counted-datum codomain:

```text
aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_postPLowerGuard
aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_terminalRoom
```

For a supplied Eq5 piecewise vector, strict alpha-domain membership, nonfirst
block data, and a supplied non-base-value inequality, the branch value
`T S` gives a counted datum `some (b,T S)`.  The two variants use either the
explicit post-`p` guard or the terminal-room inequality.  This is maps-to
bookkeeping only.  It does not construct Eq5 vectors, prove nonbase status,
prove classifier/injection/back-to-label coverage, prove an order count, pole
order, normal crossings, or RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint counted-datum bridge

Reproduction:
`reproduction-lemma5-eq5-endpoint-counted-datum-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-counted-datum-bridge.md`.
Review artifact:
`review-lemma5-eq5-endpoint-counted-datum-bridge-a5.md`.

Lean now proves counted-datum codomain membership for supplied Eq5
terminal-room endpoint values:

```text
aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom
aoyagiLemma5Eq5_endpointValue_countDatumSet_mem_of_terminalRoom
```

The first theorem maps the chain value `H_j` at an interior selected
coordinate into `aoyagiLemma5CountDatumSet`, using the Eq5 binary-prefix-delta
theorem and the existing terminal-binary counted-datum maps-to theorem.  The
second rewrites this through the supplied endpoint-chain correspondence to
map the source-facing value `T(C.point j - 1)`.  Both require the relevant
nonbase inequality as a hypothesis.  This does not construct Eq5 vectors,
endpoint realisation, nonbase status, classifiers, injection, back-to-label
coverage, order count, pole order, normal crossings, or RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 own-block counted/introduced payload

Reproduction:
`reproduction-lemma5-eq5-ownblock-counted-introduced-payload-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-ownblock-counted-introduced-payload.md`.
Review artifact:
`review-lemma5-eq5-ownblock-counted-introduced-payload-a5.md`.

Lean now packages one supplied Eq5 own-block branch as both counted-datum and
introduced-label data:

```text
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
```

Under a supplied Eq5 piecewise certificate, an own-block source coordinate,
the last-point source range, selected-width bound at `S`, the Eq5 label
formula, positive coordinate `1<=p`, and the explicit nonbase inequality
`T S != baseValue p`, the theorem proves
`some (p,T S)` belongs to `aoyagiLemma5CountDatumSet` and also proves
`T S=k-1` with `Sigma.mk S k` in `introducedLabelFinset L n S k`.  This is a
one-branch payload adapter only.  It does not construct Eq5 vectors, prove
nonbase status, alpha-domain coverage, classifier data, injection,
back-to-label coverage, no-extra terminal-minimum coverage, order count, pole
order, normal crossings, or RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 own-block block-width payload

Reproduction:
`reproduction-lemma5-eq5-ownblock-block-width-payload-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-ownblock-block-width-payload.md`.
Review artifact:
`review-lemma5-eq5-ownblock-block-width-payload-a5.md`.

Lean now adds the block-width version of the Eq5 own-block counted/introduced
payload:

```text
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_blockWidth
```

The theorem derives the selected-width bound from `C.block p S` and the
block-local actual-width lower-bound hypothesis, then reuses the existing
raw-width payload.  It also derives `1<=p` from the Eq5 strict alpha data.

This remains a one-branch payload adapter.  It does not construct Eq5 vectors,
prove nonbase status, construct a classifier, prove back-to-label coverage,
prove a Lemma 5 order count, prove pole order, prove normal crossings, or
extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 own-block width-source variants

Reproduction:
`reproduction-lemma5-eq5-ownblock-width-source-variants-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-ownblock-width-source-variants.md`.
Review artifact:
`review-lemma5-eq5-ownblock-width-source-variants-a5.md`.

Lean now adds three source-shaped versions of the Eq5 own-block
counted/introduced payload:

```text
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_leftEndpointMin
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected_lt
```

Each theorem derives the selected-width bound from one of the existing
`AoyagiSelectedCutpoints` width-dominance APIs, then reuses the raw-width
own-block payload.  The selected-width source hypotheses and explicit
nonbase inequality remain hypotheses.

This remains a one-branch payload adapter.  It does not construct Eq5 vectors,
prove nonbase status, construct a classifier, prove back-to-label coverage,
prove a Lemma 5 order count, prove pole order, prove normal crossings, or
extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 own-block counted-datum classifier

Reproduction:
`reproduction-lemma5-eq5-ownblock-countdatum-classifier-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-ownblock-countdatum-classifier.md`.
Review artifact:
`review-lemma5-eq5-ownblock-countdatum-classifier-a5.md`.

Lean now packages finite supplied Eq5 own-block source labels as a counted
datum classifier:

```text
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_blockWidth
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_leftEndpointMin
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected_lt
```

The classifier maps a supplied label `(S,k)` to
`some (pOf label, T label S)`.  Lean proves the `mapsTo` field from the
existing one-branch Eq5 own-block payload and keeps `Set.InjOn classify
labels` as a hypothesis.

This is supplied classifier packaging only.  It does not construct Eq5
vectors, prove nonbase status, derive classifier injectivity, lift local
introduced labels to a terminal domain, prove back-to-label coverage, prove a
Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 own-block common introduced domain

Reproduction:
`reproduction-lemma5-eq5-ownblock-common-introduced-domain-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-ownblock-common-introduced-domain.md`.
Review artifact:
`review-lemma5-eq5-ownblock-common-introduced-domain-a5.md`.

Lean now proves introduced-label monotonicity and Eq5 own-block common-domain
wrappers:

```text
introducedLabel_mono_state
introducedLabelFinset_subset_of_state_le
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_blockWidth
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_leftEndpointMin
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected
aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected_lt
```

The state-monotonicity theorem moves introduced-label membership forward
under `S<S' or (S=S' and J<=J')`.  The Eq5 wrappers use this to lift the
local payload label `(S,k)` from `introducedLabelFinset L n S k` to an
explicit supplied target `introducedLabelFinset L n Sfinal Jfinal`.

This is common-domain bookkeeping only.  It does not construct terminal
states, Eq5 vectors, nonbase status, classifier injectivity, back-to-label
coverage, a Lemma 5 order count, pole order, normal crossings, or RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 terminal counted-datum classifier

Reproduction:
`reproduction-lemma5-eq5-terminal-countdatum-classifier-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-terminal-countdatum-classifier.md`.
Review artifact:
`review-lemma5-eq5-terminal-countdatum-classifier-a5.md`.

Lean now adds `Lemma5Eq5TerminalClassifier.lean` with terminal-minimum
counted-datum classifier constructors:

```text
terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound
terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_blockWidth
terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_leftEndpointMin
terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected
terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_offSelected_lt
```

For each label in `TC.terminalMinimumLabels`, the classifier maps `(S,k)` to
`some (pOf label, T label S)`.  Lean proves the classifier `mapsTo` field
from the Eq5 own-block common-domain payload and keeps classifier injectivity
as a supplied hypothesis.

This is terminal counted-datum classifier packaging only.  It does not
construct Eq5 branches, prove that all terminal labels have Eq5 witnesses,
derive injectivity, build a back-to-label map, prove `UpperBoundClassifier`,
prove exactness, prove a Lemma 5 order count, prove pole order, prove normal
crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 terminal counted-datum cardinal squeeze

Reproduction:
`reproduction-lemma5-eq5-terminal-countdatum-cardinal-squeeze-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-terminal-countdatum-cardinal-squeeze.md`.
Review artifact:
`review-lemma5-eq5-terminal-countdatum-cardinal-squeeze-a5.md`.

Lean now composes the Eq5 terminal counted-datum classifier constructors with
the existing finite upper-bound and cardinal-squeeze API.  The upper-bound
wrappers are:

```text
terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound
terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_blockWidth
terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_leftEndpointMin
terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_offSelected
terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_offSelected_lt
```

They prove

```text
TC.terminalMinimumLabels.card <= a * (N + 1 - a) + 1
```

from supplied Eq5 payload data and supplied counted-datum injectivity.

The width-bound exactness wrappers additionally assume supplied branch-label
injectivity and prove equality with `TC.branchLabelImage`,
`TC.TerminalMinimumLabelExactness`, the exact cardinality, and a branch-label
bijection onto `TC.terminalMinimumLabels`.  The counted-datum injectivity and
branch-label injectivity hypotheses remain separate.

This is finite conditional API composition only.  It does not construct Eq5
branches, prove Eq5 payloads for terminal labels, prove either injectivity
from source, build a counted-datum-preserving back-to-label map, prove the
printed Lemma 5 order count, prove pole order, prove normal crossings, or
extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 alpha endpoint value-image split

Reproduction:
`reproduction-lemma5-eq5-alpha-endpoint-value-image-split-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-alpha-endpoint-value-image-split.md`.
Review artifact:
`review-lemma5-eq5-alpha-endpoint-value-image-split-a5.md`.

Lean now packages the one-coordinate value-image split:

```text
aoyagiLemma5Eq5_alphaIndexedBranch_suppliedEndpointCoverage_value_image_split
```

For a supplied alpha-indexed Eq5 strict-offset branch family at an interior
coordinate `p`, if the alpha image is exactly the strict Eq5 alpha domain and
the branch values are `Htilde'_p-alpha`, then the branch image is the Eq5
offset-value set.  Adding a supplied upper endpoint branch fills the interval
outside the rising case; in the rising case `p<=a` and `p<=ell-a`, adding both
supplied upper and lower endpoint branches fills the interval.  This is
one-coordinate finite value-image bookkeeping only.  It does not construct Eq5
branches, prove source-label legality, prove value injectivity, prove
base-value membership, prove cross-coordinate disjointness, construct a
classifier, prove no-extra terminal-minimum coverage, order count, pole order,
normal crossings, or RLCT.

## 2026-06-22 Lean Lemma 5 Eq3/Eq4 local interval cardinality

Reproduction:
`reproduction-lemma5-eq3-eq4-local-interval-cardinality-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq3-eq4-local-interval-cardinality.md`.
Review artifact:
`review-lemma5-eq3-eq4-local-interval-cardinality-a5.md`.

Lean now adds source-legality-free cardinality consequences of the local
Eq3/Eq4 rising-interval coverage equality:

```text
aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_intervalSize
aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_offsetCard_add_two
```

The first counts the local insert set by the same-coordinate interval size.
The second rewrites that same count as the strict Eq5 offset-set cardinality
plus two.  Both use only the local Eq3-shaped upper-component certificate,
the local Eq4 lower-endpoint certificate, `1<=p`, and the Eq4 rising-side
guard.

This is one-coordinate finite count bookkeeping only.  It does not construct
displayed vectors, prove source-label legality, build classifier coverage,
prove a Lemma 5 order count, prove pole order, prove normal crossings, or
extract RLCT.

## 2026-06-21 Lean Lemma 4 prefix-profile computations

Reproduction:
`reproduction-lemma4-prefix-profile-computations-a5.md`.
Statement card:
`statement-card-a5-lemma4-prefix-profile-computations.md`.
Review artifact:
`review-lemma4-prefix-profile-computations-a5.md`.

Lean now proves two generic coordinate computations for the Lemma 4
increment-prefix normal form:

```text
aoyagiLemma4IncrementPrefix_eq_upperHighCount_add_of_eq_upperNat_sub
aoyagiLemma4IncrementPrefix_eq_lowerHighCount_of_eq_lowerNat
```

If `H_j=Htilde'_j-r`, then the prefix value is `upperHighCount_j+r`; if
`H_j=Htilde_j`, then it is `lowerHighCount_j`.  The initial and terminal
profile facts were already present as
`aoyagiLemma4IncrementPrefix_zero_of_H0` and
`aoyagiLemma4IncrementPrefix_last_eq_a_of_terminalH`.  This is generic algebra
for a later Eq5 endpoint profile.  It does not prove binary deltas, two-value
Lemma 4 increments, Eq5 vector construction, endpoint realisation, classifier
data, order count, pole order, normal crossings, or RLCT.

## 2026-06-21 Lean Lemma 5 Eq5 endpoint prefix profile

Reproduction:
`reproduction-lemma5-eq5-endpoint-prefix-profile-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-prefix-profile.md`.
Review artifact:
`review-lemma5-eq5-endpoint-prefix-profile-a5.md`.

Lean now proves the four branchwise endpoint-prefix values for a supplied Eq5
piecewise vector and supplied endpoint-chain correspondence:

```text
aoyagiLemma5Eq5_endpointChain_incrementPrefix_preAlpha
aoyagiLemma5Eq5_endpointChain_incrementPrefix_alphaToP
aoyagiLemma5Eq5_endpointChain_incrementPrefix_postP
aoyagiLemma5Eq5_endpointChain_incrementPrefix_tail
```

The pre-alpha branch gives prefix value `b`; alpha-to-`p` gives `alpha-1`;
post-`p` gives `alpha+b-p`; tail gives `a`.  The alpha-to-`p` and post-`p`
profiles use the terminal-room hypothesis.  This is branchwise endpoint
profile arithmetic only.  It does not combine adjacent branches, prove binary
prefix deltas, prove Lemma 4 two-value increments, construct Eq5 vectors,
prove endpoint realisation, classifier data, order count, pole order, normal
crossings, or RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 branch-label injection

Reproduction:
`reproduction-lemma5-eq5-branch-label-injection-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-branch-label-injection.md`.
Review artifact:
`review-lemma5-eq5-branch-label-injection-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_fullBranches_of_some_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase
```

The first theorem is finite `Option` bookkeeping: nonbase branch-label
injectivity plus explicit base/nonbase separation gives injectivity on the
full supplied terminal branch set.  The second theorem specializes the
nonbase injection to Eq5 alpha-indexed branches.  Equality of Sigma labels
puts two nonbase branches in the same selected block, block uniqueness gives
the same coordinate, and the existing fixed-coordinate alpha-indexed injection
uses supplied alpha injectivity and the displayed Eq5 label formula.

This is conditional branch-label injection only.  It does not construct Eq5
branches, prove alpha-domain coverage, produce terminal payloads, derive
counted-datum injectivity, build back-to-label coverage, construct an
upper-bound classifier, prove no-extra terminal-minimum coverage, prove a
Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 terminal alpha-injection cardinal squeeze

Reproduction:
`reproduction-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze.md`.
Review artifact:
`review-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze
```

These wrappers compose the Eq5 terminal counted-datum cardinal squeeze with
the explicit Eq5 alpha-indexed branch-label injection theorem.  The opaque
`hinjBranchLabel` hypothesis is replaced by coordinatewise branch alpha
injectivity, branch block membership, branch label formula, and base/nonbase
separation.  Counted-datum injectivity and terminal-label Eq5 payloads remain
explicit hypotheses.

This is conditional finite exactness only.  It does not construct Eq5
branches, prove alpha-domain coverage, produce terminal payloads, derive
counted-datum injectivity, build back-to-label coverage, construct an
upper-bound classifier, prove no-extra terminal-minimum coverage, prove a
Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 structured injection adapters

Reproduction:
`reproduction-lemma5-eq5-structured-injection-adapters-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-structured-injection-adapters.md`.
Review artifact:
`review-lemma5-eq5-structured-injection-adapters-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5_ownBlock_countDatum_injOn_of_pAlpha_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatum_injOn_of_eq5OwnBlock_pAlpha_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_none_ne_some_of_terminalEndpointLabel_and_nonbaseBlock
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase_terminalEndpointBase
```

The counted-datum adapter turns supplied `(p, alpha)` injectivity on Eq5
own-block terminal labels into injectivity of the counted-datum map
`label |-> some (pOf label, T label label.1)`, using the Eq5 own-block value
formula `T_s = Htilde'_p - alpha`.  The base/nonbase adapter replaces the
opaque base-separation hypothesis with the explicit terminal-endpoint base
label and nonbase block membership: the terminal endpoint is in no half-open
selected block.

This is structured supplied-hypothesis reduction only.  It does not construct
Eq5 branches, prove `(p, alpha)` injectivity from source, produce
terminal-label payloads, build a counted-datum back-to-label map, prove
no-extra terminal-minimum coverage, prove a Lemma 5 order count, prove pole
order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint raw branches

Reproduction:
`reproduction-lemma5-eq5-endpoint-raw-branches-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-raw-branches.md`.
Review artifact:
`review-lemma5-eq5-endpoint-raw-branches-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5EndpointRawBranches
aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage
```

The raw branch set inserts the supplied upper endpoint at every interior
coordinate and inserts the supplied lower endpoint exactly in the rising case
`j<=a` and `j<=ell-a`.  Its value image is the full same-coordinate interval
when the strict Eq5 branch family covers the strict alpha domain and the
endpoint branch values are supplied.  The supplied-family wrapper feeds this
proved raw value image into `ofCoordinateValueCoverage`; base-value
membership, value injectivity on the raw branch set, and cross-coordinate
disjointness remain explicit hypotheses.

This is finite supplied coverage assembly only.  It does not construct Eq5
branches, prove endpoint records are source-produced, prove source-label
legality, derive raw branch injectivity or disjointness, build a counted-datum
classifier, prove no-extra terminal-minimum coverage, prove a Lemma 5 order
count, prove pole order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint branch coordinates

Reproduction:
`reproduction-lemma5-eq5-endpoint-branchcoord-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-branchcoord.md`.
Review artifact:
`review-lemma5-eq5-endpoint-branchcoord-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branchCoord_eq
```

The raw branch-coordinate adapter dispatches membership in the conditional Eq5
endpoint raw branch set through the strict, upper-endpoint, and explicitly
inserted rising lower-endpoint alternatives.  The supplied-family adapter then
passes this fact through the base-value filter in
`ofCoordinateValueCoverage`, giving the `branchCoord_eq` input needed by the
existing generic counted-datum classifier API.

This is finite coordinate bookkeeping only.  It does not construct Eq5
branches or endpoint records, prove source-label legality, prove the
coordinate map is source-produced, prove endpoint distinctness or base-filter
survival, derive raw branch injectivity/disjointness, add a dedicated Eq5
classifier wrapper, prove no-extra terminal-minimum coverage, prove a Lemma 5
order count, prove pole order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint branch-coordinate disjointness

Reproduction:
`reproduction-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-branchcoord-disjoint.md`.
Review artifact:
`review-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_branchCoord
```

The disjointness theorem says that if every strict, upper-endpoint, and
explicitly inserted rising lower-endpoint component record at an interior
coordinate has supplied coordinate `j`, then raw branch sets for distinct
interior coordinates are disjoint.  The constructor wrapper uses this theorem
to remove the separate cross-coordinate raw-disjointness input from the Eq5
endpoint supplied-family constructor.

This is finite coordinate bookkeeping only.  It does not construct Eq5
branches or endpoint records, prove source-label legality, prove the
coordinate map is source-produced, prove endpoint distinctness or base-filter
survival, derive raw value injectivity, construct a no-extra classifier, prove
a Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint raw value injectivity

Reproduction:
`reproduction-lemma5-eq5-endpoint-value-injective-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-value-injective.md`.
Review artifact:
`review-lemma5-eq5-endpoint-value-injective-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
```

The raw theorem proves one-coordinate value injectivity for the Eq5 endpoint
raw branch set from supplied strict alpha injectivity, strict alpha-domain
coverage, strict value formulas, and endpoint value formulas.  The proof
separates strict-strict collisions by alpha injectivity, excludes upper/strict
and rising lower/strict collisions by the Eq5 offset-value set, and excludes
rising upper/lower collisions by the positive interior Htilde gap.  The
interior-coordinate hypothesis is essential: the analogous `j=0` endpoint raw
set may have coincident upper and lower endpoint values.

The constructor wrapper combines this raw value-injectivity theorem with the
coordinate-disjointness theorem, removing only the raw value-injectivity and
raw disjointness inputs from the strictest Eq5 endpoint supplied-family
constructor.

This is finite endpoint/offset bookkeeping only.  It does not construct Eq5
branches or endpoint records, prove source-label legality, prove strict alpha
injectivity from source, prove endpoint record distinctness as a source fact,
prove base-filter survival, construct a no-extra classifier, prove a Lemma 5
order count, prove pole order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint counted-datum classifier

Reproduction:
`reproduction-lemma5-eq5-endpoint-countdatum-classifier-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-countdatum-classifier.md`.
Review artifact:
`review-lemma5-eq5-endpoint-countdatum-classifier-a5.md`.

Lean now proves/packages:

```text
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq
AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
```

The branch-coordinate theorem unfolds the strictest Eq5 endpoint supplied
constructor, strips the base-value filter to recover raw branch membership, and
applies the raw component-coordinate adapter.  The classifier wrapper then
feeds this branch-coordinate correctness into the generic supplied-family
`countDatumClassifierOfBranchCoord_of_branchCoord_eq` API.

This is finite supplied-family bookkeeping only.  The classifier is for the
constructed supplied `fullBranches`; it is not a source terminal-minimum
classifier.  It does not construct branch records, prove source-label
legality, prove source production of the coordinate map, prove endpoint
distinctness or base-filter survival, prove no-extra coverage, prove a Lemma 5
order count, prove pole order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 terminal pAlpha endpoint cardinal squeeze

Reproduction:
`reproduction-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze.md`.
Review artifact:
`review-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze
```

These theorems compose the structured counted-datum injection adapter from
terminal Eq5 own-block payloads and supplied terminal `(p, alpha)` injectivity
with the structured branch-label injection adapter from nonbase alpha-indexed
branch data and an explicit terminal-endpoint base label.  The result feeds
those two derived injectivity facts into the existing finite cardinal-squeeze
wrappers, proving conditional terminal-minimum exactness and the exact finite
count under the supplied hypotheses.

This is finite terminal-candidate bookkeeping only.  It does not construct Eq5
branches, prove terminal Eq5 payload coverage from source, prove terminal
`(p, alpha)` injectivity from source, build a counted-datum back-to-label map,
prove source-backed no-extra coverage, prove the Lemma 5 order count, prove
pole order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint raw cardinality

Reproduction:
`reproduction-lemma5-eq5-endpoint-raw-cardinality-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-raw-cardinality.md`.
Review artifact:
`review-lemma5-eq5-endpoint-raw-cardinality-a5.md`.

Lean now proves:

```text
aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_value_injective
aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_alpha_injective
```

The first theorem counts a one-coordinate Eq5 endpoint raw branch set through
its injective value image.  The raw value image is already the Htilde interval
value set, and that value set has cardinality
`aoyagiLemma5IntervalSize ell a j` for an interior coordinate.  The second
theorem supplies raw value injectivity from the previous strict
alpha-injective endpoint wrapper.

This is finite raw endpoint bookkeeping only.  It does not construct Eq5
branches or endpoint records, prove source-label legality, prove source
strict alpha injectivity, prove base-filter survival, count filtered nonbase
branches, classify terminal-minimum labels, prove no-extra coverage, prove a
Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint filtered cardinality

Reproduction:
`reproduction-lemma5-eq5-endpoint-filtered-cardinality-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-filtered-cardinality.md`.
Review artifact:
`review-lemma5-eq5-endpoint-filtered-cardinality-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branch_card_eq_intervalSize_sub_one
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_fullBranches_card
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_fullBranches_card
```

The first theorem specializes the generic supplied nonbase-family
one-coordinate count to the filtered Eq5 endpoint constructor: the raw endpoint
family covers the full same-coordinate interval, then the constructor erases
the supplied base value.  The next two specialize the generic full tagged
branch count to the general endpoint constructor and to the strictest
alpha-injective/component-coordinate endpoint constructor.

This is finite supplied-family bookkeeping only.  It counts filtered supplied
branches and the tagged supplied full branch set, not terminal-minimum labels.
It does not construct Eq5 branches or endpoint records, prove source-label
legality, prove base-filter survival for source records, classify
terminal-minimum labels, prove source-backed no-extra coverage, prove a
Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 value-label branch injection

Reproduction:
`reproduction-lemma5-eq5-value-label-branch-injection-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-value-label-branch-injection.md`.
Review artifact:
`review-lemma5-eq5-value-label-branch-injection-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze
```

The branch-label theorem proves injectivity on the full `Option`-tagged
branch set from supplied selected-block membership, supplied nonbase
value-label synchronisation
`TC.family.value b = ((TC.branchLabel (some b)).2 : Z) - 1`, and either
explicit base/nonbase label separation or the terminal-endpoint base-label
wrapper.  The cardinal-squeeze wrappers use this branch-label injectivity
together with the existing terminal `(p, alpha)` counted-datum injectivity
adapter.

This is finite terminal-candidate bookkeeping only.  It replaces the earlier
branch-alpha formula/injectivity inputs with supplied value-label data.  It
does not construct Eq5 branches, prove the value-label relation from source,
prove terminal Eq5 payload coverage from source, prove terminal
`(p, alpha)` injectivity from source, build a direct counted-datum
back-to-label map, prove source-backed no-extra coverage, prove a Lemma 5
order count, prove pole order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 branch-coordinate/value cardinal squeeze

Reproduction:
`reproduction-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-branchcoord-value-cardinal-squeeze.md`.
Review artifact:
`review-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_branchCoord_leftEndpoint
AoyagiLemma5SuppliedTerminalCandidateFamily.valueLabel_of_branchK_value
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_branchCoord_leftEndpoint_branchK_value_terminalEndpointBase
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze
```

The first adapter derives nonbase selected-block membership from supplied
branch-coordinate correctness and supplied left-endpoint `branchS` labels.
The second unfolds `TC.branchLabel` to turn a supplied `branchK`/value formula
into the Sigma value-label relation.  The branch-injection and cardinal-squeeze
wrappers then compose those adapters with the previous value-label branch
injection and terminal pAlpha counted-datum injection.

This is finite terminal-candidate bookkeeping only.  It does not construct Eq5
branches, prove the branch-coordinate map from source, prove source branch
labels, prove terminal Eq5 payload coverage from source, prove terminal
`(p, alpha)` injectivity from source, build a direct counted-datum
back-to-label map, prove source-backed no-extra coverage, prove a Lemma 5
order count, prove pole order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 strict endpoint filtered cardinality

Reproduction:
`reproduction-lemma5-eq5-endpoint-strict-filtered-cardinality-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-strict-filtered-cardinality.md`.
Review artifact:
`review-lemma5-eq5-endpoint-strict-filtered-and-terminal-branchcoord-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_strict_branch_card_eq_intervalSize_sub_one
```

This specializes the one-coordinate filtered endpoint count to the strictest
Eq5 endpoint constructor.  Raw value injectivity is discharged by supplied
strict alpha injectivity and endpoint value formulas; raw cross-coordinate
disjointness is discharged by supplied component-coordinate facts.  The result
counts the filtered supplied coordinate branch set after deleting the supplied
base value.

This is finite supplied-family bookkeeping only.  It does not construct Eq5
branches or endpoint records, prove source-label legality, prove source
strict alpha injectivity, prove base-filter survival for a source record,
count terminal-minimum labels, prove source-backed no-extra coverage, prove a
Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint-to-terminal branch coordinates

Reproduction:
`reproduction-lemma5-eq5-endpoint-to-terminal-branchcoord-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-to-terminal-branchcoord.md`.
Review artifact:
`review-lemma5-eq5-endpoint-strict-filtered-and-terminal-branchcoord-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.branchCoord_of_toNonbase_eq_eq5EndpointCoverage
AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint
```

The coordinate transport theorem assumes explicitly that
`TC.family.toAoyagiLemma5SuppliedNonbaseFamily` is the strictest Eq5 endpoint
constructor.  Under that supplied equality, membership in
`TC.family.branches j` rewrites to membership in the endpoint constructor's
filtered branch set, so the existing endpoint branch-coordinate theorem gives
`branchCoord b=j`.  The selected-block wrapper then combines this with the
separate supplied left-endpoint `branchS` formula and the existing
`branchBlock_of_branchCoord_leftEndpoint` adapter.

This is a terminal-family interface theorem only.  It does not identify
terminal-minimum labels with endpoint branches, does not construct Eq5
branches or endpoint records, does not prove source labels or base-filter
survival, and does not prove terminal Eq5 payload coverage, terminal
`(p, alpha)` injectivity, no-extra terminal-minimum coverage, Lemma 5 order
count, pole order, normal crossings, or RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint-family cardinal squeeze

Reproduction:
`reproduction-lemma5-eq5-endpoint-family-cardinal-squeeze-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-family-cardinal-squeeze.md`.
Review artifact:
`review-lemma5-eq5-endpoint-family-cardinal-squeeze-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_cardSqueeze
```

These wrappers compose the endpoint-to-terminal branch-coordinate transport
with the existing branch-coordinate/value cardinal-squeeze route.  The
explicit equality between `TC.family.toAoyagiLemma5SuppliedNonbaseFamily` and
the strictest Eq5 endpoint constructor replaces only the abstract terminal
`hbranchCoord` hypothesis.

This remains conditional terminal-candidate bookkeeping.  Terminal Eq5
payloads, terminal `(p, alpha)` injectivity, endpoint-family equality,
`branchS`, `branchK`, terminal-label nonbase inequalities, and the endpoint
base label are all still supplied.  The wrappers do not construct Eq5
branches, prove source labels, prove base-filter survival, build a direct
counted-datum back-to-label map, prove source-backed no-extra coverage, prove
a Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

## 2026-06-22 Lean Lemma 5 Eq5 endpoint-family block-width cardinal squeeze

Reproduction:
`reproduction-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze.md`.
Review artifact:
`review-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
```

These wrappers replace the endpoint-family cardinal squeeze's per-label width
bound by a blockwise actual-width hypothesis.  The only new proof step is
`cut.selectedWidthNat_le_actualWidth_of_block`, applied using the supplied
terminal-label block hypothesis.  Everything else is passed unchanged to the
previous endpoint-family cardinal squeeze.

This is a boundary-shaping wrapper only.  It still assumes terminal Eq5
payloads, terminal `(p, alpha)` injectivity, endpoint-family equality,
`branchS`, `branchK`, terminal-label nonbase inequalities, blockwise
actual-width data, and the endpoint base label.  It does not construct Eq5
branches, prove source labels, prove base-filter survival, build a direct
counted-datum back-to-label map, prove source-backed no-extra coverage, prove
a Lemma 5 order count, prove pole order, prove normal crossings, or extract
RLCT.

Source audit update: an xhigh Aoyagi-only source audit on 2026-06-22
recommended freezing A5 as a supplied boundary for now.  The printed
Eq3/Eq4/Eq5 families on PDF pp. 25-27 do not by themselves provide the
classifier, injection, back-to-label map, or full Lemma 4 witness needed for a
source-backed Lemma 5 order-count proof.  Further A5 work should be limited to
small handoff wrappers needed downstream unless the source policy changes or a
corrected independent construction is supplied.

## 2026-06-22 Lean Lemma 5 terminal exactness cardinal-bound equivalence

Reproduction:
`reproduction-lemma5-terminal-exactness-card-bound-equivalence-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-exactness-card-bound-equivalence.md`.
Review artifact:
`review-lemma5-terminal-exactness-card-bound-equivalence-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_card_bound_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound
```

The helper is the finite cardinal squeeze.  The supplied branch-label image is
already a subset of `terminalMinimumLabels`; branch-label injectivity gives
the image cardinality `a*(n+1-a)+1`; a supplied upper bound
`terminalMinimumLabels.card <= a*(n+1-a)+1` then forces equality of the finite
sets.  The equivalence theorem packages this as the exact remaining finite
obstruction: terminal exactness is branch-label injectivity plus the supplied
terminal-minimum cardinal upper bound.

This is finite terminal-candidate bookkeeping only.  It deliberately does not
prove the upper bound from Aoyagi's source, construct a source classifier or
back-to-label map, prove branch-label injectivity from source, build source
branches, bridge the minimum to lambda, prove chart coverage, prove pole
order, prove normal crossings, or extract RLCT.

## 2026-06-22 Lean Lemma 5 terminal order formula bridge

Reproduction:
`reproduction-lemma5-terminal-order-formula-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-order-formula-bridge.md`.
Review artifact:
`review-lemma5-terminal-order-formula-bridge-a5.md`.

Lean now rewrites the remaining supplied terminal-exactness obstruction in
Aoyagi Theorem 2's order notation:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_theorem2OrderFormula_bound
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn
```

For `data : AoyagiDefinition3CeilData (n+1) m` and a terminal-candidate
family with `a=data.aParam` and `M=data.ceilWidth`, the bridge replaces the
raw bound `terminalMinimumLabels.card <= data.aParam*(n+1-data.aParam)+1`
by `terminalMinimumLabels.card <= data.theorem2OrderFormula`.  If branch-label
injectivity and this upper bound are supplied, Lean proves the terminal
minimum label count equals `data.theorem2OrderFormula`.

This is a downstream handoff only.  It does not source-prove the upper bound,
construct branch-label injectivity, prove no-extra coverage, prove the A6
finite exponent formula, identify pole order, prove normal crossings, or
extract RLCT.

## 2026-06-22 Lean Lemma 5 counted-datum classifier order-formula bridge

Reproduction:
`reproduction-lemma5-countdatum-classifier-order-formula-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma5-countdatum-classifier-order-formula-bridge.md`.
Review artifact:
`review-lemma5-countdatum-classifier-order-formula-bridge-a5.md`.

Lean now proves:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumClassifier_and_branchLabel_injOn
```

These wrappers feed a supplied terminal-minimum counted-datum classifier
directly into Aoyagi Theorem 2's displayed order formula
`data.theorem2OrderFormula`.  Adding supplied branch-label injectivity then
reuses the existing terminal-cardinality squeeze to get equality.

This is a finite A5-to-A6 handoff only.  It does not construct the
counted-datum classifier, branch-label injectivity, a back-to-label map,
Eq3/Eq4/Eq5 branch coverage, terminal `tilde t=0`, source labels, pole order,
normal crossings, or RLCT extraction.

## 2026-06-23 Lean Lemma 5 terminal order classifier notation

Reproduction:
`reproduction-lemma5-terminal-order-classifier-notation-a5.md`.
Statement card:
`statement-card-a5-lemma5-terminal-order-classifier-notation.md`.
Review artifact:
`review-lemma5-terminal-order-classifier-notation-a5.md`.

Lean now exposes the existing upper-bound-classifier and counted-datum
back-to-label routes directly in Aoyagi Theorem 2 order notation:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_upperBoundClassifier
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_upperBoundClassifier_and_branchLabel_injOn
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumBackToBranchLabel
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumBackToBranchLabel_and_injOn
```

These wrappers only rewrite the already-proved finite bounds
`a*(n+1-a)+1` as `data.theorem2OrderFormula` for
`data : AoyagiDefinition3CeilData (n+1) m`.  The exact-count wrappers still
require supplied branch-label injectivity.  They do not construct an
upper-bound classifier, counted-datum classifier, back-to-label bridge,
branch-label injection, Eq3/Eq4/Eq5 terminal family, no-extra coverage, pole
order, normal crossings, or RLCT.

## 2026-06-23 Lean Lemma 5 Eq5 terminal order formula bridge

Reproduction:
`reproduction-lemma5-eq5-terminal-order-formula-bridge-a5.md`.
Statement card:
`statement-card-a5-lemma5-eq5-terminal-order-formula-bridge.md`.
Review artifact:
`review-lemma5-eq5-terminal-order-formula-bridge-a5.md`.

Lean now specializes the existing Eq5 endpoint-family block-width cardinal
squeeze to Aoyagi Theorem 2 order notation:

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze
```

For `data : AoyagiDefinition3CeilData (N+1) m`, the theorem binds
`a=data.aParam` and `M=data.ceilWidth`, uses `data.aParam_le` and
`data.selectedSum_eq` as the two Definition 3 inputs to the existing Eq5
count theorem, and rewrites the result as
`TC.terminalMinimumLabels.card = data.theorem2OrderFormula`.

This is a thin finite handoff.  It does not source-construct the Eq5 endpoint
family, terminal Eq5 payloads, endpoint-family equality, terminal
`(p, alpha)` injectivity, branch-label injectivity, no-extra coverage, pole
order, normal crossings, or RLCT.

## 2026-06-24 Lean Lemma 5 base-value interval membership

Reproduction:
`reproduction-lemma5-base-value-interval-membership-a5.md`.
Statement card:
`statement-card-a5-lemma5-base-value-interval-membership.md`.
Review artifact:
`review-lemma5-base-value-interval-membership-a5.md`.

Lean now proves:

```text
aoyagiLemma5BaseValue_mem_intervalValueSetNat_of_baseChainBounds
```

If a supplied base chain `baseH : Fin (ell+1) -> Int` is squeezed between
Aoyagi's displayed lower and upper `Htilde` chains, and the supplied
`baseValue j` agrees with `baseH` at every interior selected coordinate, then
`baseValue j` lies in the Nat-indexed interval value set used by the Lemma 5
counted-datum codomain.

This removes one recurring naked `baseValue_mem` obligation by replacing it
with explicit base-chain bounds plus a coordinate equality.  It does not
construct the base chain from Aoyagi's printed Eq3/Eq4/Eq5, prove source-label
legality, no-extra coverage, injectivity, back-to-label coverage, terminal
exactness, pole order, normal crossings, or RLCT extraction.

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

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

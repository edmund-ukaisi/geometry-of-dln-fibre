# A4 Case 1(2) Displayed Row-Strip New-Label Exponent

Status: reproduced the elementary exponent calculation for the fresh
Case 1(2) label `(S,J+1)`.

## Source Facts

Aoyagi's Case 1(2) starts from an old selected label `(s,k)` with

```text
tilde_t_(s,k) = J + J1.
```

In the displayed row-strip chart, the old selected variable is factored as

```text
u_(s,k) = u_(S,J+1) u'_(s,k).
```

The paper then introduces a fresh label `(S,J+1)` whose exponent vector has
the old selected prefix before `S` and the constant tail `J`:

```text
t'_(S,J+1)^i = t_(s,k)^i,     i < S,
t'_(S,J+1)^i = J,             S <= i <= L.
```

The printed numerator increment is

```text
M'_(S,J+1) = M_(s,k) + J1 * (M^(S+1) - J).
```

In Lean notation the actual width `M^(S+1)` is `n (S+1)`, while prefix minima
are separate objects. The source-validity of the new label uses the actual
width hypothesis

```text
J + 1 <= n (S + 1).
```

## Pen-And-Paper Derivation

Let

```text
T = t_(s,k),
h = J + J1,
T' = lowerTailVector T S J.
```

Thus `T'_i = T_i` for `i < S` and `T'_i = J` for `S <= i`.

Assume the old selected label is certified with least value `h`, and assume
the flat-tail invariant

```text
T_(S-1) = h,
T_i = h for S <= i <= L.
```

Also assume `2 <= S <= L`, so the terminal-exponent summand at `j=S` is
present and has a predecessor.

For `i < S`, the old least-value certificate gives `h <= T_i`, hence
`J <= T_i`. For `i >= S`, `T'_i = J`. Therefore the least value of the new
vector on `1..L` is exactly `J`, witnessed at `i=S`.

For the terminal exponent

```text
E(T) =
(n_1 - T_1)(n_2 - T_1)
+ sum_{j=2}^L (T_(j-1) - T_j)(n_(j+1) - T_j),
```

all summands are unchanged except `j=S`. The old `j=S` summand is

```text
(h - h) * (n_(S+1) - h) = 0,
```

and the new `j=S` summand is

```text
(h - J) * (n_(S+1) - J)
= J1 * (n_(S+1) - J).
```

Thus

```text
E(T') = E(T) + J1 * (n_(S+1) - J).
```

This is the elementary calculation behind Aoyagi's printed
`M'_(S,J+1)` formula.

## Lean Boundary

Lean already had the same-vector arithmetic as

```text
Case1FirstJumpHypotheses.lowerTailVector_labelExponentCertificate
```

for a same-domain update of the old selected label. The new checkpoint adds a
separate theorem for the fresh label:

```text
Case1FirstJumpHypotheses.displayedRowStrip_newLabelExponentCertificate
```

The proof reuses the terminal-exponent and least-value fields of the old
lower-tail certificate, but replaces the `introduced` field with the
post-state proof

```text
introducedLabel L n S (J+1) S (J+1).
```

The checkpoint also packages supplied post-data:

```text
Case1DisplayedRowStripExponentPostData
```

and domain-extension wrappers for all introduced-label certificates:

```text
IntroducedLabelExponentCertificates
  .extendDomain_case1DisplayedRowStripNewLabel_of_postData
IntroducedLabelExponentCertificates
  .extendDomain_case1DisplayedRowStripNewLabel_updateData
IntroducedLabelExponentCertificates
  .extendDomain_case1DisplayedRowStripNewLabel_of_levelTailInvariants
```

The concrete update-data wrapper changes only `(S,J+1)`. Preservation of old
introduced labels is justified by the existing fact that `(S,J+1)` is not
introduced at state `(S,J)`.

## Caveats

- This is not a Case 1 transition theorem.
- The chart production of the post-data is supplied, not proved.
- The old selected label remains an old introduced label; this theorem adds a
  fresh label rather than replacing it.
- The level-to-least-value bridge and `FlatTailFromPred` invariant remain
  supplied hypotheses.
- The theorem requires `2 <= S`; no `S=1` endpoint theorem is included.
- No recurrence production, `b'_i` normalization choice, chart regularity,
  Jacobian formula, normal crossings, or RLCT extraction is proved.

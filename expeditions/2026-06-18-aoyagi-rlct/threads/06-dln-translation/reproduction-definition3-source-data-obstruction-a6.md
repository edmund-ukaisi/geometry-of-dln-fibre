# Reproduction - Definition 3 source-data obstruction

Date: 2026-06-24.

Status: reproduced; Lean diagnostic landed.

Independent source scout:
Leibniz the 2nd, xhigh read-only source check.

## Question

Can Aoyagi Definition 3, as printed, be turned into an arbitrary
selected-cutpoint existence theorem for every reduced-width profile?

The finite profile

```text
M^(1)=1,   M^(2)=2,   M^(3)=100
```

shows that the answer is no.  The right formal target is a diagnostic
obstruction, not a source-data existence theorem.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, chooses selected source indices

```text
1 <= S_1 < ... < S_(ell+1) <= L+1
```

and applies the printed inequalities to the selected value set

```text
M = { M^(S_j) : j = 1,...,ell+1 }.
```

The relevant displayed conditions are:

```text
sum_j M^(S_j) > ell * M^(S_i)
```

for selected values, and

```text
sum_j M^(S_j) <= (ell-1) * M^(s)
```

for reduced-width values not in the selected value set.

## Pen-and-paper Calculation

Take `L=2`, `r=0`, and source widths

```text
H(1)=1,   H(2)=2,   H(3)=100.
```

Then the reduced widths are exactly `1,2,100`.

The strict selected cutpoints all lie in `{1,2,3}`.  Therefore

```text
ell + 1 <= 3,
```

so, since Definition 3 has `ell>0`, only `ell=1` and `ell=2` are possible.

If `ell=2`, then all three source positions are selected.  The selected sum is

```text
T = 1 + 2 + 100 = 103.
```

The strict selected inequality at the selected width `100` requires

```text
2 * 100 < 103,
```

which is false.

If `ell=1`, exactly two source positions are selected.  There are three
strictly ordered possibilities.

For selected widths `{1,2}`, the nonselected width is `100`, and the printed
nonselected inequality requires

```text
1 + 2 <= (1-1) * 100 = 0.
```

For selected widths `{1,100}`, the nonselected width is `2`, and the printed
nonselected inequality requires

```text
1 + 100 <= (1-1) * 2 = 0.
```

For selected widths `{2,100}`, the nonselected width is `1`, and the printed
nonselected inequality requires

```text
2 + 100 <= (1-1) * 1 = 0.
```

All three cases contradict positivity of the selected sum.

## Lean Shape

The theorem is:

```text
AoyagiDefinition3SourceData.not_exists_widths_one_two_hundred
```

It states that for

```text
H(s) = if s=1 then 1 else if s=2 then 2 else if s=3 then 100 else 0,
L=2,
r=0,
```

there is no `ell` and no selected cutpoint package `C` with

```text
AoyagiDefinition3SourceData 2 ell H 0 C.
```

## Nonclaims

This does not prove Aoyagi's RLCT formula false.

It does not prove nonexistence of Definition 3 source data for all width
profiles.

It does not construct or classify selected cutpoints under additional
hypotheses.

It does not change the expedition policy that `AoyagiDefinition3SourceData` is
supplied unless its hypotheses are proved in the current branch.

It proves no Eq5 endpoint-family construction, Lemma 5 exactness, chart
production, normal crossings, pole order, or RLCT.

## Verification

Focused Lean build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

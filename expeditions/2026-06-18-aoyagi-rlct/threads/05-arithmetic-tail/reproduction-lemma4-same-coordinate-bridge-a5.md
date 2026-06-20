# Pen-and-paper reproduction - Lemma 4 same-coordinate bridge

Status: checked source-gap slice.  This records the conservative replacement
for the sentence in Aoyagi's Lemma 4 proof:

```text
Because Ttilde <= T <= Ttilde' and Htilde_ell = Htilde'_ell = 0,
we have H_ell = 0.
```

The conclusion is valid after adding an explicit same-coordinate
correspondence hypothesis.  It is not a consequence of Definition 4 alone.

## Source Check

Definition 4 on PDF p. 14 defines vectors

```text
T = (t_1, ..., t_L)
```

and componentwise order:

```text
T <= T'  iff  t_i <= t'_i for every i.
```

On PDF p. 22, Aoyagi says that for a terminal vector one can choose
sequences `(H_j)` and `(S_j)` with

```text
H_j in {t^(1), ..., t^(L)}
S_j < S_(j+1)
H_j <= H_(j-1)
H_j <= M(S_(j+1))
H_ell = 0.
```

This is an existence statement for a rewriting of the terminal exponent, not a
unique map from a vector `T` to a sequence `(H_j)`.

The nearest explicit coordinate relation appears in the Lemma 5 discussion on
PDF p. 26, where the displayed families use the relation

```text
t^(S_(j+1)-1) = H_j.
```

If this same coordinate is used for the lower extremal vector, the middle
vector, and the upper extremal vector, then the endpoint squeeze follows by
componentwise order.

## Conservative Bridge

Let `p` be the common endpoint coordinate.  Assume:

```text
Tlo <= T <= Thi,
Tlo[p] = E,
T[p] = H_ell,
Thi[p] = E,
```

where `E` is the common terminal endpoint expression for `Htilde_ell` and
`Htilde'_ell`.  Then componentwise order at `p` gives

```text
E = Tlo[p] <= T[p] = H_ell <= Thi[p] = E.
```

Thus

```text
E <= H_ell <= E.
```

Combining this with the previously proved endpoint-zero calculation `E=0`
gives

```text
H_ell = 0.
```

The existing Lemma 4 count wrappers can then be applied exactly as in the
endpoint-sandwich slice.

## Why the Hypothesis Is Needed

Componentwise vector bounds alone do not determine `H_ell`.  For example, take
two-coordinate vectors

```text
Tlo = (0, 100),    T = (0, 50),    Thi = (0, 100).
```

Then `Tlo <= T <= Thi`.  If the extremal endpoint is read from coordinate `1`
but the middle endpoint is read from coordinate `2`, then

```text
Htilde_ell = 0,
Htilde'_ell = 0,
H_ell = 50.
```

So the endpoint conclusion fails without a fixed endpoint coordinate or an
equivalent monotone endpoint functional.

## Lean Boundary

Lean now proves:

```text
same-coordinate vector bounds -> endpoint <= H_last <= endpoint,
same-coordinate vector bounds + selected-width sum -> H_last = 0,
```

and source-shaped wrappers feeding this into the existing finite Lemma 4 count
and Lemma 4-to-Lemma 3 free-count bridge.

It still does not prove:

- the full `Htilde` or `Htilde'` chains;
- a source-defined unique correspondence `T -> (H_j),(S_j)`;
- that Aoyagi's displayed `Ttilde <= T <= Ttilde'` supplies the
  same-coordinate hypotheses;
- the two-value increment hypothesis;
- vector admissibility or correspondence to `lambda`;
- Lemma 5 chart-family admissibility, coverage, and order count;
- normal crossings or RLCT extraction.

## Independent Checks

Xhigh source checker `Cicero the 5th` classified this as a source-gap slice:
Definition 4 alone gives componentwise order but not the endpoint-selection
map.  Cicero identified the same-coordinate projection as the conservative
formalizable statement and gave the two-coordinate counterexample above.

Xhigh Lean/API scout `Jason the 5th` confirmed that no A5 vector API already
exists and recommended a conservative wrapper using pointwise function order,
without importing the A4 blow-up scaffolding.

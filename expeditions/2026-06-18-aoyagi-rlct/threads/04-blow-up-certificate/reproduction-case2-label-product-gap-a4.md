# A4 Case 2 Label-Product Gap

Status: reproduced finite label-product calculation for the displayed Case 2
row-weight recurrence; independent xhigh check saved at
`review-case2-label-product-gap-a4.md`.

## Scope

This note refines the previous explicit `step k = 1` gap bridge. It models the
recurrence factor at level `r` as a finite product over supplied labels whose
level is `r`, then proves that a finite label gap makes those recurrence
factors equal to `1`.

This is still conditional. The finite label set is supplied as data; this note
does not prove that it is exactly Aoyagi's set of introduced labels at a
recursive state.

## Reproduction

Let `labels` be a finite set of labels used in a row-weight recurrence, with

```text
level : labels -> Nat,
var   : labels -> R.
```

Define the recurrence factor at level `r` by

```text
step_r = product over labels p with level(p)=r of var(p).
```

If no supplied label has level `r`, then this is the empty product, hence

```text
step_r = 1.
```

Assume the displayed Case 2 label gap:

```text
no supplied label p has J+1 <= level(p) < mu_S.
```

Then for every `r` in `J+1 <= r < mu_S`, the product defining `step_r` is
empty, so `step_r=1`. The previous gap-row-weight calculation applies:
for every displayed Case 2 residual row `i` with

```text
J+1 <= i <= mu_S,
```

we have

```text
b_i = b_(J+1).
```

After the displayed selected-entry substitution `D_J = u*A`, we absorb the
selected variable once into the row weights:

```text
newWeight_i = u * b_i.
```

Thus all displayed residual row weights are flat and equal to the pivot row
weight `u*b_(J+1)`.

## Lean Shape

Generic finite label-product API:

```text
levelProductStep
levelProductStep_eq_one_of_forall_ne
levelProductStep_eq_one_of_gap
```

Displayed Case 2 row-weight bridge:

```text
case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap
exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap
```

## Normalisation and Boundary Checks

- The supplied finite `labels` set must be the same set used in the recurrence
  factor. Lean does not prove it is Aoyagi's actual introduced-label set.
- Introduced labels are actual-width labels; do not replace the source label
  domain by prefix-width labels.
- Displayed Case 2 residual rows are `J+1..mu_S`, where
  `mu_S = prefixMinNat n S`.
- Displayed Case 2 residual columns remain actual-width columns
  `J+1..n_(S+1)`.
- The displayed pivot still requires `J+1 <= prefixMinNat n (S+1)`.
- The selected variable is counted once as `newWeight_i = u * oldWeight_i`.

## Reproduction Check

- Checker/path/verdict: xhigh Lean/API review and source/ledger fidelity review
  saved at `review-case2-label-product-gap-a4.md`; verdict is sound as a
  conditional finite-label bridge, with the caveats listed above.

## Kill Conditions

- The supplied finite label set omits a label with level in
  `J+1..mu_S-1`.
- The recurrence factor is not exactly the product over the same supplied label
  set.
- Row weights are not indexed by displayed source row levels.
- A later use silently swaps the prefix-minimum row range with the actual-width
  column range.
- The selected variable is counted both in the row weights and as an
  additional outside diagonal factor.
- The result is promoted from a conditional displayed row-weight bridge to a
  full Case 2 transition, chart-coverage theorem, coordinate-regularity/Jacobian
  theorem, exponent update, termination proof, normal-crossing certificate, or
  RLCT extraction.

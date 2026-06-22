# Reproduction - Definition 3 bridge to Lemma 4/Htilde arithmetic

Date: 2026-06-22.

Status: second A6 bridge slice, extended with count/formula handoff wrappers.
This is finite arithmetic only.

## Source Anchor

Aoyagi Definition 3 is on PDF pp. 8-9.  It supplies the selected-sum datum

```text
sum_{j=1}^{ell+1} M^(S_j) = ell*(M-1) + a
```

after introducing the ceiling integer `M` and residue `a`.

Aoyagi's Lemma 4/Lemma 5 arithmetic on PDF pp. 24-25 uses this selected-sum
identity to make the displayed terminal endpoint vanish and to run the
displayed `Htilde` chain calculations.

## Terminal Endpoint Check

The existing Lean terminal endpoint is

```text
Endpoint = sum_j m_j - (a*M + (ell-a)*(M-1)).
```

With the Definition 3 selected-sum identity,

```text
Endpoint
  = ell*(M-1) + a - (a*M + (ell-a)*(M-1)).
```

Since `a <= ell`,

```text
(ell-a)*(M-1) + a*(M-1) = ell*(M-1).
```

Thus

```text
Endpoint
  = ell*(M-1) + a - (ell*(M-1) + a)
  = 0.
```

This is exactly the existing theorem
`aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum`, now packaged as a
method on `AoyagiDefinition3CeilData`.

## Htilde Terminal Check

The existing lower and upper displayed chains already prove:

```text
Htilde_lower_last = Endpoint
Htilde_upper_last = Endpoint
```

under `a <= ell`.  Therefore the same Definition 3 datum gives both terminal
zeros.

The upper-chain penultimate endpoint also reuses the existing calculation:

```text
Htilde'_((ell-1)) = M - W_ell
```

where `W_ell` is the last selected width in zero-based Lean indexing.  This
needs both `1 <= a` and `a <= ell`, which are fields of
`AoyagiDefinition3CeilData`.

## Source-selected Inequality Boundary

Definition 3 contains more than the selected-sum datum.  Its strict selected
inequalities imply, for every selected width,

```text
m_i <= M - 1.
```

The Lean bridge does not store these inequalities in
`AoyagiDefinition3CeilData`; it requires the strict source-selected inequality
as a separate hypothesis:

```text
forall i, ell * m_i < sum_j m_j.
```

Under that additional hypothesis, existing Htilde APIs prove label bounds for
equation `(4)` and equation `(5)`.  The new bridge only repackages those
theorems through `AoyagiDefinition3CeilData`; it does not construct displayed
vectors or chart families.

## Count and Formula Handoff Check

Aoyagi Theorem 2 displays the pole-order symbol `theta` as

```text
a*(ell-a)+1.
```

The Lean Definition 3 package names this finite arithmetic expression
`theorem2OrderFormula`, not `theta`, because no pole-order interpretation is
proved in this file.

Existing A5 arithmetic has already proved the interval-size identity

```text
1 + sum_{j=1}^{ell-1} (intervalSize_j - 1) = a*(ell-a)+1
```

and the same identity for the cardinalities of the same-coordinate `Htilde`
interval value sets.  The A6 bridge substitutes the `aParam` field of
`AoyagiDefinition3CeilData`, so both finite counts rewrite to
`data.theorem2OrderFormula`.

At the terminal coordinate, the selected-sum identity makes both displayed
chains zero.  Therefore the same-coordinate terminal value set is `{0}`.  A
separately supplied terminal equality

```text
T(C.point ell - 1)=0
```

then fills the terminal Eq5-offset set into that same singleton.  This is only
terminal finite-set bookkeeping; it is not a terminal-minimum classifier.

## Local Eq3/Eq4 and Lemma 4 Handoff Check

The bridge now exposes the existing Lemma 4 count theorem through
`AoyagiDefinition3CeilData`, but it still requires both:

```text
Htilde_lower <= H <= Htilde_upper,
F_j in {M-1,M} for every j.
```

Thus Definition 3 data plus chain bounds do not by themselves prove Lemma 4's
two-value increment hypothesis.

For Lemma 5 equation `(4)`, the local arithmetic package is repackaged under
the strict source-selected inequalities and the local guards

```text
1 <= p, p+1 <= a, p <= ell-a.
```

For equation `(3)`, the bridge deliberately keeps the missing one-unit slack

```text
selectedWidth_0 + 2 <= M
```

as an explicit hypothesis, along with `a < ell` and the strict source-selected
inequalities.  This preserves the A5 obstruction: Eq3 slack is not forced by
Definition 3-shaped data alone.

## Lean Translation

The new Lean file is `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

It adds method-style wrappers on `AoyagiDefinition3CeilData`:

- `one_le_ell`;
- `one_le_aParam`;
- `terminalEndpoint_eq_zero`;
- `htildeLowerChain_last_eq_zero`;
- `htildeUpperChain_last_eq_zero`;
- `htildeLowerNat_last_eq_zero`;
- `htildeUpperNat_last_eq_zero`;
- `htildeUpperNat_pred_eq_sub_lastWidth`;
- `Hlast_eq_zero_of_htildeChainBounds`;
- `intervalSize_excess_sum_Icc_eq_theorem2OrderFormula`;
- `htildeIntervalValueSetNat_excess_sum_Icc_eq_theorem2OrderFormula`;
- `htildeIntervalValueSetNat_terminal_eq_singleton_zero`;
- `suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`;
- `lemma4_twoValueCount_of_htildeChainBounds`;
- `selectedWidth_le_pred_of_sourceSelectedInequality`;
- `htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality`;
- `lemma5Eq4_localData_of_sourceSelectedInequality`;
- `lemma5Eq5_labelBounds_of_sourceSelectedInequality`;
- `lemma5Eq3_localData_of_sourceSelectedInequality_and_slack`.

## Kill Conditions

- Do not read `AoyagiDefinition3CeilData` alone as the full Definition 3
  selection condition.
- Do not derive selected-width upper bounds without the strict selected-width
  inequality hypothesis.
- Do not use the label-bound wrappers as displayed-vector construction,
  vector admissibility, terminal-minimum classification, pole-order, normal
  crossings, or RLCT extraction.
- Do not use the Htilde terminal zero wrappers as a proof of Lemma 4's
  two-value increment hypothesis.
- Do not read the finite count/order-formula wrappers as a pole-order theorem.
- Do not drop the explicit Eq3 one-unit slack hypothesis.

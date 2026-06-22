# Reproduction - Definition 3 bridge to Lemma 4/Htilde arithmetic

Date: 2026-06-22.

Status: second A6 bridge slice.  This is finite arithmetic only.

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
- `selectedWidth_le_pred_of_sourceSelectedInequality`;
- `htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality`;
- `lemma5Eq5_labelBounds_of_sourceSelectedInequality`.

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

# Statement Card - A5 Lemma 5 Terminal Eq5 Gap

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5OffsetValueSet_eq_empty_of_terminal`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_terminal_offsets_ne_intervalValueSetNat_of_selectedSum`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedTerminalUpper_Eq5_offsets_eq_intervalValueSetNat`

## Claim

At the terminal coordinate `p=ell`, Eq5 has no strict offset values.  Under
Definition 3's selected-width sum, the terminal same-coordinate interval is the
singleton `{0}`.  Therefore Eq5 offsets alone do not fill the terminal
interval, while a separately supplied terminal-zero value, or equivalently a
supplied terminal upper-endpoint value under the selected-width sum, does fill
it.

## Inputs

- For the terminal interval singleton: `a<=ell` and the selected-width sum
  `sum m = ell*(M-1)+a`.
- For the supplied coverage wrapper: a supplied equality
  `T(C.point ell - 1)=0`.
- For the upper-endpoint form: a supplied equality
  `T(C.point ell - 1)=Htilde'_ell`.

## Proves

The Eq5 terminal-offset theorem proves:

```text
Eq5Offsets_ell = empty.
```

The terminal interval theorem proves:

```text
IntervalValueSet_ell = {0}.
```

The noncoverage theorem proves:

```text
Eq5Offsets_ell != IntervalValueSet_ell.
```

The supplied-terminal-zero wrapper proves:

```text
insert (T(C.point ell - 1)) Eq5Offsets_ell = IntervalValueSet_ell.
```

The supplied-upper wrapper proves the same equality from
`T(C.point ell - 1)=Htilde'_ell`.

## Does Not Prove

- Construction of the terminal-zero branch from Aoyagi's printed equations.
- Eq3, Eq4, or Eq5 source-label legality at the terminal endpoint.
- Terminal-label exactness, injection, back-to-label coverage, or absence of
  extra terminal minimizers.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF pp. 26-27, represented by the strict-offset
set; and the displayed terminal equality of the lower and upper Htilde chains
under Definition 3's selected-width sum.

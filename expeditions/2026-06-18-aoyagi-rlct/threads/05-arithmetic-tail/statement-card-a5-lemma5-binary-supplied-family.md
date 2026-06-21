# Statement Card - A5 Lemma 5 Binary Supplied Family

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryNonbaseFamily`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryNonbaseFamily.toAdmissibleNonbaseFamily`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.fullBranches`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.fullH`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.toAdmissibleFamily`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.fullBranches_card_and_fullBranch_twoValueCount`

## Claim

A supplied Lemma 5 branch family whose branches carry terminal binary
prefix-delta data can be converted into the existing supplied admissible-family
boundary.

For each nonbase branch, the binary supplied interface assumes:

```text
H_0 = m_0
H_ell = 0
Delta_r in {0,1}
value = H_j at the counted coordinate
```

The full binary family adds the analogous `baseH` data for the base branch.
Under `a<=ell` and the selected-width sum, Lean derives the previously supplied
fields:

```text
Htilde <= H <= Htilde'
F_r in {M-1,M}
```

and then reuses the existing full-branch count and per-branch two-value count.

## Inputs

- Existing supplied branch-value coverage/nonduplication fields from
  `AoyagiLemma5SuppliedNonbaseFamily`.
- Per-branch `H_0=m_0`, terminal `H_ell=0`, and binary prefix-delta
  hypotheses.
- For conversion: `ha : a <= ell` and
  `sum m = ell*(M-1)+a`.

## Proves

The conversion theorem builds:

```text
AoyagiLemma5SuppliedAdmissibleNonbaseFamily
AoyagiLemma5SuppliedAdmissibleFamily
```

from the binary supplied data.  The full-family wrapper proves:

```text
fullBranches.card = a*(ell-a)+1
```

and Lemma 4's finite two-value count for every tagged full branch after
conversion.

## Does Not Prove

- Construction of Aoyagi's displayed source vectors.
- That source vectors have binary prefix deltas.
- Source-label legality, terminal `tilde t=0`, or chart-family coverage.
- The Lemma 5 upper-bound classifier from terminal lambda-vectors.
- Pole order, normal crossings, or RLCT extraction.

## Source

This is finite assembly below Aoyagi Lemma 5's source classifier frontier.  It
uses the preceding binary-prefix arithmetic and does not add a new citation
boundary.

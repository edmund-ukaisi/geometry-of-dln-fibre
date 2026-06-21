# Statement card - A5 Lemma 5 equation (4) no terminal upper extension example

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_no_terminalUpperNatExtension_ell3_a2_p1_allWidthsTwo`

## Statement

Lean now records a concrete supplied-data incompatibility for equation `(4)`.

For

```text
ell=3, a=2, p=1, M=3, W_1=W_2=W_3=W_4=2,
```

any supplied equation `(4)` piecewise certificate rules out the supplied
terminal upper-chain extension

```text
T(S_(ell+1)-1) = Htilde'_ell.
```

In Lean notation this is

```text
T (C.point 3 - 1) != aoyagiHtildeUpperNat 3 2 3 (fun _ => 2) 3.
```

## Proved

- The closed selected-width tuple has terminal-collision index
  `p+(ell-a)+1=ell`.
- For any supplied equation `(4)` piecewise certificate with these constants,
  the last-width compatibility obstruction rules out the terminal upper-chain
  extension.

## Assumed

- A supplied equation `(4)` piecewise certificate for the concrete constants.

## Cited

- No Lean citation.  The source context is Aoyagi Lemma 5, PDF pp. 25-27; the
  Lean statement is finite endpoint arithmetic plus supplied-data
  compatibility.

## Deferred

- Construction or existence of equation `(4)`'s displayed vector.
- Construction of a terminal extension.
- Proof that Aoyagi's terminal convention follows from the printed branch
  certificate.
- Terminal `tilde t=0`, vector admissibility, source vector-to-chain
  correspondence, Case 1(2) chart sequence, Lemma 5 order count, pole order,
  normal crossings, and RLCT extraction.
- Compatibility between `layerWidth` and the selected widths.

## Review

- Source/API review passed by xhigh independent audit:
  `review-lemma5-eq4-no-terminal-upper-extension-example-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

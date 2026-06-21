# Statement card - A5 Lemma 5 equation (4) p=1 terminal extension obstruction

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_no_terminalUpperNatExtension_of_p1_sourceSelectedInequality`

## Statement

Lean now records a uniform `p=1` source-selected obstruction to adding a
terminal upper-chain extension in equation `(4)`'s terminal-collision case.

If a supplied equation `(4)` piecewise certificate has `p=1`, the
terminal-collision equality `1+1=a`, Definition 3's selected-sum identity, and
Definition 3's strict selected-width inequalities, then it cannot also satisfy

```text
T(S_(ell+1)-1) = Htilde'_ell.
```

In Lean notation:

```text
T (C.point ell - 1) != aoyagiHtildeUpperNat ell a M m ell.
```

## Proved

- A terminal upper-chain extension in the `p=1` terminal-collision case would
  force `W_(ell+1)=M`.
- Definition 3's strict selected-width inequality forces
  `W_(ell+1)<=M-1`.
- Hence the supplied equation `(4)` certificate and supplied terminal
  upper-chain extension are incompatible under these hypotheses.

## Assumed

- A supplied equation `(4)` piecewise certificate with `p=1`.
- The terminal-collision equality `1+1=a`.
- Definition 3's selected-sum identity.
- Definition 3's strict selected-width inequalities.

The supplied certificate includes `a<=ell`; together with `1+1=a`, this gives
`1<=ell` before applying the selected-width upper bound.

## Cited

- No external source beyond Aoyagi Lemma 5 and Definition 3.  The Lean
  statement is finite endpoint arithmetic plus supplied-data compatibility.

## Deferred

- Construction or existence of equation `(4)`'s displayed vector.
- Construction of a terminal extension.
- Proof that Aoyagi's terminal convention follows from the printed branch
  certificate.
- Terminal `tilde t=0`, vector admissibility, source vector-to-chain
  correspondence, Case 1(2) chart sequence, Lemma 5 order count, pole order,
  normal crossings, and RLCT extraction.

## Review

- Source/API review passed by xhigh independent audit:
  `review-lemma5-eq4-p1-terminal-extension-obstruction-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

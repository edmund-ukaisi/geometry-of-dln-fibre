# Statement card - A5 Lemma 5 equation (4) terminal extension forces p

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_terminalExtension_forces_two_le_p_of_sourceSelected`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_no_terminalExtension_of_sourceSelected_of_p_lt_two`

## Statement

Lean now records a general source-selected necessary condition for adding a
terminal upper-chain extension in equation `(4)`'s terminal-collision case.

If a supplied equation `(4)` piecewise certificate satisfies `p+1=a`,
Definition 3's selected-sum identity, Definition 3's strict selected-width
inequalities, and the supplied terminal upper-chain extension

```text
T(S_(ell+1)-1) = Htilde'_ell,
```

then Lean proves

```text
2 <= p.
```

Equivalently, under the same supplied-certificate and source-selected
hypotheses, if `p<2`, the supplied terminal upper-chain extension is
impossible.

## Proved

- A terminal upper-chain extension in the terminal-collision case forces
  `W_(ell+1)=M-p+1`.
- Definition 3's strict selected-width inequality forces
  `W_(ell+1)<=M-1`.
- Hence the supplied terminal upper-chain extension forces `2<=p`, and `p<2`
  rules it out.

## Assumed

- A supplied equation `(4)` piecewise certificate.
- The terminal-collision equality `p+1=a`.
- Definition 3's selected-sum identity.
- Definition 3's strict selected-width inequalities.
- For the positive theorem: the supplied terminal upper-chain extension.
- For the negative theorem: `p<2`.

The supplied certificate includes `a<=ell`; together with `p+1=a`, this gives
`1<=ell` before applying the selected-width upper bound.

## Caveat

The Lean theorem is stated for the totalized supplied-certificate API.  The
`p=0` edge is a Lean-totalized supplied-certificate consequence, not an
additional printed source case for Aoyagi's equation `(4)`.

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
  `review-lemma5-eq4-terminal-extension-forces-p-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

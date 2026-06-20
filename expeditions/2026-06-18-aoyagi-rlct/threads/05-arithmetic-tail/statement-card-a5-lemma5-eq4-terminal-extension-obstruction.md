# Statement card - A5 Lemma 5 equation (4) terminal extension obstruction

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary`

## Statement

Lean now records the compatibility forced by adding a supplied terminal
extension to the equation `(4)` terminal-collision case.

If a supplied equation `(4)` piecewise certificate is in the terminal-collision
case `p+1=a`, Definition 3's selected-sum identity holds, and a separate
terminal extension supplies

```text
T(S_(ell+1)-1) = Htilde'_ell,
```

then Lean proves

```text
W_(ell+1) = M - p + 1.
```

Equivalently, if this last-width condition fails, then the supplied equation
`(4)` branch certificate cannot also satisfy that terminal extension.

## Proved

- Terminal extension plus terminal-collision branch value forces the
  last-width compatibility `W_(ell+1)=M-p+1`.
- Failure of that compatibility rules out the supplied terminal extension.

## Assumed

- A supplied equation `(4)` piecewise certificate.
- The terminal-collision equality `p+1=a`.
- Definition 3's selected-sum identity.
- For the positive theorem: a supplied terminal extension
  `T(S_(ell+1)-1)=Htilde'_ell`.
- For the negative theorem: failure of the last-width compatibility.

## Cited

- None in Lean.  This is finite endpoint arithmetic and supplied-data
  compatibility.

## Deferred

- Construction or existence of equation `(4)`'s displayed vector.
- Proof that Aoyagi's terminal convention follows from the printed branch
  certificate.
- Terminal `tilde t=0` without an explicitly supplied extension.
- Source vector-to-chain correspondence, vector admissibility, Case 1(2) chart
  sequence, Lemma 5 order count, pole order, normal crossings, and RLCT
  extraction.

## Review

- Source/API review passed by xhigh `Pascal`:
  `review-lemma5-eq4-terminal-extension-obstruction-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

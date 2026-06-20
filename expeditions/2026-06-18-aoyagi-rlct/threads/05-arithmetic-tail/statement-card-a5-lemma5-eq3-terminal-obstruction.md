# Statement card - A5 Lemma 5 equation (3) terminal obstruction

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_terminalEndpoint_one_of_one`

## Statement

For a supplied Aoyagi Lemma 5 equation `(3)` branch certificate with `a=1`,
Definition 3's selected-sum identity implies

```text
T(S_(ell+1)-1) = 1.
```

Thus equation `(3)` cannot itself be used as a uniform terminal-endpoint-zero
theorem.

## Proved

- The special equation `(3)` boundary is the terminal selected endpoint when
  `a=1`.
- Under the selected-sum identity, the supplied boundary assignment gives value
  `1` there.

## Assumed

- A supplied equation `(3)` piecewise branch certificate.
- The selected-sum identity with `a=1`.

## Cited

- None in Lean.  This is finite endpoint arithmetic.

## Deferred

- Construction or existence of the displayed vector.
- Any terminal `tilde t=0` theorem.
- Case 1(2) chart sequence, introduced-label status, vector admissibility,
  Lemma 5 order count, normal crossings, and RLCT extraction.

## Review

- xhigh `Boyle` passed the theorem as source-faithful:
  `review-lemma5-eq3-terminal-obstruction-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

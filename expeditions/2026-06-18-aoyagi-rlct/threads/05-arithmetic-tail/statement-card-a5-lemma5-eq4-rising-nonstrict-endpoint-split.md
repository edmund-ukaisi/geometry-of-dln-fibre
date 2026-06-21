# Statement card - A5 Lemma 5 Eq4 rising non-strict endpoint split

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_risingNonStrictEndpoint_iff_predBoundary_or_eq_a`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryIndex_not_lt_ell_iff_predBoundary_or_eq_a`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_risingNonStrictEndpoint_predBoundary_or_no_piecewiseSourceVector`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4TerminalCollisionPayload`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4GuardFailurePayload`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_risingNonStrictEndpoint_split`

## Statement

In the rising range `p<=a`, failure of the strict Eq4 endpoint case

```text
p+1 < a
```

splits into exactly two boundary forms:

- terminal collision `p+1=a`;
- repaired-guard failure `p=a`.

The displayed split packages existing consequences:

- in the terminal-collision branch, every supplied Eq4 piecewise certificate
  has its special boundary at the terminal selected endpoint, outside all
  half-open blocks, and terminal zero is equivalent to the last-width
  compatibility condition;
- in the guard-failure branch, Eq5 retains the rising erased-endpoints deficit
  and no repaired Eq4 piecewise certificate of the fixed shape exists.

## Proved

- The pure Nat split and its raw boundary-index alias.
- A lightweight displayed dispatcher:
  `p+1=a` or `p=a` plus no repaired Eq4 piecewise certificate.
- A richer endpoint inventory payload separating terminal-collision
  consequences from guard-failure consequences.

## Assumed

- Rising hypotheses for the richer payload: `a<=ell`, `1<=p`, `p<=a`,
  `p<=ell-a`.
- Selected-width sum for the terminal zero iff in the terminal-collision
  branch.
- Supplied Eq4 piecewise certificate only inside the conditional
  terminal-collision payload.

## Cited

- None in Lean.  This is finite endpoint arithmetic and packaging from
  existing formalised Eq4/Eq5 boundary facts.

## Deferred

- Eq4 displayed-vector construction, source coverage, terminal zero,
  source-label legality, classifier/injection/back-to-label coverage, Lemma 5
  order count, pole order, normal crossings, and RLCT extraction.

## Review

- xhigh Lean scout `Jason` recommended the non-strict split as the genuinely
  new API point.
- xhigh hardener `McClintock` accepted the slice only as endpoint bookkeeping
  and warned that the terminal-collision branch is conditional/vacuous if no
  Eq4 certificate is supplied.

## Verification

- From `lean/`: `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`

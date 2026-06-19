# Statement card - A4 Case 1 displayed row-strip new-label exponent

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`549785b7e479cfd2682fbf160527787becfd3105`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.displayedRowStrip_newLabelExponentCertificate`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripExponentPostData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.extendDomain_case1DisplayedRowStripNewLabel_of_postData`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripExponentPostData.updateNewLabel`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.extendDomain_case1DisplayedRowStripNewLabel_updateData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.extendDomain_case1DisplayedRowStripNewLabel_of_levelTailInvariants`

## Statement

Lean now records the conditional exponent-domain extension for Aoyagi
Case 1(2)'s displayed row-strip new label `(S,J+1)`.

Given an old selected label `(s0,k0)` at level `J+J1`, an old label
certificate, a supplied `leastValue=level` bridge, and a supplied flat-tail
invariant, the fresh label receives:

```text
t'_(S,J+1) = lowerTailVector (t_(s0,k0)) S J,
numerator'_(S,J+1)
  = numerator_(s0,k0) + J1 * (n_(S+1) - J),
leastValue'_(S,J+1) = J.
```

The new label is introduced at the post-state `(S,J+1)` under the actual-width
bound `J+1 <= n_(S+1)`. All labels already introduced at `(S,J)` are
preserved by supplied post-data, or by the concrete update-data wrapper that
changes only the fresh label.

## Source Role

Aoyagi prints this Case 1(2) new-label data after factoring the old selected
variable as `u_(s,k)=u_(S,J+1)u'_(s,k)`. The exponent increment uses the
actual reduced width `M^(S+1)`, represented in Lean by `n (S+1)`.

## Proved

- The lower-tail vector for the old selected label gives a one-label
  certificate for the fresh label `(S,J+1)`.
- The post-state introduced-label proof uses actual width, not prefix width.
- A supplied post-data package extends all introduced-label exponent
  certificates from `(S,J)` to `(S,J+1)`.
- Concrete update data changing only `(S,J+1)` satisfies the post-data package.
- The level/tail invariant package discharges the selected old
  least-value/flat-tail hypotheses.

## Assumed

- The old selected label certificate is already present.
- `leastValue s0 k0 = level s0 k0`.
- `FlatTailFromPred L S (t s0 k0) (level s0 k0)` is supplied.
- `2 <= S`, `S <= L`, and `J+1 <= n(S+1)`.
- The chart produces the supplied post-data.

## Not Proved

- No selected-entry chart construction or chart coverage.
- No proof that Aoyagi's displayed chart produces these post assignments.
- No recurrence production or resolution of the `b'_i` normalization ambiguity.
- No hidden old-label source-validity production.
- No chart regularity, transition regularity, or Jacobian formula.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-displayed-row-strip-new-label-exponent-a4.md`.
- Review artifact:
  `review-case1-displayed-row-strip-new-label-exponent-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From the worktree root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory found no Lean forbidden-token use; hits are existing prose
  mentions in expedition notes and statement cards.

# Statement cards

A **statement card** links a formalised claim to its Lean theorem in markdown,
replacing LaTeX `\leanref` (the paper is a separate write-up downstream). The card
is the surface a human reviewer reads to confirm the Lean says what the claim says.

## Shape

Place the card next to the claim in the expedition or theory markdown:

```
> **Claim.** <one-line statement, hypotheses named>
>
> - **Lean:** `DLNFibre.Core.Orbit.orbit_eq_iff_kostant_eq`
>   (`lean/DLNFibre/Core/Orbit.lean` @ `<commit-sha>`)
> - **Gloss.** <plain-English reading of the Lean signature>
> - **Proved.** <what the Lean establishes unconditionally>
> - **Assumed.** <hypotheses the statement carries that the informal claim also needs>
> - **Cited.** <anything used from an external source, not reproved here — or "none">
> - **Deferred.** <the reduction/step the impressive reading needs but that is NOT done — or "none">
> - **Status.** sorry-free / sorry-free + reviewed
```

## Rules

- **Pin the commit SHA**, not a line number — line numbers rot. Bump the SHA when
  the statement changes.
- The **gloss** restates the Lean signature in words so a reviewer who does not read
  Lean can check fidelity against the claim.
- The card is created at the formalisation thread's AUDIT step and updated to
  `reviewed` when a reviewer confirms fidelity.
- The **Proved / Assumed / Cited / Deferred** split is the precision discipline
  ([`precision.md`](precision.md)): the headline (and the Lean name) state only what is **Proved**;
  anything **Deferred** is named, never omitted.

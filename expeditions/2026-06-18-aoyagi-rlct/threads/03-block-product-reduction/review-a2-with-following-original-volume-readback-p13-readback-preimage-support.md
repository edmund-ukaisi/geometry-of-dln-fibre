# Review - A2 with-following original-volume readback p.13/readback-preimage support

Date: 2026-07-07.

Reviewer: xhigh read-only agent `Chandrasekhar the 2nd`.

## Verdict

Pass after documentation status fix.

The original review returned `FAIL, documentation-only` because the statement
card still said `Status: Planned` after the theorem had been implemented and
checked.  The Lean theorem and reproduction boundary passed the audit.

## Checked

- The raw-pushforward equality remains a hypothesis, so the theorem does not
  prove raw-Haar transport.
- The theorem exposes only the local equality
  `sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V`, not global source-image
  coverage.
- The shrink logic is sound: `W` comes from the p.13/readback local equality,
  `V ⊆ W` comes from the existing original-volume readback bridge, and the
  domination is composed from `thetaReference.restrict W` to
  `thetaReference.restrict G`.
- The support conversion is exactly the intended set bookkeeping via
  `sourceChart_image_eq_p13_readback_preimage_of_subset` and
  `chartPiece_subset_sourceChart_image_of_subset_p13_readback`.

## Checks

The reviewer independently observed:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

passing from `lean/`, and an axiom probe for the new theorem reporting only
`[propext, Classical.choice, Quot.sound]`.

## Required Fix

Update the statement-card status from `Planned` to `Implemented/proved` and
record the focused Lean and axiom checks.

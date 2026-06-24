# Review - A4 Case 2 transition-generated substitution-block rewrite

Date: 2026-06-24.

Reviewer: `Godel the 2nd`, xhigh-effort independent subagent.

Status: pass.  No blocking findings.

## Scope

Reviewed the uncommitted finite substitution-block rewrite:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- `reproduction-case2-transition-generated-substitution-block-rewrite-a4.md`;
- `statement-card-a4-case2-transition-generated-substitution-block-rewrite.md`.

The review checked statement fidelity, denominator hypothesis,
arbitrary-versus-displayed scope, and overclaim risks.

## Findings

No blocking formalisation or mathematical issues were found.

The denominator hypothesis is correctly the source-normalized target
coordinate

```text
case2SourceSelectedNormalizedMapOfMem hsource residual targetPivot != 0
```

not `(u * denom) != 0`; no `u != 0` hypothesis is introduced.

The theorem proves substitution-block equality only.  It does not prove
normalized-block equality, a target Schur-complement or `Q/P` reduced-block
rewrite, analytic transition regularity, source production, normal crossings,
pole order, or RLCT extraction.

The arbitrary target-pivot theorem is the finite all-pivot selected-entry
abstraction.  The displayed pivot is the directly Aoyagi-facing special case.

## Non-Blocking Repairs Applied

- Mirrored the arbitrary-pivot versus displayed-pivot caveat in the thread
  summary.
- Reworded the statement-card verification section so the targeted build is
  not tied to pre-review provenance.

## Gates

Passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The full `DLNFibre` build completed with pre-existing Core/style warnings
outside this slice.

## Minimal Repair

None required.

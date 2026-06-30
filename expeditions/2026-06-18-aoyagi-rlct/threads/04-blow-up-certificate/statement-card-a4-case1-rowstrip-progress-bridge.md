# Statement card - A4 Case 1(2) row-strip progress bridge

Date: 2026-06-30.

## Statement

Add a generic same-stage introduced-label progress alias and a Case 1(2)
row-strip payload bridge:

```text
AoyagiIntroducedLabelBranchState.progressStep_sameStage_increment
AoyagiIntroducedLabelBranchState.progressStep_case1DisplayedRowStrip_jIncrementPayload
```

The Case 1(2) bridge consumes only
`Case1DisplayedRowStripJIncrementPayload` and proves the introduced-label
progress step

```text
(S,J) -> (S,J+1).
```

## Source Reference

Aoyagi PDF pp. 16-18 for Case 1(2), where `u_(s,k)` is factored by the fresh
new variable `u_(S,J+1)` and the continuation branch advances `J` by one.

The exclusion of Case 1(1) is source-critical: PDF p. 16 treats Case 1(1) as a
same-domain selected-old lowering step with a different progress count.

## Dependencies

- `Case1DisplayedRowStripJIncrementPayload`
- `AoyagiIntroducedLabelBranchState.progressStep_case2_increment`

The dependency on the older `case2`-named theorem is only the generic finite
same-stage support-growth calculation; the new public alias is named by its
actual content.

## Assumptions Kept Explicit

- supplied Case 1(2) row-strip payload;
- actual-width validity of the fresh label `(S,J+1)` from that payload.

## Nonclaims

No Case 1(1) progress theorem, chart construction, post-state construction,
source production, full branch termination, normal crossings, pole order, or
RLCT is proved.

## Reproduction and Review

Reproduction:

```text
threads/04-blow-up-certificate/reproduction-a4-case1-rowstrip-progress-bridge.md
```

Review:

```text
threads/04-blow-up-certificate/review-a4-case1-rowstrip-progress-bridge.md
```

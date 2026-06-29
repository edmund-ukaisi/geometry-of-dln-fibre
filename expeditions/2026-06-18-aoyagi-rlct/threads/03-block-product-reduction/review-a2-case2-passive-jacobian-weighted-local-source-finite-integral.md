# Review - A2 Case 2 Passive Jacobian-Weighted Local-Source Finite Integral

Date: 2026-06-29.

Status: PASS.

## Reviewed Artifacts

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/reproduction-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md
expeditions/2026-06-18-aoyagi-rlct/threads/03-block-product-reduction/statement-card-a2-case2-passive-jacobian-weighted-local-source-finite-integral.md
```

## Lean/API Review

Reviewer: Erdos the 3rd, xhigh read-only.

Verdict: PASS.

Findings:

- The theorem's `muJ` is exactly the reproduced measure: restrict the passive
  product-domain measure to `Udom`, weight by the formal raw-order Jacobian
  factor, and push forward by `sourceChart`.
- The final integral is only over
  `(muJ.restrict (U inter sourceStratum)).prod nu`.
- `localSource` and `sourceStratum` match the reproduction: identity `Cedge`,
  retained-passive local source, and fixed-base source-rank stratum.
- The exponent/sign is the expected
  `-(t + aoyagiTheorem2RegularVariableCount 2 H r / 2)`, with residual
  integrability consumed at exponent `-t`.
- The s-finiteness handoff is explicit: finite passive mass installs
  `IsFiniteMeasure passiveMeasure`, and `SFinite muJ` is inferred before the
  generic local-source finite-integral theorem is applied.
- No hidden source-prior, Haar, or raw-source theorem is used; the proof
  consumes the residual-source package and the generic retained-passive
  local-source handoff.

No Lean/API findings were reported.

## Scope Review

Reviewer: Lovelace the 3rd, xhigh read-only.

Verdict: PASS.

Findings:

- The theorem name and statement match the chart-produced
  Jacobian-weighted finite-integral handoff and do not claim a source-prior or
  source-image result.
- The two-neighborhood structure is correct: `Udom` is a source-domain
  neighborhood of `z0`; the inner `U` is an edge-family neighborhood of the
  fixed base.
- The local loss and density hypotheses are stated over
  `nhdsWithin base localSource`, matching the generic retained-passive
  local-source consumer.
- Finite passive mass is used only for measure-class bookkeeping, not as a
  substitute for source-prior transport.
- The theorem docstring and statement card keep the nonclaim boundary explicit.

No scope findings were reported.

## Controller Resolution

No Lean or documentation repairs were required after review.

Verification completed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
scripts/lb DLNFibre
git diff --check
scripts/sorries
direct #print axioms probe
```

`scripts/sorries` reports `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probe for the new theorem reports
`[propext, Classical.choice, Quot.sound]`.

Nonclaim boundary remains: no exact localized residual marginal,
determinant-chart Haar pushforward, raw/source Haar theorem, original
source-prior transport, source-prior Jacobian formula, source-image equality,
local coverage, normal crossings, pole order, or RLCT.

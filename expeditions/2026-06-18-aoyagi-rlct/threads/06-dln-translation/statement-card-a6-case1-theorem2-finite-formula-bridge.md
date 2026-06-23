# Statement card - A6 Case 1 to Theorem 2 finite formula bridge

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Case1Theorem2FiniteExponentBridge.lean`

Names:

- `Case1SelectedEntryA0ExponentCoordinateBridge.theorem2CandidateRatio`
- `Case1SelectedEntryA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData`
- `Case1SelectedEntryA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`
- `Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2CandidateRatio`
- `Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData`
- `Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`

## Claim

Given a supplied Case 1 selected-entry A0 coordinate bridge, the candidate
ratio

```text
(1 + J1 * (n (S + 1) - J)) / 2
```

fills the finite Theorem 2 exponent-formula boundary once the following are
supplied:

- a global active-ratio lower bound by this candidate;
- an equality identifying this candidate with
  `aoyagiTheorem2Lambda_fromCeilData`;
- either a raw exponent-order equality or chart-count witnesses at this
  candidate ratio.

## Inputs Kept Explicit

- supplied finite exponent data `D`;
- supplied coordinate `p`;
- supplied Case 1 coordinate bridge `B`;
- supplied active-ratio lower bound;
- supplied candidate-ratio/Theorem 2 lambda equality;
- supplied order equality, or supplied chart-count equality and all-chart
  upper bound.

## Proved

The theorem constructs

```text
AoyagiTheorem2FiniteExponentFormulaHypothesis D Lthm ell H r m data.
```

The selected-old wrapper version preserves the
`Case1SelectedOldUnitSuppliedChartFamilyBoundary` provenance carried by `B`.

## Not Proved

No construction of `D`, no construction of `p`, no global lower-bound proof,
no candidate-ratio/lambda equality proof, no chart-count proof, no
selected-width provenance, no chart production, no analytic extraction, no
pole order, and no RLCT.

## Verification

Initial focused check passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Case1Theorem2FiniteExponentBridge
```

Independent xhigh review passed:
`review-case1-theorem2-finite-formula-bridge-a6.md`.

Focused and full checkpoint gates passed and are recorded in the review
artifact.

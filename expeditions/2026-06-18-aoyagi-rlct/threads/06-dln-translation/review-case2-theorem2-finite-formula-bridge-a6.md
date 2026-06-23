# Review - Case 2 to Theorem 2 finite formula bridge

Date: 2026-06-23.

Status: xhigh source/math and Lean/API reviews passed.

## Reviewed Artifact

- `lean/DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean`
- `reproduction-case2-theorem2-finite-formula-bridge-a6.md`
- `statement-card-a6-case2-theorem2-finite-formula-bridge.md`

Lean name reviewed:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData
```

## Source/Math Review

Reviewer: `Raman the 2nd`.

Verdict: pass; no required fixes.

The reviewer confirmed that this is the right bounded finite-bookkeeping slice
provided it remains conditional.  The hypotheses that must stay explicit are:
the supplied Case 2/A0 coordinate bridge, the global active-ratio lower bound,
the equality identifying the Case 2 center-cardinality ratio with Theorem 2's
displayed lambda formula, the supplied order equality, and the Definition 3
ceiling data.

The reviewer confirmed fidelity to Aoyagi pp. 5-6 only at the finite
normal-crossing interface level: the theorem uses the active ratio minimum and
does not claim the analytic extraction theorem.  Fidelity to Theorem 2 is also
conditional because the displayed lambda and order formulas enter as supplied
equalities.

## Lean/API Review

Reviewer: `Dirac the 2nd`.

Verdict: pass; no required fixes.

The reviewer confirmed that the clean placement is a separate optional bridge
module importing `Case2FiniteExponentBridge` and `Theorem2FiniteExponentBridge`.
The imports are acyclic, the Case 2 certificate level and Theorem 2 formula
level must stay separate, and the proof is routine: use the Case 2 supplied
minimum theorem, rewrite by the supplied center-cardinality/lambda equality,
and fill the order field with the supplied order equality.

## Verification

Focused and full gates passed:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Case2Theorem2FiniteExponentBridge
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build reported only pre-existing Core linter warnings.

## Boundary

This review does not certify construction of the A0 exponent data `D`, the
coordinate `p`, active-ratio lower bounds, the center-cardinality/Theorem 2
lambda equality, the order equality, selected-width provenance, chart
production, analytic normal-crossing chart data, pole order, or RLCT
extraction.

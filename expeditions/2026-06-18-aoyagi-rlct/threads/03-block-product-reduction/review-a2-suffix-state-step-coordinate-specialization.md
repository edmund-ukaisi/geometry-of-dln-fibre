# Review - A2 suffix-state step coordinate specialization

Reviewer: Harvey the 4th, xhigh-effort subagent.

## Verdict

Pass.  No blocking findings.

## Findings

The two wrappers

```text
ChartLocalSuffixState.suffixState_stepRawCoordinates_triangularBlockProduct
ChartLocalSuffixState.suffixState_stepRawCoordinates_productDifference
```

have the correct product orientation.  The middle product is

```text
P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj),
```

and `hsuccRight` rewrites it as `P p.succ j hpj * E p` for the generic
adapter.  The transformed edge is used only as the source of the raw
coordinate corners.

The block dimensions match the p. 13 calculation: the left multiplier acts on
`rho ⊕ kappa j`, the right multiplier acts on
`rho ⊕ kappa p.castSucc`, and both lower-right terms `y.D * y.C` and
`y.F3 * y.F2` land in `Matrix (kappa j) (kappa p.castSucc) K`.

The statements stay inside finite block algebra.  They assume the local
block-diagonal invariant and the determinant chart for the transformed edge;
they do not assert analytic chart status, chart coverage, ideal transport,
normal crossings, pole order, or RLCT.

## API Note

The existential `F3prev` chosen via
`suffixState_L_eq_lowerUnitriangular` is mathematically acceptable.  A future
canonical convenience wrapper with

```text
F3prev = lowerLeftBlock (suffixState E j p.succ hpj).L
```

may be useful if downstream code needs the prior lower-left coefficient by
name rather than through an existential witness.

`hS : BlockDiagonal` includes more data than these proofs use, but it is the
right consumer-facing invariant for this layer.

## Verification

The controller ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
```

The reviewer separately checked only this file with Lean from the Lean project
root.

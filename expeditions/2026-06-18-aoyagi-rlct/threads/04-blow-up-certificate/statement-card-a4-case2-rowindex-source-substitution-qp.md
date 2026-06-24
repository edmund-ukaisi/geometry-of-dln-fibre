# Statement card - A4 Case 2 row-index source-substitution Q/P bridge

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `exists_case2DisplayedQP_mul_sourceSubstitution_of_rowIndex_monomialRec`
- `exists_case2DisplayedQP_verticalBlock_sourceSubstitution_of_rowIndex_monomialRec`

## Claim

The displayed Case 2 `Q/P` identity holds in source-substitution form when old
row weights are `monomialRec step rowLevel`; the vertical-block wrapper lifts
the residual-tail identity through unchanged top rows.

## Source Role

This connects Aoyagi's displayed source substitution, transported following
factor `Q^{-1} C`, and `P` quotient witnesses in the row-index monomial
recurrence presentation.

## Inputs Kept Explicit

- displayed Case 2 pivot assumptions `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`;
- row weights in the form `monomialRec step (case2ResidualRowLevel ...)`;
- selected variable `u`;
- residual block and following factor.

## Not Proved

No arbitrary-pivot theorem, source-produced recurrence weights, source
production of `C'^(S+1)`, terminal product, transition invariant, analytic
chart coverage, Jacobian/volume theorem, analytic/global normal-crossing
certificate, pole order, or RLCT.

## Verification

Focused check passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
```

Full gate passed with pre-existing unrelated warnings:

```text
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.

Xhigh independent review passed with no blocking findings.  Durable artifact:
`review-case2-all-pivot-and-rowindex-source-bridges-a4.md`.

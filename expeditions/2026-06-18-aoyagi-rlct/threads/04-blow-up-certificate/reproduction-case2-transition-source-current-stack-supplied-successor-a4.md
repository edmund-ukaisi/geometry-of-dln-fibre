# Reproduction - A4 Case 2 transition source-current stack supplied successor

Date: 2026-06-24.

Status: pen-and-paper reproduced; formalisation in progress.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The continuing branch rewrites the displayed
`Q/P` calculation into a source-current row stack, multiplies by the source
suffix, and then advances from `J` to `J+1`.

This note records only the finite transition-plus-consumer wrapper on an
overlap between an arbitrary selected-entry source chart and Aoyagi's displayed
top-left chart.

## Reproduction

Let `p` be the arbitrary selected-entry source pivot and let the displayed
target pivot be

```text
q = (J+1,J+1).
```

Write the source normalized coordinates as

```text
x_r = case2SourceSelectedNormalizedMapOfMem p_mem residual r
d   = x_q.
```

On the displayed overlap assume

```text
d != 0.
```

The transition-generated displayed target data are

```text
targetU          = u*d,
targetResidual_r = x_r/d.
```

The displayed substitution block at the target data is entrywise the original
source selected-entry substitution block:

```text
DisplayedSub(targetU,targetResidual)
  = Sub_q(u*d,x/d)
  = Sub_p(u,x).
```

At the pivot this says `(u*d) = u*x_q`; off the pivot it says
`(u*d)*(x_r/d) = u*x_r`.

Now suppose the transition-generated displayed target data carry a supplied
source-production obligation

```text
ob : SourceProductionObligation data targetResidual ... C Ctail Csucc Cterm.
```

This obligation supplies the same successor following object used by the
source-current stack consumer:

```text
Csucc =
  case2DisplayedSourceSuccessorFollowingFactor
    n data.stage_pos data.continuation targetResidual C.
```

Applying the supplied-block source-current stack consumer with

```text
B = Sub_p(u,x)
```

and the transition substitution-block equality gives the continuing
source-current stack with the source-side lower-left block written as
`Sub_p(u,x)` and the right side written with the supplied `Csucc`.

The row-operation witness, suffix product, corrected exponent data, level
data, least-value gap, and Case 2 gap are exactly those inherited from the
existing supplied-obligation stack theorem.  The center membership,
divisibility, and principalization outputs are still for the transition target
displayed coordinates `(targetU,targetResidual)`.

## Lean Target

Add a theorem in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`, next to the
existing supplied-successor transition reindexed-product wrapper.

Planned name:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.
  sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero
```

Inputs kept explicit:

- source chart, source coordinates `(u,residual)`, and displayed-overlap
  nonzero hypothesis;
- target displayed data `targetU` and `targetResidual`, with equations
  `targetU = u*d` and `targetResidual r = x_r/d`;
- continuing guard `J+2 <= prefixMinNat n (S+1)`;
- displayed supplied boundary `data` for `targetU`;
- `SourceProductionObligation data targetResidual ... C Ctail Csucc Cterm`;
- suffix index family, suffix matrices, supplied `Csucc`, and `Cterm`.

Conclusion:

- displayed target chart-map equality back to the source chart point;
- displayed target substitution block equals the original source selected
  block;
- the full continuing source-current stack package from
  `continuing_sourceCurrentStack_suppliedCsucc_of_substitutionBlock_eq`,
  instantiated with the original source selected substitution block.

## Boundary

- Only the lower-left substitution block is rewritten to source data.
- The post-pivot residual block, Schur block, target weights, and target
  successor formula remain target-displayed data.
- The post state is `pre.case2Succ targetU`, not `pre.case2Succ u`.
- The obligation, `Csucc`, `Cterm`, suffixes, and successor charts remain
  supplied.
- This proves no source production, transition regularity, chart coverage,
  analytic Jacobian/volume theorem, normal crossings, pole order, termination,
  or RLCT extraction.
- Aoyagi prints the displayed chart; the arbitrary all-pivot source chart is
  the finite wrapper used by this Lean development.

## Kill Conditions

- If the denominator becomes `targetU` or requires `u*d != 0`, stop.
- If `ob` is for the source residual rather than `targetResidual`, stop.
- If `data` is for source `u` rather than target `targetU`, stop.
- If the theorem constructs `SourceProductionObligation`, `Csucc`, `Cterm`,
  suffixes, or successor charts, weaken or rename it.
- If the Schur or post-pivot residual block is rewritten to source data, stop.
- If the continuing guard is omitted or terminal cases are folded in, stop.

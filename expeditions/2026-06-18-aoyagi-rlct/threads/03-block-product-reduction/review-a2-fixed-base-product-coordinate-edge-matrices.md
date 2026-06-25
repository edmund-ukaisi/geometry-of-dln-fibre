# Review - A2 fixed-base product-coordinate edge matrices

Date: 2026-06-25.

Scope: finite matrix algebra and fixed-base coordinate readout for raw p.13
product-coordinate edge matrices.

## Verdict

Pass at the stated finite scope.

The sign check is consistent with the existing suffix-state recursion.  The
key invariant is that raw middle and left edge matrices become the displayed
transformed-edge shapes only after the suffix tail has already produced
`B=0`.  The new Lean theorem
`ChartLocalSuffixState.suffixState_tail_fields_of_productCoordinateEdges`
records that induction explicitly.

## Independent Checks

Read-only xhigh check by Laplace the 5th:

- confirmed the right endpoint `[I,0;-F3,C]` starts the `F3` field with the
  correct sign;
- confirmed middle edges require the carried `B=0` invariant;
- confirmed the left endpoint gives `S.B=-F2`, `S.Ctop=Ctop`, and
  `L=[I,0;F3,I]`;
- confirmed the single-edge Schur residual is `C0`.

Read-only xhigh check by Ptolemy the 5th:

- recommended keeping the matrix-pattern API near `transformedEdge`;
- warned not to reintroduce a fully parameterized wrapper unfolding the large
  coordinate map;
- emphasized the multi-edge caveat that raw matrices are not transformed
  matrices unless the accumulated `B` field is controlled.

## Boundaries

The proof is pointwise finite algebra.  It does not construct the final
parameterized product-coordinate family `G(x,u)`, prove continuity of such a
family, prove source-rank coverage, construct a product chart, transport
measure/density, produce normal crossings, prove pole order, or extract RLCT.

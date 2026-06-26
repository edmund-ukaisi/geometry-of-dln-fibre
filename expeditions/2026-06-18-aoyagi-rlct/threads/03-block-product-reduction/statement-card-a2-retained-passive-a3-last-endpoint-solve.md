# Statement Card - A2 retained-passive `A3_last` endpoint solve

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last_eq_of_A3_eq_neg_target_mul_Ctop
```

## Reproduction

```text
reproduction-a2-retained-passive-a3-last-endpoint-solve.md
```

## Review

```text
review-a2-retained-passive-a3-last-endpoint-solve.md
```

## Claim

For a nonempty retained-passive edge family, the explicit product-tail sum at
the final edge unfolds to the final `A3` contribution:

```text
Tail_lastEdge = -(I * A3_last * Ctop_last^-1).
```

If `det(Ctop_last)` is a unit and

```text
A3_last = -G * Ctop_last,
```

then Lean proves

```text
Tail_lastEdge = G.
```

## Method

The proof uses:

- the recursive product-tail unfolding at `Fin.last M`;
- terminal successor tail `0`;
- terminal residual product `I`;
- `Matrix.mul_nonsing_inv Ctop_last` under `IsUnit Ctop_last.det`;
- associativity, one-multiplication, and double-negation.

## Role

This is the local endpoint cancellation needed for the retained-passive
coordinate inverse.  The later full theorem should instantiate `G` as the
desired active `F3_0` plus the unsigned earlier-edge prefix contribution.

## Nonclaims

No retained-passive coordinate-domain theorem is proved.  No prefix `G`
construction, open-domain proof, source-rank coverage, source/image equality,
measure pushforward, density/Jacobian theorem, normal crossings, pole order, or
RLCT extraction is proved.

Lean's matrix inverse is total; analytic/chart uses must carry determinant-unit
facts for the relevant `Ctop` block.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

This focused check passed on 2026-06-26 before review and again during xhigh
review.  The controller also ran `scripts/sorries`, `git diff --check`, and the
full `DLNFibre` build before the checkpoint commit; the full build still emits
pre-existing warnings outside the touched Aoyagi module.

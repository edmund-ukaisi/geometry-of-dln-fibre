# Statement Card - A6 Definition 3 equal-width Theorem 2 formula

## Lean Files

- `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`
- `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

## Claim

Lean proves the finite Theorem 2 formula package for the source-backed
equal-width Definition 3 branch.  If all source-range reduced widths are the
same Nat value `w`, and `w = L*q+a` with `0<a<=L`, then the consecutive
selected cutpoints with `ell=L` have explicit ceiling data, order formula,
selected pair sum, and unfolded finite lambda formula.

## Lean Names

```text
aoyagiSelectedWidthPairCount_cast
aoyagiSelectedWidthPairSum_const
AoyagiDefinition3SourceData.exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_decomposition
```

## Inputs

- positive-remainder decomposition `w = L*q+a`;
- bounds `0<a` and `a<=L`;
- constant reduced-width hypothesis
  `aoyagiReducedWidthInt H r s = w` on `1 <= s <= L+1`.

## Outputs

- consecutive selected cutpoints `C.cut j = j.val+1`;
- source data `AoyagiDefinition3SourceData L L H r C`;
- constant selected-width family `m j = w`;
- explicit ceiling data `ceilWidth=w+q+1`, `aParam=a`;
- order formula `a*(L-a)+1`;
- selected pair sum `((L+1)*L*w^2)/2`;
- unfolded finite lambda formula with pair contribution `((L+1)*L*w^2)/4`.

## Not Proved

This is finite arithmetic for a restricted source-backed branch.  It does not
prove arbitrary Definition 3 branch selection, final Theorem 2 for arbitrary
source data, Eq5 production, chart production, normal crossings, pole order,
or RLCT extraction.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

Passed on 2026-06-26.

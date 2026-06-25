# Review - Definition 3 exact ceiling data

Date: 2026-06-25.

Reviewer: Carson, xhigh source/API review.

Verdict: PASS.  No blocking findings.

## Scope

Reviewed the exact Definition 3 ceiling/residue constructor and its bridge:

```text
AoyagiDefinition3CeilData.ofSelectedSumCeil
AoyagiDefinition3CeilData.ofSelectedSumCeil_ceilWidth
AoyagiDefinition3CeilData.ofSelectedSumCeil_aParam
AoyagiDefinition3CeilData.nonempty_of_ell_pos
```

Files:

```text
lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean
lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

## Checks

- Lean elaboration passed for `FinalFormula.lean` and
  `Definition3Bridge.lean`.
- The constructor uses Euclidean division of `T - 1`, so the residue
  `((T - 1) % ell + 1).toNat` lies in `1..ell` for positive `ell`, including
  negative integer selected-width sums.
- The projected `ceilWidth` and `aParam` simp lemmas are precise projection
  lemmas.
- `nonempty_of_ell_pos` soundly delegates to the exact constructor.
- No `Core` or `ClosedForm` dependency is introduced; the slice remains in
  the Aoyagi finite-formula layer.
- The formulas match Aoyagi Definition 3, PDF pp. 8-9:
  `M - 1 < T/ell <= M` and `a = T - (M - 1)ell`.
- The reproduction and statement card keep the nonclaims explicit: no
  selected-cutpoint construction, no branch-selection rule, no repaired
  inactive inequality, no normal crossings, no pole order, no RLCT, and no
  Core/quiver codimension facts.

No reviewer edits were made.

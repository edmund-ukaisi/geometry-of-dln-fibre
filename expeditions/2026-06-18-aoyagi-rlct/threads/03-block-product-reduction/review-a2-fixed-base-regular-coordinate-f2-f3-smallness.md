# Review - A2 fixed-base regular-coordinate F2/F3 smallness

Date: 2026-06-24.

Reviewer: xhigh scout `Kierkegaard the 4th`.

Status: passed; recommended theorem boundary implemented.

## Checked Target

The reviewer recommended adding the source-data wrapper in namespace

```text
PaperEndpointFixedBaseRegularCoordinateSourceData
```

with the scalar field specialised to `real`.  This matches the implemented
theorems:

```text
regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one
regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one_nhdsWithin_source
```

The review specifically warned against placing this in the polymorphic `K`
section, because the finite smallness theorem is real-valued.

## Proof Check

The proof route is exactly the reviewed route:

1. use `regularBlockCoordinateMap_centered_continuousAt` from the source-data
   package to obtain Pi-valued centering and continuity;
2. turn it into coordinatewise centered-continuity data using `congrFun` and
   `continuous_apply`;
3. apply
   `AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt`;
4. derive the `nhdsWithin` version only by filter weakening from the ambient
   theorem.

The focused build passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```

## Type-Fidelity Checks

The reviewer highlighted the main tag and endpoint-order risks:

- `mu` is the complement at `Fin.last N`;
- `nu` is the complement at `0`;
- the `F2` subfamily is indexed by `iota x nu`;
- the `F3` subfamily is indexed by `mu x iota`;
- the nested `Sum` annotations should be retained.

The implemented statements retain these choices.

## Nonclaims

The `nhdsWithin` theorem is only a relative-filter weakening.  It does not
prove source-rank-stratum openness, source-stratum nonemptiness, chart-domain
coverage, analytic regular-coordinate status, analytic ideal transport,
regular-suspension normal crossings, pole order, or RLCT.

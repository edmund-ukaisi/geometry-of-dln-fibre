# Statement card - A2 with-following original-volume readback from reverse raw-source domination

Date: 2026-07-02.

## Lean targets

Formal-product upstream bridge:

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
```

Primary bridge:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
```

Same-shrink readback bridge:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_restrict_rawSource_le_smul_case2PassiveThetaWithFollowingFactor_rawMap
```

## Inputs

On a local with-following Case 2 shrink `V`:

```text
rawHaar.restrict rawSourceSet
  <= D • Measure.map rawMap (thetaReference.restrict V)
```

with `rawHaar.IsAddHaarMeasure`, `chartPiece` measurable, and `chartPiece`
contained either in the p.13 source set or in `sourceChart '' V` for the
support-discharge wrapper.

## Output

The formal-product bridge proves:

```text
formalProductMeasure.restrict chartPiece
  <= D • Measure.map sourceChart (thetaReference.restrict V)
```

The original-volume bridge proves:

```text
originalVolume.restrict chartPiece
  <= ((cHaar^-1) * D) • Measure.map sourceChart (thetaReference.restrict V)
```

where

```text
cHaar =
  (Measure.map rawOrderMatrixTupleEquiv rawHaar).addHaarScalarFactor
    (originalTupleVolume d).
```

The readback theorem proves:

```text
AEMeasurable readback (originalVolume.restrict chartPiece)
```

and

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= ((cHaar^-1) * D) • thetaReference.restrict G.
```

The readback theorem also returns local source-chart readback, injectivity,
continuity, measurable image, and p.13 support for `sourceChart '' V`.

## Proof dependencies

- with-following endpoint source-chart local readback/injectivity package;
- with-following raw-order/source-chart two-stage handoff;
- retained-passive formal-product COV and p.13 original-volume scalar bridge;
- `readback_aemeasurable_and_map_le_smul_of_le_smul_source_measure_le`.

## Verification

Focused local builds for the three touched Aoyagi modules passed, and the full
local build passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
Touched-file marker scan and `git diff --check` passed.  Direct axiom probes
for the three new constants reported:

```text
[propext, Classical.choice, Quot.sound]
```

Independent xhigh review `review-a2-with-following-original-volume-readback-reverse-raw-source-domination.md`
found no issues.

## Nonclaims

No determinant-Haar transport, no exact raw-Haar pushforward, no
`sourceImageDensity` construction, no positivity/lower-bound theorem, no
source-rank coverage, no normal crossings, no pole order, and no RLCT
extraction.

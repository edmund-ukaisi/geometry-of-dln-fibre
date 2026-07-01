# Reproduction - A2 Case 2 original-volume source-image same-shrink conditional

Date: 2026-07-01.

Status: pen-and-paper boundary check and Lean proof complete for the
conditional bridge.

## Question

Can the current Aoyagi p.13 infrastructure identify the original edge-family
volume on a local chart piece with the concrete passive-theta source-image
reference

```text
Measure.map sourceChart (thetaReference.restrict V)
```

without an extra hypothesis?

## Source Boundary

The answer is no.  Aoyagi p.13 gives the block algebra for the reduced
coordinates:

```text
F2 = -A1^{-1} A2
F3 = -A3 A1^{-1}
C  = A4 - A3 A1^{-1} A2
```

and the product-difference normal form

```text
[ C1 - I_r              -F2
  -F3       prod_s C^(s) - F3 F2 ].
```

This supports the elementary product-reduction and regular-variable
calculation.  It does not by itself prove that the chart-produced
passive-theta source-image measure is the restriction of the original
edge-family volume.  The full retained-passive raw determinant chart has
additional variables, while the p.13/reduced section fixes variables such as
`C1 = I` and `A3 = 0`.  A local original-volume comparison therefore needs a
separate local change-of-variables/Jacobian theorem, or an explicit raw-Haar
raw-source pushforward hypothesis.

## Conditional Bridge

The existing p.13 raw-order/original-volume theorem says that if the local
raw-order pushforward is exactly the raw Haar restriction to the raw-order
source-recursive determinant chart, then the source-chart image is a scalar
multiple of the original volume restricted to the p.13 source set.

The new Lean theorem puts this in the actual local source-image chart shape.
On one local shrink `V`, it also records:

- `readback (sourceChart z) = z` for `z in V`;
- injectivity and continuity of `sourceChart` on `V`;
- measurability of `sourceChart '' V`;
- containment `sourceChart '' V subset p13SourceSet`.

Then for every measurable `chartPiece subset sourceChart '' V`, if

```text
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet,
```

the restricted original edge-family volume is a bounded-density perturbation
of the concrete source-image reference with constant inverse Haar scalar.

## Boundary

The raw-Haar pushforward is still an assumption.  The theorem does not prove
determinant-chart Haar transport, raw-order Haar transport, original
source-prior transport, full source-image coverage, source-rank coverage,
normal crossings, pole order, or RLCT extraction.

## Lean Check

Lean witness:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

# Review: A2 Case 2 original-volume finite integral from reverse raw-source domination

Status: controller check and xhigh read-only review passed.

## Controller check

The theorem calls the existing direct original-volume finite-integral front
end, obtains the local source-chart witness `V subset W` from the new reverse
raw-source readback bridge, and passes the bridge's readback a.e.
measurability and domination hypotheses to the finite-integral handler.

The scalar direction is:

```text
m.restrict rawSourceSet <= D * rawMap_*(coordinateSourceMeasure|V)
```

implies

```text
readback_*(originalVolume|chartPiece)
  <= (cHaar^{-1} * D) * coordinateSourceMeasure|W.
```

The scalar is finite because `(cHaar^{-1} : NNReal)` coerces to a finite
`ENNReal` and `D < infinity` is a hypothesis.

The theorem keeps the chart piece inside the actual local source-chart image,
so the p.13 source-set and right-inverse hypotheses are same-witness data.

## Verification

Focused warning-clean elaboration passed:

```text
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

Full local verification passed:

```text
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_reverse_raw_source_finite_integral_axioms.lean
```

The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.

Xhigh read-only reviewer `Turing` found no correctness issue.  The only
non-blocking implementation note was API brittleness from large `simpa` blocks
over local `let`s; no mathematical boundary or theorem-shape issue was found.

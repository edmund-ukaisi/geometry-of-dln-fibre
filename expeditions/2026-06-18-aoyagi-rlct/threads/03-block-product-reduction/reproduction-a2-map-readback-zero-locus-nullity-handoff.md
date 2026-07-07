# A2 map/readback zero-locus nullity handoff

## Source and role

This is elementary measure theory used by the A2 rank-cut residual
zero-locus frontier.  It is not a new cited theorem from Aoyagi and it does
not by itself prove the original-prior residual zero-locus nullity.

## Reproduction

Let `μ` be a measure on edge-family coordinates, `θμ` a measure on theta
coordinates, and `readback : E -> Θ`.  Let `f : E -> R` be the edge-side
residual square-sum and `g : Θ -> R` the theta-side product-residual
square-sum.

Assume:

1. `readback` is a.e.-measurable for `μ`.
2. `Measure.map readback μ <= c • θμ`.
3. `0 < g z` for `θμ`-a.e. `z`.
4. The edge-side zero locus is a.e. contained in the readback preimage of the
   theta-side zero locus:

   ```text
   {E | f E = 0} <=ᵐ[μ] readback^{-1} {z | g z = 0}.
   ```

First, by scalar domination and theta-side a.e. positivity,

```text
(Measure.map readback μ) {z | g z = 0} = 0.
```

Second, because `readback` is a.e.-measurable, Mathlib's `Measure.le_map_apply`
gives, without a measurability assumption on the zero set,

```text
μ (readback^{-1} {z | g z = 0})
  <= (Measure.map readback μ) {z | g z = 0}
  = 0.
```

Hence the readback preimage of the theta-side zero locus is `μ`-null.  The
a.e. zero-locus containment then gives

```text
μ {E | f E = 0} = 0.
```

## Kill conditions

- Reading the lemma as proving concrete original-prior domination.
- Reading the lemma as proving the readback/sourceChart residual equality.
- Reading the lemma as proving theta-side residual positivity.
- Reading the lemma as proving source-rank coverage, determinant/raw-Haar
  transport, normal crossings, pole order, or RLCT extraction.

## Lean target

```text
measure_zero_set_eq_zero_of_map_le_smul_of_ae_pos_of_ae_zero_imp
```

in `lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`.

## Verification

Focused module build, full local `lake build DLNFibre`, `scripts/sorries`,
`git diff --check`, touched Lean-file marker scan, and direct axiom probe
passed.  The declaration reports only
`[propext, Classical.choice, Quot.sound]`.

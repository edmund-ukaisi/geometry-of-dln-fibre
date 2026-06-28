1. Yes, use (a). The Mathlib idiom is:

```lean
hcontOn.isOpen_inter_preimage hSopen isOpen_ne
```

where `hcontOn : ContinuousOn f S`, `hSopen : IsOpen S`, and `isOpen_ne : IsOpen {x | x ≠ 0}`. This proves:

```lean
IsOpen (S ∩ f ⁻¹' {x | x ≠ 0})
```

Then prove the joint set as an intersection of such open sets using `IsOpen.inter`. For the readX locus use ordinary preimage openness, e.g. `hUnitOpen.preimage hProjCont` or `hProjCont.isOpen_preimage _ hUnitOpen`. If any determinant is globally continuous, use `hcont.isOpen_preimage _ isOpen_ne`; otherwise use `ContinuousOn.isOpen_inter_preimage`.

2. Correct: generalize the entrywise `ContDiffAt` bank to arbitrary `q` with determinant hypotheses. The dependency order is exactly:

`A0⁻¹`, `A1⁻¹` need `det A0 q ≠ 0`, `det A1 q ≠ 0`;  
`P00⁻¹` needs `det P00 q ≠ 0` plus entry smoothness of `P00`;  
`R`, `U`, etc. consume those inverse-entry facts;  
`W` entries then become `ContDiffAt` from `W = 1 + R`;  
`W⁻¹` needs `det W q ≠ 0` and the entrywise `ContDiffAt` facts for `W`.

This is mechanical. The main subtlety is only to keep determinant hypotheses attached to the point `q`, not hidden as global assumptions.

3. I recommend per-point generalized `ContDiffAt`, not a new `ContDiffOn jointUnitSet` layer. Your landed bank, inverse helper, and target theorem are all `ContDiffAt`; staying pointwise avoids `ContDiffWithinAt`/`ContDiffOn` bookkeeping, `mono` subset threading, and repeated open-set conversions. A final wrapper theorem can say `∀ q ∈ jointUnitSet, ContDiffAt ... q`. Only switch to `ContDiffOn` if several later consumers genuinely need smoothness-on-the-open-set as an object.
**Verdict**

**FACT:** the raw `Ψ` is only smooth on the unit locus where `P00` and `1+X1` are invertible. So it does **not** satisfy the current global `ContDiff ℝ ⊤ f` antecedent as stated.

**INFERENCE:** the cutoff route is sound for the three antecedents, but only after choosing the right coordinate space. Define, in split coordinates,

```text
T1 ↦ T1 + χ · K · (U1 - T1)
where U1 = Z1 (1+X1)⁻¹ Y1,   K = Z1 P00⁻¹ Y0.
```

Choose `χ = 1` near `0` and `tsupport χ` inside the common invertibility locus for `P00` and `1+X1`. Then:

- `ContDiff ℝ ⊤ Ψχ`: yes, by the same support-inside-unit-locus argument as `schurCutoffShift`.
- `Ψχ 0 = 0`: yes, since the correction vanishes at the deepest point.
- `HasStrictFDerivAt Ψχ id 0`: yes, since near `0`, `χ=1` and the correction is `O(read²) · O(read) = O(read³)`. The correct `e` is the identity continuous linear equivalence.

Do **not** claim `coreΦ ∘ Ψχ = Score` globally. Claim it as a germ/eventual equality near `wstar`, where `χ=1` and the coreAbsorb cutoff is also in its raw Schur region.

**Loud Red Flag: `split`**

**FACT:** from the setup, `split` is only typed as a homeomorphism `≃ₜ`.

**INFERENCE:** if you define flat-coordinate

```text
Ψflat = split.symm ∘ Ψsplit ∘ split
```

then `ContDiff Ψflat` is **not available** from the current type. A homeomorphism does not transport smoothness. This is the real hidden obstruction.

Best routes:

1. **Cleanest:** work in `DeepestSplit` coordinates for this RLCT step. Apply `rlctAtOn_comp_localDiffeo` to `Ψsplit` at `0`.
2. **If final theorem must be flat:** either prove `split` and `split.symm` are `ContDiff`/a smooth affine equivalence, or define `Ψflat` directly by flat coordinate projections/injections, avoiding smoothness transport through `split`.
3. **If you can touch RLCT infrastructure:** a `ContDiffAt`-only variant is mathematically cleaner than cutoff, but it still does not solve the `split` transport problem.

**Cleanest Ψ**

Conceptually, act in absorbed core coordinates:

```text
S1 ↦ (I - K) S1
```

and fix everything else. In raw core coordinates this is exactly your formula:

```text
T1' = (I - K) T1 + K · Z1(1+X1)⁻¹Y1.
```

That is the cleanest slot action because the middle factor sits immediately before `S1`:

```text
S0 · S1  ↦  S0 · (I-K) · S1.
```

Acting on the reduced product directly is less Lean-friendly because it is not a coordinate slot. Acting on `T0` is possible but less natural and creates worse bookkeeping.

**Composition Chain**

On the inner neighborhood where all cutoffs are raw:

1. `Ψ` fixes reg/spec and `T0`.
2. `U1 := Z1(1+X1)⁻¹Y1` is unchanged.
3. `S1' = T1' - U1`
4. `= (I-K)T1 + K U1 - U1`
5. `= (I-K)(T1 - U1)`
6. `= (I-K)S1`.
7. `S0' = S0`.
8. Banked `deepestCoreF_coreAbsorb_eq_prodSchur` gives  
   `coreΦ(Ψ x) = ‖S0 · (I-K) · S1‖²_F`.
9. Banked LDU gives  
   `Score(x) = ‖S0 · (I-K) · S1‖²_F`.

So the core identity is complete, modulo the local cutoff-equals-raw lemma and the product-order convention from the banked theorem.

One extra check: `Sreg_E` must truly factor only through the slots fixed by `Ψ`. If `Sreg_E` is the full product regular residual containing terms like `Y0 T1`, then changing `T1` would not fix it.

**Tide Estimate**

Highest risk first:

1. **`split` smoothness / transport:** multi-tide if not already banked. This is the blocker for flat `Ψ = split.symm ∘ ... ∘ split`.
2. **Composition identity plumbing:** 1-2 tides, mostly `split`/`coreAbsorb`/`paramsEquivFlat` bookkeeping.
3. **Cutoff global smoothness:** about 1 tide if the `schurCutoffShift` pattern is reusable; more if `P00⁻¹` smoothness/support lemmas are new.
4. **Strict derivative `= id`:** small, likely sub-tide once the map is formulated in smooth coordinates.

Bottom line: the cutoff route is sound, but the flat-coordinate construction is not Lean-sound until `split` is promoted from `≃ₜ` to a smooth/affine chart or bypassed.
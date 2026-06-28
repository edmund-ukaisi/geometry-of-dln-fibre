**VERDICT: (A).**

In one generic corank-`r` recStep firing, `T` enters only through the outer `Δ ∈ matBox r r T` chart radius and through the resulting bounded angular/chart coefficients. On a pivot chart, write `Δ = a · R` with `a ∈ [-T,T]`; after the N2b split and Schur-complement translation, the residual lower-corank variables land in a box of radius of the form

`T'' = K + B`

where `K` is the current `S`/residual-box radius inherited from the original `T`, and `B` is the chart-dependent Cramer/Schur shift bound coming from the angular `R` box. This is exactly the kind of radius accepted by the general-`T` lower IH.

So the recStep should invoke:

`SchurLowerIH (r - j) (c' - jp/2) T''`

with `T'' ≈ T + B` or, depending on normalization, `K + B`.

The unit-only `core_schur3_lt_top` is not structurally needed by the generic recStep. It is a validated corank-3 endpoint using a hardwired unit-box chart chain and the banked `(3,3,4)` anchor, but the generic recursion does not need to call that theorem if its contract is already “peel one Morse block, translate, invoke lower IH at arbitrary radius.”

The supporting evidence is exactly your #1–#3:

- `core_schur2_lt_top`: general `T`, so the recursion base is fine.
- `resolvedShiftR2c3_le`: general `K`, and calls the base at `K+B`.
- `schurResid2_translate_lt_top`: general `T`, again via base at `T+B`.

Thus no matrix box-scaling lemma is needed to build the generic per-corank `SchurRecStep`, assuming the radial chart/N2b/translation arguments themselves are written parametrically in `T`.

The deferred `lintegral_comp_smul` box-scaling is still useful, but for upgrading the already-bankrolled standalone theorem `core_schur3_lt_top` from unit-box to general-`T`. It is not a per-corank obstruction to the generic recursive step.

Mathlib lemma names: `lintegral_comp_smul` is **INFERRED**, not a confident existing name.
Cost ranking:

1. **(A) cheapest.** Clean if stated as `¬ IsNilpotent h`, not merely `h ≠ 0`.
2. **(B) medium.** Genuine incidence; feasible but multi-lemma/typeclass work.
3. **(C) heavy/overkill.** “THE chart prime” needs extra uniqueness/canonical-choice data; not worth it for this fix.

For **(A)**, exact Mathlib names:

- `IsReduced.eq_zero` to get `¬ IsNilpotent g` from `g ≠ 0`.
- `IsNilpotent.map_iff` to reflect nilpotence across injective maps.
- `Algebra.TensorProduct.includeRight_injective` for `includeRight`.
- `PrimeSpectrum.basicOpen_eq_bot_iff` for `basicOpen h = ⊥ ↔ IsNilpotent h`.
- `Ideal.mem_comap` if phrasing opens by ideals.
- `e.symm.injective` / `e.injective` from the `AlgEquiv`; no special lemma needed.

Important correction: `g ∉ I` gives `g ≠ 0` because `0 ∈ I`; reducedness is only used to turn `g ≠ 0` into `¬ IsNilpotent g`.

For **(B)**, the right API is faithfully-flat lying-over, not minimal-prime machinery:

- `Ideal.exists_isPrime_liesOver_of_faithfullyFlat`
- or spectrum form: `PrimeSpectrum.comap_surjective_of_faithfullyFlat`
- `Ideal.mem_of_liesOver` gives `includeRight g ∉ Q` from `g ∉ I`.
- Use local `letI := Algebra.TensorProduct.rightAlgebra`; then
  `Algebra.TensorProduct.algebraMap_eq_includeRight` identifies `algebraMap` with `includeRight`.
- Faithful flatness source:
  `RingHom.FaithfullyFlat.isStableUnderBaseChange` plus `TensorProduct.isPushout`.
  Inference: over a field and `[Nontrivial SchurLoc]`, `Module.FaithfullyFlat k SchurLoc` should be TC-solvable via `Module.Free.of_divisionRing` + the free nontrivial faithfully-flat instance.

So **(B)** is the honest incidence lemma, but it is not one-line cheap.

If you want minimal C4 closure: land **(A)** and correct the docstring. Precise claim:

> The produced smooth basic open `D(h)` is nonempty/nonvacuous: `¬ IsNilpotent h`, equivalently `PrimeSpectrum.basicOpen h ≠ ⊥`.

It **does not** claim `D(h)` meets the chart image of the chosen component `I`, nor does it produce a prime over `I`. That incidence requires **(B)**.
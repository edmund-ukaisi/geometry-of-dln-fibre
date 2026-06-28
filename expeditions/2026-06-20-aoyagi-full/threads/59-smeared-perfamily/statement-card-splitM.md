# Statement card — `splitOfPartition` (the general `Reg × Core × Spec` block split, #159 sub-tide 2)

> **Claim.** For any `N, a, b, c : ℕ` and any index decomposition `e : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin N`,
> there is a measure-preserving block-equivalence
> `(Fin N → ℝ) ≃ᵐ (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ))` whose three factors read the original
> coordinates off the `inl` / `inr∘inl` / `inr∘inr` images of `e`. This is the general primitive
> behind the per-family smeared chart's `shearM` — the input shape `coreShear_measurable a b c shift`
> consumes — subsuming the hand-built `split121` / `split231` (which fix the coords for one shape).
>
> - **Lean:** `DLNFibre.DLN.RLCT.splitOfPartition` + `measurePreserving_splitOfPartition`
>   (`lean/DLNFibre/DLN/RLCT/Foundations/CoreSplitMP.lean` @ `7ea60bb1`); readback
>   `splitOfPartition_reg` / `_core` / `_spec` / `splitOfPartition_symm_apply`; the thin consumer
>   instance `coreSetEquiv` / `splitOfCoreSet` / `measurePreserving_splitOfCoreSet` /
>   `splitOfCoreSet_core` / `splitOfCoreSet_spec` (same file); worked-instance cross-check
>   `DLNFibre.DLN.RLCT.split_e231_*`, `measurePreserving_splitOfPartition_e231`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSplitValidate.lean` @ `7ea60bb1`).
> - **Gloss.** `splitOfPartition e` reindexes the flat function space `Fin N → ℝ` along `e`
>   (`piCongrLeft`, a coordinate re-label — never a `Nat`-cast on a dependent `Fin`), then splits the
>   sum index twice (`sumPiEquivProdPi`) into the product `(Reg) × ((Core) × (Spec))`. The Reg / Core /
>   Spec blocks are the `inl` / `inr∘inl` / `inr∘inr` preimages of `e`; the readback lemmas state
>   `(split e u).1 i = u (e (inl i))`, `(…).2.1 j = u (e (inr (inl j)))`, `(…).2.2 k = u (e (inr (inr k)))`
>   (all `rfl`), and `(split e).symm q (e idx) = Sum.elim q.1 (Sum.elim q.2.1 q.2.2) idx`. `volume` is
>   preserved factor-by-factor (`volume_measurePreserving_piCongrLeft`,
>   `volume_measurePreserving_sumPiEquivProdPi`, `MeasurePreserving.prod`).
> - **Proved.** Unconditionally, for ALL widths `N, a, b, c` and ALL index-equivs `e`: the equivalence
>   `splitOfPartition e` is a `MeasurableEquiv`, is measure-preserving for the product Lebesgue measure,
>   and reads the three blocks off the stated `e`-images (forward + symm readback). The `(2,3,1)`
>   cross-check confirms cardinality `9 = 1 + 2 + 6` and that `splitOfPartition e231` reproduces the
>   `split231` block assignment Reg = {0}, Core = {6,7}, Spec = {1,2,3,4,5,8}, exactly.
> - **Assumed.** None. (`e` is a free parameter — the construction works for any decomposition; the
>   theorem carries no hypothesis on the block sizes beyond `a + b + c = N` implicit in `e`'s existence.)
> - **Cited.** None — built from Mathlib v4.29 measurable-equiv primitives only.
> - **Deferred.** The `coreSet : Finset (Fin N)` itself for a general `M` — *which* flat indices are the
>   kept top-`r` rows of `A^{L−1}`, derived from the achiever rank pattern — is the per-family consumer's
>   (`shearM_conj`, genm-assemble). The block-split machinery that consumes a `coreSet` IS built here
>   (`splitOfCoreSet`, parameterization iii, genm-assemble's settled convention: Core = `coreSet`,
>   Spec = `coreSetᶜ`, Reg = ∅). `splitOfPartition` is convention-agnostic (reads the block assignment off
>   `e`), so the design-doc-vs-instances Reg discrepancy (design §1: Reg = front; instances/convention:
>   Reg = ∅, shift reads the full complement) does not bind it.
> - **Status.** sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## Notes for the consumer (`shearM_conj`, genm-assemble)

- `splitOfPartition` is exactly the shape `measurePreserving_coreShear_measurable a b c shift` consumes:
  `shearM = (splitOfPartition e).symm ∘ (coreShear shift) ∘ (splitOfPartition e)` is MP for any widths
  (compose `measurePreserving_splitOfPartition` with `measurePreserving_coreShear_measurable` and its
  symm, the same pattern as `measurePreserving_shear231`).
- To prove `shearM` commutes with the shift (the `split231_shear231` analogue), use the readback lemmas:
  `splitOfPartition_reg/_core/_spec` express each block as `u ∘ e ∘ (inl|inr∘inl|inr∘inr)`, so a shift
  written as a function of the original coords pulls back through `e` mechanically.
- The block convention is yours to set via `e`: pick `e` so the Core block (`inr∘inl`) is the slots your
  shift moves, Reg+Spec (`inl`, `inr∘inr`) the slots it reads. The `(2,3,1)` cross-check
  (`RouteMSplitValidate.e231`) is a worked template for building such an `e` (explicit map +
  `Equiv.ofBijective` + `decide`-checked bijectivity).

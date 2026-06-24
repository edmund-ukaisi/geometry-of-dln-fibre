# Statement card — R2-3 route-(b) reducedness chain (thread 17)

> **Claim.** On the rank-`r` pivot chart, the fibre ideal `I_B = (mult(Ã) − B)` is **radical**
> (`F_B = k[Ã]/I_B` **reduced**), and consequently the fibre's vanishing ideal collapses to its
> generator ideal — *provided* the chart trivializes as a product `S ≅ₐ[k] R ⊗_k F_B` with the chart
> ring `S` reduced. The reducedness descends from the reduced ambient chart `S` through the
> trivialization (the certified route (b), thread 16).
>
> - **Lean (descent):** `DLNFibre.Core.isReduced_of_tensor`
>   (`lean/DLNFibre/Core/FibreReducedTrivialization.lean` @ `91c77ff0`)
> - **Lean (chain):** `DLNFibre.Core.fibreGenIdeal_isRadical_of_trivialization` (same file/SHA)
> - **Lean (collapse):** `DLNFibre.Core.vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`
>   (same file/SHA)
> - **Lean (bridge):** `DLNFibre.Core.fibreGenIdeal_isRadical_iff_isReduced_fibreAlg` (same file/SHA)
>
> - **Gloss.**
>   - `isReduced_of_tensor` — over a field `k`, for a nontrivial commutative `k`-algebra `R` and a
>     commutative `k`-algebra `F`: `R ⊗_k F` reduced ⟹ `F` reduced. (`F` injects into `R ⊗_k F` via
>     `includeRight`, injective since `F` is `k`-flat and `algebraMap k R` is injective; pull back
>     reducedness with `isReduced_of_injective`.)
>   - `fibreGenIdeal_isRadical_of_trivialization` — given an algebra equiv `e : S ≃ₐ[k] R ⊗_k F_B`
>     (`F_B = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B`) and `IsReduced S`, the ideal
>     `fibreGenIdeal d B` is radical. (`S` reduced ⟹ `R ⊗_k F_B` reduced via `e.symm` ⟹ `F_B` reduced
>     via the descent ⟹ `fibreGenIdeal` radical via `Ideal.isRadical_iff_quotient_reduced`.)
>   - `vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization` — under the same hypotheses and
>     `[IsAlgClosed k]`, `vanishingIdeal (canonicalCoord d '' fibre d B) = fibreGenIdeal d B`: the
>     `radical (·)` in `MultComorphism` point 4 drops.
>   - `fibreGenIdeal_isRadical_iff_isReduced_fibreAlg` — `(fibreGenIdeal d B).IsRadical ↔
>     IsReduced (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B)` (the engine restatement of
>     `Ideal.isRadical_iff_quotient_reduced`).
>
> - **Proved (unconditional).** The tensor-with-a-field reducedness descent `isReduced_of_tensor`
>   (the "one open dependency" the thread-16 certificate flagged — now a proved Core lemma). The
>   `IsRadical ⟺ quotient-reduced` bridge. The full route-(b) chain and the radical-collapse, *as
>   functions of the trivialization hypothesis* `e` + `IsReduced S` (every step from `e`/`IsReduced S`
>   to `fibreGenIdeal` radical to the collapse is discharged). Sorry-free; axiom-clean
>   `[propext, Classical.choice, Quot.sound]`; non-vacuity witnesses in-file.
>
> - **Assumed (carried as explicit hypotheses, not asserted).** The trivialization
>   `e : S ≃ₐ[k] R ⊗_k F_B` and `IsReduced S`. These are the deep endpoint-normalization product iso
>   for the reduced chart ring — supplied as hypotheses, NOT proved here.
>
> - **Cited.** The geometric reducedness *fact* `F_B` reduced for the rank chart is certified by
>   pen-and-paper (thread 16: Singular `primdecGTZ` + `radical` over ℚ on 11 cases + decorrelated
>   Codex). The Lean here does not re-derive that fact from scratch; it derives it *through* the
>   trivialization hypothesis (the certified mechanism). Mathlib: `includeRight_injective`,
>   `isReduced_of_injective`, `Ideal.isRadical_iff_quotient_reduced`,
>   `MultComorphism.vanishingIdeal_image_fibre_eq_radical` (engine, point 4).
>
> - **Deferred (named, the residual G2-3 wall).** The construction of the trivialization
>   `e : S ≃ₐ[k] R ⊗_k F_B` itself, for the genuine deep rank chart with `S = O(Σ̄^r ∩ chart)` reduced
>   (the engine's `Sred = (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)[1/ΔP]`). This is the deep
>   endpoint-normalization product iso (`Ã₁ = A₁H⁻¹`, `Ã_N = L⁻¹A_N`); it is new scheme-free affine
>   scaffolding (no deep localized total ring exists in the engine yet — G2-2's machinery is `N = 1`
>   only). It is a separate rung (R2-3b), now fully de-risked downstream: every consumer of `e` is
>   already proved here against the hypothesis, so landing `e` + `IsReduced S` closes the chain with
>   no further reducedness work.
>
> - **Status.** sorry-free, axiom-clean (awaiting reviewer fidelity check + aggregator wiring).

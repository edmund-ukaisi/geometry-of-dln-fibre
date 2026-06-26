# Statement card — thread 26 (fidelity fix: C3 arbitrary-B θ-count, C4 chart-smoothness incidence)

Closes OPERATOR fidelity items C3/C4/C5 on PR #11. SHA below is pre-commit HEAD
(`fd70f6c2`); bump to the integrating commit on commit.

**Fidelity review: PASSED** (reviewer teammate, decorrelated Codex read) — C3 PASS (genuine free-`B`
general claim, not secretly normal form), C4 PASS (non-vacuity proved with same witness; full
incidence residual honestly disclosed, not hidden), C5 PASS (well-formed deprecations, warnings
retained). Gates re-verified independently: `scripts/sorries` 0; `#print axioms` clean on all four
headlines; whole-library `scripts/lb` green (3805 jobs). Status of cards below: **sorry-free + reviewed**.

---

## C3 — the fibre-`θ` count for an ARBITRARY rank-`r` target (CLOSED)

> **Claim.** For an arbitrary rank-`r` target `B` (not only the chart normal form `E_r`), the number
> of top-dimensional irreducible components of the multiplication-map fibre `mult⁻¹ B` equals the
> closed combinatorial form `cTheta (d − r)`. Needs `N ≥ 1` and the model hypotheses.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of_rank`
>   (`lean/DLNFibre/Core/FibreThetaCountArbitrary.lean` @ `fd70f6c2`)
> - **Gloss.** For `d : Fin (N+2) → ℕ`, `r`, rank bounds `hp/hq`, `hN : 0 ≠ last`, `Monotone d`,
>   `∀ i, r ≤ d i`, Kostant-nonempty `h₀/h`, and any `B` with `B.rank = r`:
>   `(TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B)).ncard = cTheta (dminus d r)`.
>   At `k : Type` (`Type 0`), `[IsAlgClosed k] [CharZero k]` — matching the model headline's universe.
> - **Proved.** Unconditionally (modulo the stated hyps). The transport lemma
>   `ncard_topDimMinPrimes_fibre_eq_of_rank_eq` (same rank ⟹ equal fibre top-component count) is
>   universe-polymorphic and proved separately; the headline composes it with the LANDED model
>   headline `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus`.
> - **Assumed.** Same hyps as the model headline (`N ≥ 1`, monotone/rank/Kostant). `B.rank = r`.
> - **Cited.** none beyond LANDED harness lemmas (`exists_baseChange_of_rank_eq`,
>   `image_smul_fibre`, `vanishingIdeal_image_smul`, `vanishingIdeal_image_fibre_eq_radical`,
>   `topDimMinPrimes_quotient_radical_ncard_eq`, `topDimMinPrimes_ncard_eq_of_ringEquiv`).
> - **Deferred.** none for C3.
> - **Route.** Same-rank ⟹ `GL×GL`-equivalent (`exists_baseChange_of_rank_eq`); the base change
>   `A ↦ P•A` carries `mult⁻¹ B` onto `mult⁻¹ E_r` (`image_smul_fibre`); its coordinate-ring
>   automorphism `baseChangeAlgEquiv P` (a `RingEquiv`) identifies the radical quotients
>   (`vanishingIdeal_image_smul` + `Ideal.quotientEquiv`); the count is radical-insensitive
>   (`topDimMinPrimes_quotient_radical_ncard_eq`) and a ring-iso invariant
>   (`topDimMinPrimes_ncard_eq_of_ringEquiv`). Codex-confirmed: bare RingEquiv suffices, no
>   properness argument.
> - **Status.** sorry-free; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## C4 — chart smoothness on a NONEMPTY basic open (PARTIAL — non-vacuity closed, full incidence residual)

> **Claim.** The source pivot chart `Away (chartDsig …)` is smooth on a *nonempty* basic open at the
> chosen top component `I` (strengthening the prior form that dropped non-vacuity / incidence).
>
> - **Lean:** `DLNFibre.Core.isSmoothAt_chartDsig_topComponent_nonvacuous`
>   (`lean/DLNFibre/Core/FibreComponentOrbitTransport.lean` @ `fd70f6c2`); helper
>   `exists_smooth_localizationAway_chartDsig_nonvacuous`
>   (`lean/DLNFibre/Core/FibreGenericSmoothUncond.lean`).
> - **Gloss.** For a top-dim minimal prime `I` of `sweepFibreRing`: `∃ h : Away (chartDsig …),
>   ¬ IsNilpotent h ∧ ∀ p prime, h ∉ p → IsSmoothAt k p`. The `¬ IsNilpotent h` certifies the
>   smooth basic open `D(h) = {h ≠ 0}` is **nonempty** — the smoothness conclusion is non-vacuous.
> - **Proved.** Unconditionally. `h = e.symm (1 ⊗ g)` for the singular witness `g ∉ I`; `g ≠ 0`,
>   `sweepFibreRing` reduced ⟹ `¬ IsNilpotent g`; `includeRight` and `e.symm` injective transport
>   non-nilpotence to `h` (`IsNilpotent.map_iff`, `includeRight_injective`).
> - **Assumed.** `I ∈ TopDimMinPrimes`. `[IsAlgClosed k] [Infinite k]`.
> - **Cited.** none beyond LANDED harness lemmas.
> - **Deferred (HONEST RESIDUAL).** Full component-incidence `D(h) ∩ V(I) ≠ ∅` (that `D(h)` meets
>   the chart image of `I`'s generic point specifically) is NOT closed. It needs the faithfully-flat
>   lying-over of `includeRight : sweepFibreRing → SchurLoc ⊗_k sweepFibreRing` over `I`
>   (`Ideal.exists_isPrime_liesOver_of_faithfullyFlat`), which requires
>   `Module.FaithfullyFlat sweepFibreRing (SchurLoc ⊗_k sweepFibreRing)` — NOT TC-discoverable here:
>   needs `Module.Free k SchurLoc` (`Module.Free.of_divisionRing` works) + `Nontrivial SchurLoc` +
>   the tensor orientation flip (the Mathlib base-change instance is `S ⊗[R] M` over `S`, the chart
>   is `M ⊗[k] S`). Probed and confirmed multi-lemma; left as residual. The weak form
>   `exists_isSmoothAt_chartDsig_unconditional` had its docstring CORRECTED to state precisely this
>   gap.
> - **Status.** sorry-free; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

---

## C5 — deprecate the two dead orbit-iso consumers (CLOSED)

> `@[deprecated … (since := "2026-06-26")]` added to
> `DLNFibre.Core.isSmoothAt_sweepFibre_of_component_orbitPolyEquiv`
> (`FibreComponentOrbit.lean`) and
> `DLNFibre.Core.isSmoothAt_sweepFibre_of_component_orbitSmooth`
> (`FibreGenericSmoothUncond.lean`). Full-library build fires **no** deprecation warning on either —
> confirming both are dead (no live consumer). Existing ⚠ docstrings kept.
> - **Status.** green, no warnings.

# Statement card — Tier-R reduced-fibre local-trivial bundle (B1–B4)

Module: `lean/DLNFibre/Core/FibreBundleReduced.lean` (NEW; not yet wired into `DLNFibre.lean`).
All theorems sorry-free, `#print axioms = [propext, Classical.choice, Quot.sound]`.
Base commit at AUDIT: `0abb338` (`expedition/theta-components`); bump SHA on change.

This deliverable lives on the **reduced fibre variety** (`sweepFibreRing = k[Rep]/vanishingIdeal(F)`),
NOT the scheme cut `FibreAlg = k[Rep]/fibreGenIdeal` (which needs the months-scale reducedness wall,
out of scope here). Every statement names `sweepFibreRing` / "reduced variety" explicitly.

---

## B1 (keystone) — the away-localization base-change `AlgEquiv`

> **Claim.** For any commutative `k`-algebra `F` (`k` a field) and any `f : MvPolynomial ι k`,
> inverting the `F`-coefficient image `map (algebraMap k F) f` of `f` is the base change of the
> away-localization `Away f` by `F`.

- **Lean:** `DLNFibre.Core.mvPolynomialAwayMapTensorAlgEquiv`
  (`lean/DLNFibre/Core/FibreBundleReduced.lean` @ `0abb338`)
- **Gloss.** `Localization.Away (MvPolynomial.map (algebraMap k F) f) ≃ₐ[k] Localization.Away f ⊗[k] F`.
- **Proved.** The `k`-`AlgEquiv`, sorry-free, for arbitrary field `k`, arbitrary `CommRing F` with
  `[Algebra k F]`, arbitrary index `ι`, arbitrary `f`. Mechanism: polynomial base-change
  `MvPolynomial ι F ≃ₐ[k] (MvPolynomial ι k) ⊗_k F` (`algebraTensorAlgEquiv` + `TensorProduct.comm`,
  carrying `map (algebraMap k F) f ↦ algebraMap _ _ f`), then localization base-change
  `IsLocalization.tensorProduct_tensorProduct` (`(Away f) ⊗_k F` is the localization of
  `(MvPolynomial ι k) ⊗_k F` at `powers f`), glued by `IsLocalization.algEquivOfAlgEquiv`.
- **Assumed.** none beyond the stated typeclasses.
- **Cited.** none (all Mathlib v4.29 lemmas, reproved-free).
- **Deferred.** none.
- **Status.** sorry-free.

## B1-specialized — the schur-side chart product trivialization

> **Claim.** The schur-side localized chart coordinate ring `Away chartGfib` is the product of the
> free Schur localization `SchurLoc` with the reduced fibre ring `sweepFibreRing`.

- **Lean:** `DLNFibre.Core.reducedFibre_chartGfib_tensorEquiv_reducedVariety` (@ `0abb338`)
- **Gloss.** `Away (chartGfib d r hp hq) ≃ₐ[k] SchurLoc (d 0) (d (last (N+1))) r ⊗[k] sweepFibreRing d r hp hq`.
- **Proved.** B1 at `f = detSchurS`, `F = sweepFibreRing`, `ι = SchurVar` (`chartGfib = map (algebraMap
  k sweepFibreRing) detSchurS` definitionally). sorry-free.
- **Assumed / Cited / Deferred.** none.
- **Status.** sorry-free.

## B2 — the per-chart product trivialization at `{detΔ ≠ 0}`

> **Claim.** The source pivot-chart ring `Away chartDsig` of the rank-`r` product locus is the
> product `SchurLoc ⊗_k sweepFibreRing`.

- **Lean:** `DLNFibre.Core.reducedFibre_chartDsig_tensorEquiv_reducedVariety` (@ `0abb338`)
- **Gloss.** `[Infinite k] → Away (chartDsig d r hp hq) ≃ₐ[k] SchurLoc … ⊗[k] sweepFibreRing d r hp hq`.
- **Proved.** Compose the BUILT chart `e_β = chartLocalizedAlgEquiv`
  (`Away chartDsig ≃ₐ[k] Away chartGfib`) with B1-specialized. sorry-free.
- **Assumed.** `[Infinite k]` (the chart `e_β` carries it).
- **Cited.** `chartLocalizedAlgEquiv` (LANDED earlier in `Core.ChartLocalizedAlgEquiv`; route-β).
- **Deferred.** none.
- **Status.** sorry-free.

## B4 — bundle-base homogeneity (every rank-`r` fibre is a base-change image of the model)

> **Claim.** For `N ≥ 1`, every rank-`r` target `B` lies in the single `GL(d_last)×GL(d_0)` orbit of
> the normal form `E_r`, and `mult⁻¹(B) = (P•·) '' mult⁻¹(E_r)` for a base change `P`.

- **Lean:** `DLNFibre.Core.reducedFibre_baseChangeHomogeneous` (@ `0abb338`)
- **Gloss.** `B.rank = r → ∃ P : BaseChangeGroup d, fibre d B = (fun A ↦ P • A) '' fibre d (normalForm
  (d (last (N+1))) (d 0) r hp hq)`.
- **Proved.** `rank_normalForm` (`E_r.rank = r`) + `exists_baseChange_of_rank_eq` (equal rank ⟹
  end-factor `GL×GL`-equivalent, `P` produced with inner units = 1) + `image_smul_fibre` (the fibre
  transport `fibre d (P_N·E·P_0⁻¹) = (P•·) '' fibre d E`). The `N ≥ 1` hypothesis `0 ≠ last (N+1)` is
  automatic for `Fin (N+2)`. sorry-free.
- **Assumed.** none beyond `B.rank = r` (the `N ≥ 1` is structural in `Fin (N+2)`).
- **Cited.** `exists_baseChange_of_rank_eq`, `image_smul_fibre`, `rank_normalForm` (all LANDED in
  `Core.FibreNormalForm` / `Core.ChartEvalRealize`).
- **Deferred.** A genuine **open cover of `Mat^{=r}` by per-minor-position charts** is NOT claimed —
  only the single top-left chart `e_β` is built, and the base homogeneity (single orbit) is the honest
  substitute for "local triviality over the whole base". A minor-position chart family would be a
  separate build.
- **Status.** sorry-free.

## Headline — single-chart triviality + rank-orbit homogeneity over the rank-`r` stratum

> **Claim.** For every rank-`r` `B`, (i) a base change carries the model fibre `mult⁻¹(E_r)` onto
> `mult⁻¹(B)`, and (ii) the model chart `Away chartDsig` is the product `SchurLoc ⊗_k sweepFibreRing`.

- **Lean:** `DLNFibre.Core.reducedFibre_singleChartTrivial_reducedVariety` (@ `0abb338`)
- **Gloss.** `[Infinite k] → B.rank = r → (∃ P, fibre d B = (P•·) '' fibre d (normalForm …)) ∧
  Nonempty (Away (chartDsig d r) ≃ₐ[k] SchurLoc … ⊗[k] sweepFibreRing d r)`.
- **Proved.** Conjunction of B4 and B2. sorry-free.
- **Assumed.** `[Infinite k]`.
- **Cited.** as B2 + B4.
- **Deferred.** the per-minor-position open cover (see B4 Deferred); the scheme-cut version (reducedness
  wall).
- **Status.** sorry-free + reviewed (fidelity, reviewer agent).

---

### Fidelity review (reviewer agent, PASS WITH CONCERNS → actioned)
- **PASS on formal content.** Reduced-vs-scheme-cut confirmed (`sweepFibreRing` = reduced
  `…⧸ vanishingIdeal`, not `FibreAlg`); `chartGfib` definitionally `map (algebraMap k sweepFibreRing)
  detSchurS` so B1-specialized matches `e_β`'s codomain; B4 `N ≥ 1` genuinely discharged (structural
  in `Fin (N+2)`, not assumed-away); produced `P` is end-factor only (inner units = 1); no
  `LocallyTrivial` predicate anywhere (verified) so the statements assert only the honest conjunction.
- **CONCERN actioned (naming overclaim).** The original names/docstrings said "locally trivial over
  `Mat^{=r}`", which implies a per-minor open cover that is NOT built. Renamed
  `reducedFibre_locallyTrivial_baseChange → reducedFibre_baseChangeHomogeneous` and
  `reducedFibre_locallyTrivial_reducedVariety → reducedFibre_singleChartTrivial_reducedVariety`;
  module title + docstrings reworded to "single-chart triviality + rank-orbit homogeneity" with the
  per-minor open cover explicitly disclaimed in-statement. Rebuilt green, axiom-clean post-rename.

### Wire-up note for the controller
`FibreBundleReduced.lean` is NOT imported in `DLNFibre.lean` (single-writer aggregator). Add at the
tail, after `Core.ChartLocalizedAlgEquiv` and `Core.FibreNormalForm` / `Core.ChartEvalRealize` (its
imports). Suggested:
`import DLNFibre.Core.FibreBundleReduced`.

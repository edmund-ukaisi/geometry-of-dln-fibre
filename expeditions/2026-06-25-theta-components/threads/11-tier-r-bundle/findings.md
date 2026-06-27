# Thread 11 — Tier-R reduced-fibre product trivialization (B1–B4) — certificate

**Formaliser tide (lean-formaliser).** New file `lean/DLNFibre/Core/FibreBundleReduced.lean` (254 LoC),
wired into the aggregator by the controller; whole library green (3781 jobs); all headlines axiom-clean
`[propext, Classical.choice, Quot.sound]` (controller-gated via `#print axioms`).

## HEADLINE — single-chart triviality + rank-orbit homogeneity on the REDUCED variety
The deliverable is the product structure on the **reduced** fibre variety (`sweepFibreRing =
k[Rep]/vanishingIdeal(F)`), NOT the scheme cut `FibreAlg`. It is **single-chart** triviality plus
base-change homogeneity of the rank-`r` stratum — **not** a full per-minor-position open-cover bundle
(that is rung B3, intentionally NOT built; see below).

## Theorems delivered (all sorry-free, axiom-clean)
- **B1 keystone** `mvPolynomialAwayMapTensorAlgEquiv` — reusable, network-free, ANY field `k`, ANY
  `k`-algebra `F`, ANY `f : MvPolynomial ι k`:
  `Away (map (algebraMap k F) f) ≃ₐ[k] (Away f) ⊗[k] F`. Route (Codex-vetted): polynomial base-change
  `algebraTensorAlgEquiv` + `TensorProduct.comm`, then localization base-change
  `IsLocalization.tensorProduct_tensorProduct`, glued by `IsLocalization.algEquivOfAlgEquiv`.
- **B1-specialized** `reducedFibre_chartGfib_tensorEquiv_reducedVariety` —
  `Away chartGfib ≃ₐ[k] SchurLoc ⊗[k] sweepFibreRing`.
- **B2** `reducedFibre_chartDsig_tensorEquiv_reducedVariety` — `[Infinite k]`: composes the BUILT
  `chartLocalizedAlgEquiv` (`e_β`) with B1 ⟹ `Away chartDsig ≃ₐ[k] SchurLoc ⊗[k] sweepFibreRing`.
- **B4** `reducedFibre_baseChangeHomogeneous` — `B.rank = r → ∃ P, fibre d B = (P•·) '' fibre d (normalForm…)`
  (rank-`r` stratum is a single `GL×GL` base-change orbit; reuses `exists_baseChange_of_rank_eq` +
  `image_smul_fibre` + `rank_normalForm`).
- **Headline** `reducedFibre_singleChartTrivial_reducedVariety` — `[Infinite k]`: the conjunction of B4
  and B2 (the rank-`r` stratum is one orbit, and on its model chart the source pivot-chart is a product
  `SchurLoc ⊗ sweepFibreRing`).

## Honesty / scope (reviewer-driven, fidelity PASS WITH CONCERNS → actioned)
The reviewer flagged a naming overclaim: the original `…_locallyTrivial_…` names implied a per-minor open
cover that is **not built** (only the single top-left chart `e_β` exists). Actioned: renamed to
`reducedFibre_baseChangeHomogeneous` / `reducedFibre_singleChartTrivial_reducedVariety`, retitled the
module + docstrings to "single-chart triviality + rank-orbit homogeneity", disclaimed the open cover
in-statement. The formal content was honest throughout (no `LocallyTrivial` predicate; statements assert
exactly the proved conjunction).

## Remaining rungs (precise)
- **B3 — genuine open cover of `Mat^{=r}` by per-minor-position charts. NOT landed, not claimed.** Only
  the one top-left pivot chart `e_β` exists. A real B3 needs a per-minor chart family (each an analogue of
  `e_β` at a different pivot) + transition maps on overlaps — **a separate, larger build; the thread-10
  "2–3 modules" estimate undercounts this** (it assumed the chart family existed). The honest substitute
  landed here is base-change homogeneity (single orbit) + the single model chart.
- Out of scope by design: the scheme-cut (`FibreAlg`) version, which needs the months-scale reducedness
  wall (thread-10 Part 1).

## Reusable spin-out
`mvPolynomialAwayMapTensorAlgEquiv` is fully network-free (no DLN content) — a candidate for promotion to
a generic Core/Mathlib-adjacent lemma (localization-of-base-changed-polynomial ≃ tensor).

## Artifacts
`threads/11-tier-r-bundle/statement-card.md`, `threads/11-tier-r-bundle/codex/b1-tensor-package-{prompt,answer}.md`,
`.../codex/fidelity-{prompt,answer}.md`. Lean: `Core/FibreBundleReduced.lean`.

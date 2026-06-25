# Statement card — `e` (the localized chart `AlgEquiv`)

> **Claim.** On the pivot chart `{ΔPdeep ≠ 0}` of the rank-exactly-`r` product locus `Σ^r`, the
> coordinate ring localized at the deep pivot minor is isomorphic, as a `k`-algebra, to the schur-side
> polynomial ring `MvPolynomial (SchurVar) O(F)` localized at the schur determinant — i.e. the chart
> `Σ^r ∩ U_Δ` trivializes as `Mat^{=r}_Δ × F` at the coordinate-ring level (the homogeneity lever as a
> regular chart `AlgEquiv`, route-β). `k` alg-closed char 0; `N ≥ 1` (as `Fin (N+2)`); `r ≤ d 0`,
> `r ≤ d (last)`.

- **Lean:** `DLNFibre.Core.chartLocalizedAlgEquiv`
  (`lean/DLNFibre/Core/ChartLocalizedAlgEquiv.lean` @ `66029094`)
  (the file is `ChartLocalizedAlgEquiv.lean` but its `namespace` is `DLNFibre.Core`, so the module
  name is not a namespace segment — the fully-qualified decl is `DLNFibre.Core.chartLocalizedAlgEquiv`.)
- **Gloss.** For a dimension vector `d : Fin (N+2) → ℕ` and `r` with `hp : r ≤ d (last)`, `hq : r ≤ d 0`,
  over an `Infinite` field `k`, there is a `k`-algebra equivalence
  `Localization.Away (chartDsig k d r hp hq) ≃ₐ[k] Localization.Away (chartGfib k d r hp hq)`, where
  `chartDsig = mk (vanishingIdeal Σ^r) ΔPdeep ∈ O(Σ^r)` (the deep pivot minor's class) and
  `chartGfib = map (algebraMap k O(F)) detSchurS ∈ MvPolynomial (SchurVar) O(F)`. It is
  `AlgEquiv.ofAlgHom chartPsiLoc chartPhiLoc` of the two localized comorphisms, with both round-trips
  proved.
- **Proved.** The two localized algebra homs `chartPsiLoc : Away dsig →ₐ[k] Away gF` (the Ψ comorphism
  of `Ψ(M,B) = chartGauge(M)⁻¹ • B`, descended through `vanishingIdeal Σ^r` then localized) and
  `chartPhiLoc : Away gF →ₐ[k] Away dsig` (the Φ comorphism of the forward chart map, descended through
  `vanishingIdeal F`), AND the two round-trips `chartPsiLoc ∘ chartPhiLoc = id`,
  `chartPhiLoc ∘ chartPsiLoc = id` — so `chartLocalizedAlgEquiv` is an honest `AlgEquiv`. Sorry-free,
  axiom-clean `[propext, Classical.choice, Quot.sound]`. Both descents ride only `vanishingIdeal`
  (point-realization + clearing-denominators), never a generator-ideal containment (the R2-3b-4 wall is
  structurally avoided).
- **Assumed.** `[Field k] [Infinite k]` (the `Infinite` is used by the Ψ descent's coefficientwise
  zero-test `mvpoly_eq_zero_of_forall_eval_fibre` via `MvPolynomial.funext`; benign at the
  `IsAlgClosed`+`CharZero` DLN scope). `N ≥ 1` (as `Fin (N+2)`); `r ≤ d 0`, `r ≤ d (last)`.
- **Cited.** none — the construction is reproved from the engine (gauge machinery, Schur normal form,
  the LANDED `chartGauge_mem_fibre` realization) and Mathlib v4.29 (`IsLocalization.liftAlgHom`,
  `Localization.algHom_ext`, `MvPolynomial.aevalTower`/`algHom_ext'`, `RingHom.map_det`).
- **Deferred.** `e` is the chart `AlgEquiv` only — it does NOT by itself give `varietyDim Σ^r = δ +
  varietyDim F`. That needs `e` fed (with the two no-drops `hsig`/`hP` + `hF`) into
  `ChartSweepWiring.sweep_of_localizedChartAlgEquiv`; the source no-drop `hsig` (the pp-nodrop cert,
  Fact B `detΔ ∉ P`) is NOT yet built (task #59).
- **Status.** sorry-free + reviewed (controller-spawned reviewer, verdict PASS: statement fidelity,
  honest non-vacuous AlgEquiv with both round-trips genuinely proved, 0 sorry/axiom library-wide
  (`[propext, Classical.choice, Quot.sound]`), both descents avoid the generator-ideal wall, `[Infinite
  k]` benign — all confirmed; the Proved/Assumed/Cited/Deferred split confirmed accurate).

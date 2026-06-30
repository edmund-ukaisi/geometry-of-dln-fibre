# Statement card — `dln_hchart_residual` (#231-proper, the D1 `hchart`)

> **Claim.** At an optimal `v` (`prod H v = B`, `rank B = r`) of the `L = 2` square-Frobenius DLN
> loss, given an invertible `m`-minor of the flat Jacobian (selected loss-entry rows `er`,
> selected flat-coordinate columns `ec`, both injective, `det ≠ 0`), the local RLCT of the loss at
> `v` equals the post-chart sum-of-squares form on `ℝ^m × ℝ^(N−m)` for a **global `C¹`** residual
> `q` and basepoint `(0, t0)`:
> `rlctAt H (dlnLoss H B) v = rlctAtOn (fun p ↦ ∑ p.1 i² + ∑ q p i²) (0, t0)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.dln_hchart_residual`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1HChartResidual.lean` @ `c4ac6729`)
> - **Gloss.** There exist a residual vector field `q : (Fin m → ℝ) × (Fin (flatDim H − m) → ℝ) →
>   EuclideanSpace ℝ (Fin (H 0 · H 2))` and a complement-block basepoint `t0` such that `q` is
>   `ContDiff ℝ 1` and the local RLCT of `dlnLoss H B` at `v` equals the local RLCT of
>   `(s,t) ↦ ∑ᵢ sᵢ² + ∑ᵢ q(s,t)ᵢ²` at `((0 : Fin m → ℝ), t0)`. This is exactly the `hchart`
>   hypothesis the §SEL engine `deepest_le_of_optimal_of_iftResidual` consumes (at `m = nRegL2 H r`,
>   `n = H 0 · H 2`, `Y = Fin (flatDim H − m) → ℝ`).
> - **Proved.** The full chart-transfer to the §SEL sum-of-squares shape, unconditionally from the
>   two stated hypotheses (optimality + invertible minor). Chains, all sorry-free + clean-three:
>   (i) the flatten+translate MP bridge `rlctAt_eq_rlctAtOn_lossFlatShift`;
>   (ii) the right-inverse-exposing IFT chart `rlctAtOn_eq_of_contDiff_chart_rinv` (now also exposing
>   `ContDiffOn ℝ 2 Ψsymm V` on an open `V ∋ 0`);
>   (iii) the flat-space germ split `germA` (`lossFlatShift ∘ Ψsymm =ᶠ ∑ₖ (w(ec k))² + ∑ᵢⱼ rawResid²`
>   — selected loss entries become coordinates via the banked `selected_lossEntry_germ`, the rest are
>   the residual);
>   (iv) the bump-globalised residual `exists_contDiff_eventuallyEq_of_contDiffOn` (a `ContDiffOn`
>   map on the IFT nbhd → a GLOBAL `C¹` map agreeing near the basepoint, via a `ContDiffBump`);
>   (v) the measure-preserving reindex `splitHomeo : ℝ^N ≃ₜ ℝ^m × ℝ^(N−m)` (`rlctAtOn_comp_homeomorph`).
> - **Assumed.** `prod H v = B` (optimality); `(jacFlatL2 H v).submatrix er ec).det ≠ 0` and `er`,
>   `ec` injective (the invertible flat-Jacobian minor — produced upstream by `exists_jacFlatL2_minor`
>   from the H_indep rank bound `nReg ≤ jacFlatL2.rank`). `B.rank = r` is carried to pin
>   `m = nRegL2 H r` at the use-site (semantic tie; not consumed in the proof body).
> - **Cited.** none. All Mathlib tools (`ContDiffBump`, `piEquivPiSubtypeProd`/`piCongrLeft` MP,
>   `contDiff_euclidean`, the C^r IFT `ContDiffAt.toOpenPartialHomeomorph`/`to_localInverse`) are
>   library facts; the DLN-specific pieces (chart `chartΦ`, the rank bound, the germ blocks) are
>   banked in the D1HChart* slot and reproved there.
> - **Deferred.** none *for this statement*. (Downstream, `deepest_le_of_optimal_of_iftResidual`
>   still carries `hRne` (slice residual a.e.-nonzero), `hDeepest` (#44), `hDegraded` (R1-at-M') as
>   named hypotheses; those are NOT part of this `hchart` and are tracked separately. This card
>   discharges only the chart-transfer obligation #225.)
> - **Route.** Sub-build ladder banked by genm-d1ladder (STEP1, #229, #230, #231-infra + germ blocks);
>   this thread (genm-d1wire) executed the 5 plumbing tiles: (1) MP `splitHomeo` + selected-slot read;
>   (2) strengthened rinv corollary exposing `Ψsymm` `C²` (additive `ContDiffOn` field on
>   `exists_boundedUnit_chart_of_contDiffAt`, threading the already-proven internal `hUsymm'_cd`);
>   (3) `germA` flat-space loss split (`sum_split_selected` + `selected_lossEntry_germ`);
>   (4) bump-globalization; (5) the assembly.
> - **Status.** sorry-free + reviewed (independent reviewer + decorrelated Codex xhigh: fidelity-PASS,
>   non-vacuity confirmed — `q` is the genuine loss residual, `C¹` premise honest, gate-4
>   existential-`Wᶜ` preserved through `chartΦ`; clean-three `[propext, Classical.choice, Quot.sound]`).

# Statement card — D1 IFT-chart producer at a general optimal `v` (L = 2)

> **Claim.** At L = 2, the D1 `≥`-leg per-point obligation `rlctAt_deepest_le_of_optimal`
> (Skeleton:1172) — `rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v` at a general optimal
> `v ∈ optimalSet H B` — reduces, GIVEN the general-`v` IFT-chart certificate `GeneralVChartL2` (the
> genuinely-Mathlib-lacking constant-rank quadratic split, bundled) and the existing `#44` deepest-side
> equality `hDeepest`, to mechanical wiring + the banked residual-core diffeo transfer. The reduction is
> proved sorry-free; the certificate's diffeo data discharges `hCore` in-module (NOT a bare hypothesis).
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_le_of_optimal_of_chart_certificate`,
>   `DLNFibre.DLN.RLCT.GeneralVChartL2` (structure), `DLNFibre.DLN.RLCT.GeneralVChartL2.ofExactGerm`
>   (non-vacuity smart constructor)
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1ChartProducerL2.lean` @ `<commit-sha>`)
> - **Gloss.** `GeneralVChartL2 H B v coreDeepest` bundles, over abstract finite-dim normed spaces
>   `Reduced`/`Gauge` with `m = nReg = r·(H⁰+Hᴸ−r)`: the IFT chart transfer
>   `rlctAt (dlnLoss H B) v = rlctAtOn F (0,(t0,g0))`; the post-chart sum-of-squares form
>   `F = ∑ s² + Q` with `Q ≥ 0`; the slice residual `R = Q(0,·)` measurable and a.e.-nonzero near the
>   basepoint; the quasi-split comparison `(∑ s²)+R ≤ C·F`; and the bounded-unit residual-core local
>   diffeo `Φ` with `R = (core₀∘fst)∘Φ` and `coreDeepest = rlctAtOn core₀ t0`. The producer theorem
>   takes such a `Γ` plus `hDeepest : rlctAt (dlnLoss H B) deepest = nReg/2 + coreDeepest`, and concludes
>   `rlctAt (dlnLoss H B) deepest ≤ rlctAt (dlnLoss H B) v`.
> - **Proved.** The reduction: from `Γ` + `hDeepest`, the conclusion follows by (1)
>   `hCore_slice_residual_eq` on `Γ`'s diffeo data ⟹ `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`, (2)
>   `hCore := le_of_eq (hcoreDeepest.trans hCoreEq.symm)`, (3) the banked `deepest_le_of_optimal_chart`
>   (which itself runs the quasi-split engine for `hAtV` + cancels `nReg/2`). Sorry-free, axiom profile
>   `[propext, Classical.choice, Quot.sound]` (CLEAN-THREE, no `sorryAx`/`monomial_rlct`). `m` pinned to
>   `nReg`. Non-vacuity SHOWN: `ofExactGerm` builds the certificate from a strictly-realizable weaker
>   premise (identity residual diffeo), and a concrete `example` inhabits it from the chart transfer
>   alone (`m=0`, `core₀=R=Q≡1`).
> - **Assumed.** (i) `GeneralVChartL2` (the IFT chart at general `v` — the constant-rank quadratic
>   split, Mathlib-lacking, NOT built here); (ii) `hDeepest` = the existing #44 Skeleton sorry
>   `deepest_regular_core_normal_form`, consumed as a hypothesis, never re-proved.
> - **Cited.** None new. Reuses the banked `deepest_le_of_optimal_chart`, `hCore_slice_residual_eq`,
>   `rlct_quasiSplit_ge`, `deepest_le_of_optimal_via_L2_ge` (all clean-three in `D1ChartProducer` /
>   `DeepestMinRlct`).
> - **Deferred.** The construction of a `GeneralVChartL2` instance at the actual DLN loss — i.e. the IFT
>   constant-rank quadratic split at a general `v` (the G1 `Φ:(T,g)↦((T₁,(I+G(g))·T₂),g)`,
>   `R=‖T₁(I+G)T₂‖²`). This is "a major multi-tide build, rung-1-scale, WALL-FREE but substantial"
>   (Item 81), strictly harder than the still-open deepest analog `deepest_gauge_squeeze_exists`. NOT
>   attempted here. General-L is the named research wall #120 — NOT touched (scope L = 2 only).
> - **Scope caveat (Codex red-team).** The certificate interface EXCLUDES the terminal / direct-Morse
>   case where the reduced core is identically zero: then `hRform` forces `R ≡ 0`, contradicting `hRne`.
>   Such a `v` needs a separate (coreless) route. `hRne` is a.e.-nonzero NEAR the basepoint, so the core
>   vanishing AT its deepest point is not a contradiction.
> - **Circularity audit (Codex).** PASS. No field assumes the conclusion, `hAtV`, or `hCore`. `hchart`
>   is an RLCT transfer to `F` (not the D1 inequality); `hcoreDeepest` ties `coreDeepest` to the reduced
>   core (not `hCore`); `hCore` is PROVED from the diffeo, not assumed.
> - **Status.** sorry-free; awaiting reviewer fidelity check.

## What this banks vs what remains

- **Banks:** the D1-leg reduction is now `deepest_le_of_optimal_chart` (PART a/b, `D1ChartProducer`) +
  THIS producer — together they reduce `rlctAt_deepest_le_of_optimal` (Skeleton rung 2/5) at L = 2 to
  EXACTLY: a `GeneralVChartL2` instance (the IFT split) + the existing #44. The certificate pins the
  exact interface the unbuilt chart must satisfy.
- **Remains for the leg:** build a `GeneralVChartL2` instance at the real loss (the chart); discharge
  #44. Neither is in this module's scope.

## Consults

- `threads/04-d1-scope/codex/d1-l2-producer-scope-{prompt,answer}.md` — verdict (A): state as a
  sorry-free reduction taking the chart as a named certificate; prove `hCore` in-module; tie `m=nReg`.
- `threads/04-d1-scope/codex/d1-l2-vacuity-{prompt,answer}.md` — circularity PASS; fields jointly
  satisfiable; `ofExactGerm` is the best non-vacuity witness; terminal-core scope caveat surfaced.

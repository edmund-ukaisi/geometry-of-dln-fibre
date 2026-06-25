# Statement card — `codim(fibre d B) = C + δ` (the expedition's central result)

> **Claim.** For a deep linear network with dimension vector `d` (`N ≥ 1` layers), the geometric
> codimension of the multiplication-map fibre `mult⁻¹(B)` over any rank-`r` target `B` is the
> combinatorial codimension `C = cCodim d r` plus the matrix-stratum shift `δ = r·(d_N + d_0 − r)`:
> `codim (mult⁻¹(B)) = C + δ`. The new geometric content underneath the (Cited) RLCT `= ½·codim`
> reading. `k` algebraically closed, char 0; `N ≥ 1` (as `Fin (N+2)`); `r ≤ d 0`, `r ≤ d (last)`.

- **Lean:** `DLNFibre.Core.codimRepCanonical_fibre_eq_cCodim_add_shift`
  (`lean/DLNFibre/Core/FibreCodimFinal.lean` @ `947c4eb9`).
  Companion (the normal-form fibre directly):
  `DLNFibre.Core.codimRepCanonical_fibre_normalForm_eq_cCodim_add_shift`.
  Penultimate rung (`hSweep`): `DLNFibre.Core.varietyDim_sweepSigma_eq_shift`.
- **Gloss (minimal-hypothesis form, post-#69 tightening).** For `d : Fin (N+2) → ℕ`, `r`,
  `h : (kostantPartitions d r).Nonempty`, and a matrix `B : Matrix (Fin (d (last))) (Fin (d 0)) k`
  with `hB : B.rank = r`:
  `codimRepCanonical (fibre d B) = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (last) + d 0 − r) : ℕ) : ℕ∞)`.
  `codimRepCanonical` is the geometric codimension at the canonical linear flattening (the
  `Ideal.height` of the vanishing ideal of `canonicalCoord '' (·)`); `cCodim d r` is the type-A
  `Ext`-pairing combinatorial codimension `C`; the shift is `δ = r·(d_N + d_0 − r) = card SchurVar`.
  The rank bounds `r ≤ d (last)`, `r ≤ d 0` and `N ≥ 1` are NO LONGER hypotheses (reviewer-codim #68
  flagged them redundant; #69 dropped them) — they are derived inside the proof: `r ≤ d k` from
  `corner_le_dim_of_mem h.choose_spec` (a corner-`r` Kostant partition forces `r ≤ d k` at every
  vertex), and `(0 : Fin (N+2)) ≠ Fin.last (N+1)` vacuously (`0.val = 0 ≠ N+1`). The intermediate
  `codimRepCanonical_fibre_normalForm_eq_cCodim_add_shift` still carries `hp hq hN` (its conclusion
  names `normalForm … hp hq`, so they are type arguments there, not droppable).
- **Proved.** The full chain, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`:
  - **`hSweep`** (`varietyDim_sweepSigma_eq_shift`): `varietyDim Σ^r = δ + varietyDim F`. Built by
    feeding `(chartDsig, chartGfib, chartLocalizedAlgEquiv, hsig, hP, hF)` into the LANDED wiring
    `ChartSweepWiring.sweep_of_localizedChartAlgEquiv`. `e = chartLocalizedAlgEquiv` and `hsig`
    instantiate definitionally (no glue).
  - **`hsig`** (`SourceNoDrop.ringKrullDim_localizationAway_chartDsig_eq`): the source no-drop
    `ringKrullDim (Away chartDsig) = ringKrullDim O(Σ^r)`, over the rank-exactly-`r` ring. Via the
    LANDED reducible-ring no-drop at `p₀ = P/I_eq` (`P` = corner-`r` minimiser's orbit-rank-locus
    ideal). **Fact B** (`detΔ ∉ P`, `chartDsig_not_mem_partitionIdeal`): the realizer has product
    rank `r`, an end-factor base change carries `mult M₀` to the rank-`r` normal form (top-left
    minor `= 1`), staying in `orbitRankLocus M₀`. `I_eq ⊆ P` FREE
    (`vanishingIdeal_sweepSigma_le_orbitRankLocus`); `p₀` full-dim via the ℕ∞ catenary. No density /
    rank-raising theorem, no `I_eq = I_le` ideal equality.
  - **`hP`** (`ringKrullDim_localizationAway_chartGfib_eq`): the schur-side no-drop. Via
    `SchurSideNoDrop.ringKrullDim_localizationAway_eq_of_schurSide` at the top prime `PF/IF` of the
    fibre ring `O(F)` (`exists_minimalPrime_ringKrullDim_quotient_ge` + DoubleQuot) with the
    unit-`k`-coefficient witness `detSchurS_ne_zero`.
  - **`hF`** (`vanishingIdeal_sweepFibre_ne_top` / `fibre_normalForm_nonempty`): the fibre over the
    normal form is nonempty (the realizer base-changes onto it).
  - **arbitrary `B`**: lifted from the normal-form fibre by the LANDED same-rank invariance
    `FibreNormalForm.codimRepCanonical_fibre_eq_of_rank_eq`.
  - **`hClosure`** (`varietyDim Σ^r = varietyDim Σ̄^r`): carried by the route-c assembly
    `ClosureBridge.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep_closure`, proved in-repo by
    the codimension sandwich (zero-cite).
- **Assumed (headline `codimRepCanonical_fibre_eq_cCodim_add_shift`, minimal form).**
  `[Field k] [IsAlgClosed k] [CharZero k]` and **`k : Type` (universe 0)**;
  `(kostantPartitions d r).Nonempty`; the target rank `B.rank = r`. That is ALL — `r ≤ d 0`,
  `r ≤ d (last)`, and `N ≥ 1` are derived, not assumed (#69). (The intermediate normal-form theorem
  still lists `hp hq hN` since they are type arguments to `normalForm` in its conclusion.)
- **Cited.** none for the codimension itself — the geometric content is reproved from the engine
  (orbit-closure machinery, the Schur chart trivialization `e`, the no-drops, the closure sandwich)
  and Mathlib v4.29. (The downstream RLCT `= ½·codim` reading is the Cited Aoyagi/Watanabe bound,
  not part of this card.)
- **Scope note (universe).** The final results are at `k : Type` (universe 0), not the wiring's
  general `Type u`. `SchurVar : Type 0`, and the schur-side no-drop constrains `ι A : Type u` (same
  universe); generalizing `ι` to `Type*` cascades a universe constraint into the affine no-drop
  (`R : Type u`, `k : Type u`). This is the honest DLN-payoff scope (ℝ/ℂ and their algebraic closures
  are `Type 0`) and loses nothing for the application; `hsig`/`e`/the route-c assembly remain general
  `Type u`. Lifting the headline to `Type u` requires generalizing the affine no-drop to
  `R : Type w, k : Type u` — a multi-module universe lift, roadmap-able, not load-bearing for DLNs.
- **Deferred.** The arbitrary-`B`→`E` `G1`-lift outside the rank-`r` normal-form base-change (task
  #52, `BundleShiftInterface`) is a separate scope; here `B` ranges over rank-`r` matrices and the
  same-rank invariance handles it directly. The θ-count fidelity (`(3,3,3)` θ=2-vs-3, task #54) is
  orthogonal.
- **Status.** sorry-free + axiom-clean library build green; pending controller aggregation into
  `DLNFibre.lean` and an independent reviewer fidelity check.

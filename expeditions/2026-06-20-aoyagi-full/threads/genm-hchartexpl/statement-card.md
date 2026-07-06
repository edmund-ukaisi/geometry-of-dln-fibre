# genm-hchartexpl — Route-A "everything else is banked" landed; the wall is Codex step 5

Charged to prove `hchart_explicit`, the sole remaining sorry for the L=2 headline
(`aoyagi_learning_coefficient_L2`), via the explicit `Ψsymm`-free Schur corner-elimination chart.

## Outcome (honest)

The **downstream half** of the crux — Codex's decomposition steps 6–9, i.e. the entire
"given the explicit chart, everything else is banked" claim — is now **sorry-free, clean-three, and
pushed** as `d1ge_L2_hAtV_of_explicit_chart` (`D1L2SchurAssembly.lean`). This is a genuine reduction:
it consumes the explicit-chart data as hypotheses and produces the D1 `≥`-leg producer conclusion by
composing four ALREADY-BANKED bricks.

The **upstream half** — Codex's **step 5**, constructing the explicit rational corner-elimination map
as a *local measurable chart with Jacobian/unit control* (the general-`v` chart transfer `hchart` +
the slice factorisation `hfact`) — is **NOT landed**. It is a fresh multi-file analytic build,
independently flagged as the wall by (a) the banked Codex xhigh crux analysis
(`threads/genm-hAtV/codex/crux-answer.md`, step 5 = "the most likely hidden wall … Lean may make the
explicit chart/Jacobian/measurable-equivalence packaging painful") and (b) the repo's own Item-81
assessment (the general-`v` chart is "a major multi-tide build … strictly harder than the still-open
deepest analog"; the deepest analog `deepest_gauge_squeeze_exists` is itself still `sorry`). The
existing `d1ge_L2_hAtV_explicit` sorry is therefore **left in place** — not laundered into a
differently-named sorry.

## Files

- **NEW** `lean/DLNFibre/DLN/RLCT/Validate/D1L2SchurAssembly.lean` — the Route-A assembly. Controller
  to wire into the aggregator `DLNFibre.lean` (single-writer) if desired; NOT yet consumed by the
  headline (it plugs in once the step-5 chart is built).

## Theorem delivered (sorry-free, clean-three)

`d1ge_L2_hAtV_of_explicit_chart` (`D1L2SchurAssembly.lean`):

    (H : Fin 3 → ℕ) (r) (B) (v)
    (qₑ : (Fin (nRegL2 H r) → ℝ) × Y → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 1 qₑ) (t0 : Y)
    (hchart : rlctAt H (dlnLoss H B) v = rlctAtOn (∑ p.1² + ∑ qₑ p²) (0, t0))
    (hRne  : slice ∑ qₑ(0,·)² a.e.-nonzero near t0)
    (e     : Y ≃ₜ (Fin (flatDim (H−r)) → ℝ) × (Fin specDim → ℝ))  (he_mp, he_emb)
    (u : Y → ℝ) (hu_meas, ua ub, 0 < ua, hu_bnd : bounded-unit)
    (hfact : ∀ t, ∑ qₑ(0,t)² = u t · dlnLoss (H−r) 0 ((paramsEquivFlat (H−r)).symm (e t).1))
    ⊢ ∃ P : Params (H−r), nRegL2 H r / 2 + rlctAtOn (dlnLoss (H−r) 0) P ≤ rlctAt H (dlnLoss H B) v

English: at a general optimal `v`, GIVEN the explicit chart transfer `hchart` and the slice
factorisation `hfact` (the slice residual `= bounded-unit · reduced-core, reindexed`), the producer
conclusion holds with witness `P = (paramsEquivFlat (H−r)).symm (e t0).1`.

Proof = the banked composition:
- `rlctAt_ge_nReg_add_slice_of_residual` (step 6) → `nReg/2 + rlctAtOn(slice) t0 ≤ rlctAt v`;
- `rlctAtOn_unit_invariant_aux` (step 8) peels `u`;
- `rlctAtOn_comp_homeomorph` (`e`) reindexes onto flat-core × spectator;
- `rlctAtOn_spectator_peel` (step 7, the flat-Fubini brick) drops the spectator;
- `rlctAtOn_comp_homeomorph` (`(paramsEquivFlat (H−r))` forward) transports back to `Params (H−r)`.

Axiom footprint (forced `#print axioms`): `[propext, Classical.choice, Quot.sound]` — clean-three, no
`sorryAx`, no `monomial_rlct`, no new axiom.

## The isolated wall (what the producer sorry still needs = Codex step 5)

Produce, at the real DLN loss for a general optimal `v`, an instance of the hypotheses above:
`qₑ` (the explicit Schur residual — Codex takes `qₑ = M22 − B22 ∘ explicit-inverse`, rational on
`{det X ≠ 0, det M11 ≠ 0}`, bump-globalised to `C¹`), the chart transfer `hchart`
(`rlctAtOn_eq_of_contDiff_chart`-style, with the EXPLICIT rational corner map, NOT the germ-discarding
`Ψsymm`), `hRne` (reduced-core non-vanishing — needs `H s − r > 0`, available from the caller's
`hpos`), and the slice factorisation `hfact` (the Schur identity `M22 − M21 M11⁻¹ M12 = A0red · A1red`
on the slice, `A0red = W − Z X⁻¹ Y`, `A1red = V − U M11⁻¹ M12`, sympy-verified `‖Δ‖ ≈ 1e-15`).

This is the general-`v` analogue of the deepest-point gauge chart (`DeepestGaugeChart` /
`GeneralVChartL2`'s "genuinely-unbuilt analytic content"). Mathlib has `fromBlocks_multiply` +
`fromBlocks_eq_of_invertible₁₁` (block LDU) for the Schur ALGEBRA; the chart-CERTIFICATION (local
measurable chart + bounded Jacobian) is the painful part.

## ∀-L lift note

The assembly is stated with the reduced widths `fun s => H s - r` and an abstract flat slice `Y` +
spectator, so the peel/reindex structure lifts verbatim; the `nRegL2`/reduction-brick tie scopes it to
`Fin (2+1)`. The ∀-L version is the same corner-elimination iterated across layers, feeding the same
four bricks — this reduction is the base-case downstream.

## Consults

- Codex CLI **unavailable this tide** (`Not logged in`; operator-gated, cannot fix). Relied on the
  banked genm-hAtV Codex xhigh crux analysis (decorrelated) for the step-5 wall verdict, plus the
  repo's Item-81 assessment.

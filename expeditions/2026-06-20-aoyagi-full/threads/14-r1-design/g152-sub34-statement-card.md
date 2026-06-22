# Statement card — #44c `deepest_gauge_chart_exists` (sub-34)

**Status: ROUTE-ANALYSED, NOT YET PROVEN.** Held on an interface decision (crux2 owns the
`DeepestGaugeChart` structure + sub-5). No Lean written — three converged findings indicate the
banked structure is the wrong shape, and building 600+ lines against it would be the
visible-progress trap (CLAUDE.md disposition).

## Target (as banked by crux2, `DeepestGaugeChart.lean`)
```lean
theorem deepest_gauge_chart_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nonempty (DeepestGaugeChart H r B hB hr hL)
```
`DeepestGaugeChart` carries: `split` (MP reindex flat ≃ₜ reg×(core×spectator)) + `split_mp`/`split_zero`;
`chart : Flat ≃ₜ Flat` (global) + `Dchart` + `hasDeriv : ∀x` + `jac_unit` + `chart_zero`; `loss_form`
(germ equality `dlnLoss∘psymm∘chart =ᶠ ∑reg² + dlnLoss M 0(core)`).

## English gloss
At a rank-`r`-exact deepest point, a coordinate change on the flat parameter space splits it into
`nReg = r(H₀+H_last−r)` regular gauge directions, the reduced core `Params M` (`M = H−r`), and
`nGauge` spectators, under which `dlnLoss H B` pulls back to `∑ regular² + dlnLoss M 0(core)` near `0`.

## Numeric sanity checks (all PASS)
- `nReg = r(H₀+H_last−r)` matches the regular-residual Jacobian rank at `w0`: (2,2,2)r1→3, 3-layer
  (3,3,3,3)r1→5 (finite-diff rank).
- Dimension split `flatDim H = nReg + flatDim M + nGauge` exact: 8=3+2+3, 18=8+2+8, 27=5+12+10.

## The three route findings (decorrelated: exact-numeric + Codex xhigh; full notes in
`codex/g152-sub34-finding.md`)
1. The squeeze against the RAW reduced chain `‖T·S‖²` is FALSE for matrices (`g=(I−VY)⁻¹` between
   T,S; `‖TgS‖²/‖TS‖²→∞` as `TS→0`). The cert's gauge-normalized `T̃` is right; the core must be in
   `T̃`-coords. (The scalar (2,2,2)r1 case hides this.)
2. `Dchart`/`jac_unit` are NOT dead weight under the S1.1 transport route: the regular-residual c-o-v
   is a genuine diffeo, and unweighted `rlctAt(F∘π)=rlctAt(F)` is FALSE (S1.1 docstring: `(u,uv)⟹1/2≠1`).
3. (Decisive.) The structure's GLOBAL `chart : Flat ≃ₜ Flat` + `∀x HasFDerivAt` over-reaches:
   `rlctAtOn` is local; the honest gauge chart is a local diffeo only (inverse uses `A⁻¹`,`(I−VY)⁻¹`);
   S1.1 has global `IsProperMap`+`Surjective`. No `PartialHomeomorph`-RLCT lemma exists in the codebase.

## Two routes
- **R-S1.1** (structure as-is, populable but heavy ~600-1500 LoC): local gauge c-o-v + global
  cutoff-extension to `Flat ≃ₜ Flat` + `Dchart` + `jac_unit` + `loss_form` germ; sub-5 transports via
  `weightedThreshold_transport` + `rlctAtOn_unit_invariant_aux`. Buildable WITHOUT changing crux2's
  file (I only fill sub-3/4). Confirmed populable: a local diffeo at 0 (invertible `D(0)`) extends to a
  global self-homeo via a smooth cutoff to identity outside a ball.
- **R-squeeze** (recommended, lighter, purely local): requires crux2 to replace `loss_form` equality
  with a squeeze datum `c₁Φ ≤ loss ≤ c₂Φ` near 0; sub-5 = `rlctAtOn_squeeze` + spectator-peel(#52) +
  `rlct_additive_smooth_block`. Reuses only existing infra. The one real obligation: the matrix
  ideal-membership squeeze (`loss − Φ ∈ ideal(reg)`, bounded near `w0`).

## Blocker
crux2's interface decision (owns sub-5 + the structure). Default absent a reply: R-S1.1 (respects
single-writer ownership). Recommendation: R-squeeze (if crux2/controller direct the structure change).

## Pinned commit
`fm2/deepest-gauge-chart-sub34` @ a42f57d (diligence; baseline GREEN, 0 Lean LoC delta).

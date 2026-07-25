# Statement card — RUNG 5b: chart Jacobian (STAGE 2) + `Chart` L6 fields (STAGE 3)

- **Status.** sorry-free (pending fidelity review).
- **Modules.**
  - STAGE 1 (funext + atom defs, routeP-p1): `lean/DLNFibre/DLN/Aoyagi/Corank2GWrapDecomp.lean`.
  - STAGE 2+3 (this card, decomp-5b): `lean/DLNFibre/DLN/Aoyagi/Corank2ChartJac.lean`.
- **Lane branch.** `expedition/aoyagi-engine-5b-decomp`, rebased onto routeP-p1's STAGE 1 @ `c5012ce22`.
- **Task.** #133 (rung 5b of #130); architecture settled by fork #138 (verdict (B) DECOMPOSED).
- **Axioms.** `#print axioms` (force-elaborated) = `[propext, Classical.choice, Quot.sound]` on all
  STAGE 2/3 results (clean-three, no `sorryAx`).

## The claim (from `chart-architecture-fork.md`, sympy-exact; re-verified numerically)

STAGE 1 (banked by routeP-p1): `gFaithful = shearH ∘ permP ∘ bbA0 ∘ bbA1` (`gFaithful_decomp`),
`gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1` (`gWrap_decomp`). STAGE 2/3 read the Jacobian off the
atoms:

```
|jacDet gWrap u| = |u₀|⁷ · |u₁|³ · |u₂₀|⁸        (jac = [0↦7, 1↦3, 20↦8], unit ≡ 1)
```

| atom (Corank2GWrapDecomp) | map | `|jacDet|` |
|---|---|---|
| `bbA1` | `blockBlowupMap {1,5,6,7} 1` | `|u₁|³` |
| `bbA0` | `blockBlowupMap {0,…,7} 0` | `|u₀|⁷` |
| `permP` | coord permutation `permIdx = [8,9,10,11,1,5,6,7,0,2,3,4]`, fixed `12..20` | `1` |
| `shearH` | unipotent shear (reads `{0,1,2,3,12..19}`, writes `4..11`) | `1` |
| `sigmaPiv` | `blockBlowupMap {0..7,20} 20` | `|u₂₀|⁸` |

## Lean signatures (STAGE 2/3, `Corank2ChartJac`)

- `abs_jacDet_gFaithful (u) : |jacDet gFaithful u| = |u 0|^7 * |u 1|^3`.
- `abs_jacDet_gWrap (u) : |jacDet gWrap u| = |u 0|^7 * |u 1|^3 * |u 20|^8` — the L6 Jacobian.
- `gWrap_hjac (u) : |jacDet gWrap u| = jacWeight jacWrap u * |(1:ℝ)|` — the `Chart.hjac` field (unit ≡ 1),
  `jacWrap = [0↦7, 1↦3, 20↦8]`, `jacWeight_jacWrap : jacWeight jacWrap u = |u 0|^7*|u 1|^3*|u 20|^8`.
- `analyticOnNhd_gWrap : AnalyticOnNhd ℝ gWrap Set.univ` — the `Chart.hg_analytic` field.
- `injOn_gWrap : Set.InjOn gWrap (Set.univ \ excepWrap)` — the `Chart.hg_inj` field,
  `excepWrap = {u | jacWeight jacWrap u = 0}` (= {u₀=0}∪{u₁=0}∪{u₂₀=0}).
- `volume_excepWrap : volume excepWrap = 0`, `measurableSet_excepWrap : MeasurableSet excepWrap` —
  `Chart.hexcep_null`/`hexcep_meas`.
- `jacDet_shearH (u) : jacDet shearH u = 1` — via the bridge `shearH_eq : shearH = blockShear shearPhiH`
  + the GENERAL shear-pin `jacDet_blockShear` (handles the nonlinear `shearPhiH`).
- `abs_jacDet_permP (u) : |jacDet permP u| = 1` — via `permSigma = Equiv.ofBijective permIdx` + the
  reusable atom `abs_jacDet_permCoord (σ : Equiv.Perm (Fin D)) (u) : |jacDet (fun w i ↦ w (σ i)) u| = 1`.

## Method / fidelity notes

- Jacobian via `jacDet_comp` over the banked per-atom Jacobians (`jacDet_blockBlowupMap` (O9),
  `jacDet_blockShear` (shear-pin), `det_permutation` for `permP`). **NO 21×21 determinant.**
- The nonlinear-`shearH` `jacDet = 1` "wrinkle" is discharged by the banked general shear-pin
  `jacDet_blockShear` (NOT a bespoke unit-triangular argument), after the `shearH_eq` bridge.
- The banked two-sided `hideal` (`Corank2CoreGenWrap.hideal_coreGen_fwd`/`_bwd`) is **unchanged**: stated
  for the SAME `gWrap`; the decomposition is used only for the Jacobian. NO crux re-proof.
- Payoff consistency: binding axis `E = coord 0`, `(jac₀+1)/(2·bexp₀) = (7+1)/2 = 4`; `c₁₁ = coord 20`,
  `(8+1)/2 = 4.5 > 4` (non-binding); `α = coord 1` has `bexp = 0` (not an exceptional divisor). ⟹ `rlct = 4`.

## Fidelity question for review

Do the Lean statements match the claim: (a) is `shearH`/`shearH_eq` the FAITHFUL shear (all bilinear
terms, not a proxy); (b) is `jacWrap = [0↦7,1↦3,20↦8]` the correct `Chart.jac`; (c) is `excepWrap` the
right exceptional locus for `hg_inj`; (d) does `abs_jacDet_gWrap` match the sympy monomial `u₀⁷·u₁³·u₂₀⁸`?

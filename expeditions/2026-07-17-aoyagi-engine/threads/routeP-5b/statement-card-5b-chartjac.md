# Statement card — RUNG 5b (L6): the DECOMPOSED (3,3,4) chart Jacobian

- **Status.** sorry-free (pending fidelity review).
- **Module.** `lean/DLNFibre/DLN/Aoyagi/Corank2ChartJac.lean`
- **Lane branch / SHA.** `expedition/aoyagi-engine-5b-decomp` @ `178909f596d821d37aca23bee9ffc5018eaea223`
- **Task.** #133 (rung 5b of #130); architecture settled by fork #138 (verdict (B) DECOMPOSED).
- **Axioms.** `#print axioms` (force-elaborated) = `[propext, Classical.choice, Quot.sound]` on all 9
  delivered results (clean-three, no `sorryAx`).

## The claim (from `chart-architecture-fork.md`, sympy-exact; re-verified numerically here)

The folded faithful (3,3,4) chart `gFaithful` equals the banked-atom composite, and the full chart
`gWrap = sigmaPiv ∘ gFaithful` has Jacobian the pure monomial `|u₀|⁷·|u₁|³·|u₂₀|⁸`:

```
gFaithful = shearH ∘ permP ∘ blowA0 ∘ blowA1
|jacDet gWrap u| = |u₀|⁷ · |u₁|³ · |u₂₀|⁸        (jac = [0↦7, 1↦3, 20↦8], unit ≡ 1)
```

| atom | map | `|jacDet|` |
|---|---|---|
| `blowA1` | `blockBlowupMap {1,5,6,7} 1` | `|u₁|³` |
| `blowA0` | `blockBlowupMap {0,…,7} 0` | `|u₀|⁷` |
| `permP` | coord permutation `[8,9,10,11,1,5,6,7,0,2,3,4]`, fixed `12..20` | `1` |
| `shearH` | unipotent shear (reads `{0,1,2,3,12..19}`, writes `4..11`) | `1` |
| `sigmaPiv` | `blockBlowupMap {0..7,20} 20` | `|u₂₀|⁸` |

## Lean signatures (delivered)

- `gFaithful_decomp : gFaithful = shearH ∘ permP ∘ blowA0 ∘ blowA1` — the extensional identity (self-gate).
- `abs_jacDet_gWrap (u) : |jacDet gWrap u| = |u 0|^7 * |u 1|^3 * |u 20|^8` — the L6 Jacobian.
- `gWrap_hjac (u) : |jacDet gWrap u| = jacWeight jacWrap u * |(1:ℝ)|` — the `Chart.hjac` field (unit ≡ 1),
  `jacWrap = [0↦7, 1↦3, 20↦8]`, `jacWeight_jacWrap : jacWeight jacWrap u = |u 0|^7*|u 1|^3*|u 20|^8`.
- `analyticOnNhd_gWrap : AnalyticOnNhd ℝ gWrap Set.univ` — the `Chart.hg_analytic` field.
- `injOn_gWrap : Set.InjOn gWrap (Set.univ \ excepWrap)` — the `Chart.hg_inj` field,
  `excepWrap = {u | jacWeight jacWrap u = 0}`.
- `volume_excepWrap : volume excepWrap = 0`, `measurableSet_excepWrap : MeasurableSet excepWrap` —
  the `Chart.hexcep_null`/`hexcep_meas` fields.
- Reusable engine atom: `abs_jacDet_permCoord (σ : Equiv.Perm (Fin D)) (u) : |jacDet (fun w i ↦ w (σ i)) u| = 1`.

## Method / fidelity notes

- Jacobian via `jacDet_comp` over the banked per-atom Jacobians (`jacDet_blockBlowupMap` (O9),
  `jacDet_blockShear` (shear-pin — the nonlinear-`shearH` `jacDet = 1` "wrinkle" discharged by the banked
  unit-triangular lemma, NOT a new determinant), `det_permutation` for `permP`). **NO 21×21 determinant.**
- The permutation `permP` is kept **explicit** (the load-bearing caveat, fork #138): the funext
  `gFaithful_decomp` is the self-gate — it would not close were `permP` omitted or the order reversed.
- The banked two-sided `hideal` (`Corank2CoreGenWrap.hideal_coreGen_fwd`/`_bwd`) is **unchanged**: it is
  stated for the SAME `gWrap`; the decomposition is used only for the Jacobian. NO crux re-proof.
- Payoff consistency: binding axis `E = coord 0`, `(jac₀+1)/(2·bexp₀) = (7+1)/2 = 4`; `c₁₁ = coord 20`,
  `(8+1)/2 = 4.5 > 4` (non-binding); `α = coord 1` has `bexp = 0` (not an exceptional divisor). ⟹ `rlct = 4`.

## Fidelity question for review

Do the Lean statements match the claim — in particular: (a) is `gFaithful_decomp` the FAITHFUL shear
(all bilinear terms present, not a linear proxy); (b) is `jacWrap = [0↦7,1↦3,20↦8]` the correct
`Chart.jac`; (c) is `excepWrap` the right exceptional locus for `hg_inj`; (d) does `abs_jacDet_gWrap`
match the sympy monomial `u₀⁷·u₁³·u₂₀⁸`?

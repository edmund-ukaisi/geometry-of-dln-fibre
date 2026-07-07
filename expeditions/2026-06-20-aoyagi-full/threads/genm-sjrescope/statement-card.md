# Statement card — `(S,J)`-peel contract RE-SCOPE (`genm-sjrescope` tide)

**Status:** re-scoped contract landed sorry-free where it is plumbing; the two LOAD-BEARING analytic
pieces remain named sorries with faithful statements. Green in the full import closure of
`RouteMSJResolution` (`scripts/lb`, 8302 jobs). Branch `origin/genm-sjrescope`, base
`origin/genm-sjpeel-p3b @10ed54f0`, commit `d8cce785`. `RouteMSJChartAlgebra` now WIRED into
`DLNFibre.lean` (aggregator) and imported by the peel file.

## What this tide did (the triple-confirmed fix)

The prior `(S,J)`-peel contract was FLAWED on three counts (reviewer + 2 decorrelated Codex passes). This
tide re-scoped it; a decorrelated Codex xhigh consult (`codex/gammapeel-def-{prompt,answer}.md`) adjudicated
the faithful-definition fork toward **Candidate B** (the raw per-chart contribution) over the
literal-instruction Candidate A (baked-in shear/block-coordinate integral) — B is faithful, definable, and
makes `sjBoundaryPeel` a closable pure-cover inequality; the cross-coupled shear form it required is the
already-banked `frobSq_schur_block_split`, so no new definitional machinery. This is a **ladder re-scope**
(adapt the ladder, not the destination): the controller's literal point-3 ("bake the shear-image domain into
the def") was replaced by the faithful raw def + the banked identity as the bridge `sjJointResolution`
consumes. Flagged for the controller.

### Fix 1 — well-founded sum range (`t = 1..min`, was `range(min+1)`)
The `t = 0` term (a `0×0` pivot) degenerated to the WHOLE box integral, making the peel vacuous AND
`sjJointResolution M _ 0` **circular** (its `t=0` instance IS the induction goal). Now the sum is over
`Finset.Icc 1 (min (M 0) (M 1))`; `{A₀ = 0}` (rank 0) is null, so `{rank ≥ 1}` = box a.e.

### Fix 2 — per-`(t,ρ,κ)` signature (was `t`-only)
`gammaPeelIntegral M t ρ κ c'` now carries the pivot chart `ρ : Fin t ↪ Fin (M 0)`, `κ : Fin t ↪ Fin (M 1)`;
the finite chart count is the explicit `∑_ρ ∑_κ`, not absorbed into a constant.

### Fix 3 — faithful integrand (was dropped cross-term + clean box)

> **Def.** `gammaPeelIntegral M t ρ κ c' := ∫_{A'∈paramsBoxM(tailChain M)1} ∫_{A₀ ∈ matBox(M₀)(M₁)1 ∩ pivotChart ρ κ} ofReal(frobSq(rmatMul A₀ (prod(tailChain M) A'))^{−c'})`
>
> - **Lean:** `DLNFibre.DLN.RLCT.gammaPeelIntegral`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean` @ `d8cce785`)
> - **Gloss.** The tail-outer front-factor fibre integral of the front-split integrand, with the inner
>   front factor `A₀` restricted to the pivot chart `matBox ∩ pivotChart ρ κ` (box matrices whose `t×t`
>   `(ρ,κ)`-minor is a unit). The EXACT `(t,ρ,κ)`-chart contribution to the box integral — no dropped
>   cross-term, no clean-box distortion.
> - **Faithful.** By the banked EXACT identity `frobSq_schur_block_split` (`RouteMSJChartAlgebra`), on the
>   chart (pivot block invertible) the integrand equals the cross-coupled Schur form
>   `(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'}`; the shear `D ↦ Γ` (`measurePreserving_shearSub`) exposes `Γ`
>   over its shear-image domain. That reformulation is `sjJointResolution`'s content, not the def's.

## The contracts (faithful statements; named sorries)

> **`sjBoundaryPeel`** (piece 3, named sorry). `routeMLayerBoxIntegral M c' 1 ≤ ∑_{t∈Icc 1 min} ∑_ρ ∑_κ gammaPeelIntegral M t ρ κ c'` for `c' < ½·minAdm M`.
>
> - **Gloss.** The box integral is bounded by the finite sum, over pivot cuts `t = 1..min(M₀,M₁)` and
>   pivot charts `(ρ,κ)`, of the per-chart peeled integrals (constant `1` — a pure cover inequality).
> - **Proved (banked this tide, clean-three).** `pivotChartCover_matBox_le_sum` — the `matBox`-restricted
>   cover `∫_{matBox ∩ {t≤rank}} f ≤ ∑_{ρ,κ} ∫_{matBox ∩ pivotChart ρ κ} f` (the cover HEART, the `t=1`
>   step). `minAdm_cons_zero` — `minAdm (Fin.cons 0 rest) = 0` (the `min(M₀,M₁)=0` edge: `minAdm M = 0`,
>   threshold vacuous). Both `#print axioms` clean-three.
> - **Deferred (this sorry).** The measure-plumbing assembly around those two lemmas (the multi-hundred-line
>   wall). Precise 5-step product route recorded in the theorem docstring: (1) `front_split` +
>   `setLIntegral_prod_symm` → `∫_{matBox ×ˢ box}`; (2) null rank-0 point (needs `A.rank = 0 → A = 0` — not
>   in v4.29, provable via `rank_eq_finrank_span_cols` + `finrank=0→⊥`; and `NoAtoms` on the matrix
>   `volume`); (3) `iUnion_prod_const` + `lintegral_iUnion_le`; (4) `setLIntegral_prod_symm` back; (5)
>   `Finset.single_le_sum`.

> **`sjJointResolution`** (pieces 4/5/7, named sorry). GIVEN box-finiteness for every one-shorter chain
> (strong IH), `1 ≤ t ≤ min(M₀,M₁)`: `gammaPeelIntegral M t ρ κ c' < ⊤`.
>
> - **Gloss.** Each per-`(t,ρ,κ)`-chart peeled integral is finite. `t ≥ 1` ⟹ the pivot has positive rank,
>   so the chart integral reduces to STRICTLY-shorter chains (`redChain t M`, `tailChain M`) via the IH —
>   non-circular (unlike the excluded `t = 0`).
> - **Deferred.** The analytic core: `frobSq_schur_block_split` (banked) + shear → Gram change of variables
>   + the isotropic corank atom `matBox_corank_residual_le` (banked on `origin/genm-sjpeel-blow`, NOT this
>   branch) + the `(S,J)` monomialisation. The standing L≥3 wall.

## Recursion spine (sorry-free, re-threaded)

- `sjResolutionStep_proof : SJStepHyp` — composes `sjBoundaryPeel` + `sjJointResolution` via nested finite
  `ENNReal.sum_lt_top` over `t / ρ / κ`. Carries `sorryAx` via only the two named pieces.
- `routeMBoxThresholdFinite_of_step` (the WRAPPER) — `#print axioms` **clean-three** `[propext,
  Classical.choice, Quot.sound]` (no `sorryAx`; consumes the two contracts as hypotheses).
- `routeMBoxThresholdFinite_sjResolution M : RouteMBoxThresholdFinite M` (∀L) — carries exactly the two
  named analytic sorries.

## Cited / external
- `matBox_corank_residual_le` — banked on `origin/genm-sjpeel-blow`, consumed by the future
  `sjJointResolution` proof; NOT on this branch (named in the docstring only).

## Sorry inventory
`scripts/sorries` / `grep`: **exactly 2** `sorry` in `RouteMSJResolution.lean` — `sjBoundaryPeel` (L~597),
`sjJointResolution` (L~625). No other sorries introduced; the two banked helpers + the spine are sorry-free.

**Status.** sorry-free (spine + banked helpers) / two faithful named sorries (analytic pieces) — awaiting
fidelity review.

# genm-sjassembly — statement card (R1-UPPER: carrier measurability field + radial-attach factoring)

**Thread `genm-sjassembly`** (branch `genm-sjassembly` off `expedition/aoyagi-full @c942c132`, isolated
worktree). Mission: build `decorated_peel_step` → recursion → `RouteMBoxThresholdFinite M` → close
`sjJointResolution` (`RouteMSJResolution.lean:803`). This tide delivered the **item-1 foundation** (the
carrier `ctx`-measurability field + the measurability primitives + the radial-attach integral factoring
it unblocks). The **anisotropic-corank descent (item 2) + recursion (item 3) + close-out (item 4) remain
UNBUILT** — genuinely multi-tide, `sjJointResolution:803` UNTOUCHED.

All results axiom-clean (forced `#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorryAx`,
no `monomial_rlct`, no `cited_aoyagi_dln`). Files build force-recompiled green; full `scripts/lb DLNFibre`
green (8769 jobs) after the structure change.

## Delivered

### 1. `SJDecoration.residualMeas` field (shared-canonical structure change)

> **Claim.** The `SJDecoration` carrier records that each generator's linear residual
> `residual (ctx z).1 (ctx z).2 i` is measurable in the deeper parameter `z`.
>
> - **Lean:** field `SJDecoration.residualMeas` (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDecorated.lean`
>   @ `1bd4d74b`), threaded through all three constructors (`trivial`, `radialAttach`, `rowMix`).
> - **Gloss.** An additive structure field `∀ i, Measurable (fun z => carrier.residual (ctx z).1 (ctx z).2 i)`.
>   `trivial`: residual = product-entry (continuous, via `continuous_prod` + local `OpensMeasurableSpace (Params M)`);
>   `radialAttach`: `= D.residualMeas` (radialStep preserves `coeff`); `rowMix`: finite linear combo
>   (`residual_rowMix`).
> - **Proved.** The field + all three constructors supply it; full aggregator green (ripple = `RowMix` + `AxCheck`).
> - **Cited / Deferred.** none.

### 2. Measurability primitives (`RouteMSJDecoratedMeas.lean`, NEW)

> - `continuous_genMonomial`, `continuous_jacMonomial` — the exceptional/Jacobian monomials are continuous.
> - `SJDecoration.decLoss_nonneg` — `0 ≤ decLoss u z` (sum of squares).
> - `SJDecoration.continuous_decLoss_right` — `u ↦ decLoss u z` is continuous (polynomial in `u`, `z` fixed).
> - `SJDecoration.measurable_decLoss` — `z ↦ decLoss u z` measurable (per-`u`, from `residualMeas`).
> - `SJDecoration.measurable_decLoss_uncurry` — `(z,u) ↦ decLoss u z` JOINTLY measurable (Tonelli-ready;
>   monomial rides `measurable_snd`, residual rides `measurable_fst` — `Z` has no topology so the join
>   is by projection, not product-continuity).
> - `SJDecoration.measurable_integrand` — the full decorated integrand jointly measurable.
> - `lintegral_unitBox_succ_cons` — split coordinate `0` off `∫⁻_{unitBox (d+1)}` via the MP `piFinSuccAbove 0`
>   equiv + Tonelli. Reusable.
> - **Proved / Cited / Deferred.** all sorry-free, clean-three; no external cite; nothing deferred.

### 3. Radial-attach integral factoring (`RouteMSJDecoratedRadial.lean`, NEW)

> **Claim.** Attaching a fresh fully-shared Case-2 divisor factors the decorated box-integral into a 1-D
> radial Jacobian factor times the parent — the integral-level realization of `carrierThreshold_shift`.
>
> - **Lean:** `SJDecoration.radialAttach_integral`, `radialAttachFactor`, `radialAttachFactor_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDecoratedRadial.lean` @ `1bd4d74b`).
> - **Gloss.** `(radialAttach D j₀).integral c' = radialAttachFactor j₀ c' · D.integral c'` (UNCONDITIONAL
>   in `c'`, holds even where both sides are `⊤`), where `radialAttachFactor j₀ c' = ∫⁻_{[0,1]} |u₀|^{j₀}·(u₀²)^{−c'}`;
>   plus `radialAttachFactor_lt_top`: that factor is finite when `−1 < j₀ − 2c'` (i.e. `c' < (j₀+1)/2`, the
>   per-divisor Morse threshold).
> - **Proved.** the equality (via `lintegral_unitBox_succ_cons` + pointwise `Real.mul_rpow` factoring +
>   three const-mul factorings) and the finiteness (via banked 1-D `abs_rpow_lintegral_Ioo_lt_top`).
> - **Cited.** `abs_rpow_lintegral_Ioo_lt_top` (banked, `RouteMSJMonomialLower`). **Deferred.** none within scope.
> - **Status.** sorry-free (awaiting reviewer fidelity check).

**Name-clash caught:** `radialFactor` collides with `RouteMRadialFactor`'s `ChartFactor` of the same name in
the same namespace (the module-scope build missed it); renamed to `radialAttachFactor`.

## What remains — the crux (item 2) + recursion (item 3) + close-out (item 4), UNBUILT

- **Item 2 — the anisotropic-corank descent (`decorated_peel_step` core).** Compose `lintegral_eq_polar`
  (banked spherical blow-up, `r^{pq−1}` Jacobian) + `frobSq_schur_block_split` (banked Schur weld) +
  `measurePreserving_shearSub` (banked shear) + per-`ω`/per-`A'` radial analysis to descend the anisotropic
  block integral `∫_{Γ box}(frobSq(A·Q̃)+frobSq(C·Q̃+Γ·Qb))^{−c'}` to the isotropic residual
  `matBox_corank_residual_absZ_le` at the shifted exponent `c'−pq/2`, with the IRREDUCIBLE pivot/corank
  interleaving (rank-deficient `Qb`). This is the "~65–75% genuinely-new" multi-tide construction; NOT
  attempted here (would require laundering). The radial-attach factoring delivered here is the carrier-level
  SINGLE-divisor version — the spherical blow-up (`r` over the sphere) is a different coordinate structure.
- **Item 3 — the well-founded recursion** on arity → `DecoratedBoxThresholdFinite (trivial M)` →
  (`decoratedBoxThresholdFinite_trivial_iff`) `RouteMBoxThresholdFinite M`. The driver
  `routeMBoxThresholdFinite_of_step`/`SJStepHyp` exists sorry-free; needs item 2 to supply `SJStepHyp`
  WITHOUT `sjJointResolution` (else circular).
- **Item 4 — close-out.** With item 3's independent `RouteMBoxThresholdFinite M`, close `sjJointResolution:803`
  via banked `sjJointResolution_of_boxThresholdFinite`. LEFT UNTOUCHED (closing it now would be circular).

## Controller actions

- Wire `RouteMSJDecoratedMeas` and `RouteMSJDecoratedRadial` into `DLNFibre.lean` (single-writer aggregator).
- Optionally add the load-bearing results (`SJDecoration.radialAttach_integral`, `radialAttachFactor_lt_top`,
  `measurable_integrand`) to `AxCheck.lean`.
- No `git commit`/PR by this tide beyond the feature-branch pushes to `origin/genm-sjassembly`.

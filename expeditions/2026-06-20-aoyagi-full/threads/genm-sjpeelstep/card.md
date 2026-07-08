# genm-sjpeelstep — statement card (R1-UPPER: the `∫⁻` spherical blow-up CoV, item-1)

**Thread `genm-sjpeelstep`** (branch `genm-sjpeelstep` off `expedition/aoyagi-full @360722fb`, isolated
worktree). Mission: build `decorated_peel_step` → the recursion → `RouteMBoxThresholdFinite M` (∀L) →
close `sjJointResolution` (`RouteMSJResolution.lean:803`), via the PURE R-BLOWUP route.

## What landed (banked, pushed to `origin/genm-sjpeelstep`)

**File:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSphereBlowup.lean` (network-free; imports only
Mathlib `HaarToSphere` + `Measure.Haar.InnerProductSpace`). Two theorems, both axiom-clean
(`[propext, Classical.choice, Quot.sound]`, FORCED `#print axioms`; no `monomial_rlct`, no
`cited_aoyagi_dln`), no `sorry`, no warnings.

This is the mission's **item 1** — "the sole new analytic sub-brick": the lower-Lebesgue (`∫⁻`) form of
the polar / spherical change of variables (the coordinate blow-up `Γ = r • ω`, Jacobian `r^{N−1}`), the
`∫⁻` companion of Mathlib's `integral_fun_norm_addHaar` (which is `∫`, Bochner, and radially-symmetric
only — the pure route needs the general anisotropic integrand, so it rides
`measurePreserving_homeomorphUnitSphereProd` directly).

- **`lintegral_eq_sphereProd`** — raw measure-preserving form. For `[NeZero N]` and any nonneg `h` on
  `EuclideanSpace ℝ (Fin N)` (no measurability needed):

      ∫⁻ x, h x  =  ∫⁻ p, h ((homeomorphUnitSphereProd _).symm p)
                      ∂(volume.toSphere.prod (volumeIoiPow (finrank ℝ E − 1))).

  Proof: `restrict_compl_singleton` (origin null under Haar) + `lintegral_subtype_comap` +
  `MeasurePreserving.lintegral_comp_emb` on `measurePreserving_homeomorphUnitSphereProd`, with
  `Homeomorph.symm_apply_apply` collapsing `symm ∘ homeo = id`.

- **`lintegral_eq_polar`** — iterated (Tonelli + `withDensity`-unfolded) form, Jacobian exposed. For
  `[NeZero N]` and **measurable** nonneg `h`:

      ∫⁻ x, h x  =  ∫⁻ ω ∂volume.toSphere, ∫⁻ r in Ioi 0,
                      ofReal (r^{N−1}) · h (r • ↑ω) ∂volume.

  Proof: `lintegral_eq_sphereProd` + `lintegral_prod` (Tonelli) + the `withDensity` unfold of
  `volumeIoiPow (N−1)` (`lintegral_withDensity_eq_lintegral_mul`) + `lintegral_subtype_comap` on the
  `Ioi 0` subtype; `homeomorphUnitSphereProd_symm_apply_coe` rewrites `symm (ω,r) = r • ω`.

  This is the exponent-shift shape the pure peel consumes: after the block loss factors as
  `u²·(residual)` on the sphere (`frobSq(r•ω) = r²`), the `r`-integral `∫ r^{N−1}·(r²·residual)^{−c'}`
  descends the exponent by `N/2`.

**Why this is genuinely new (not duplicating a banked route).** The banked isotropic exponent-shift
(`RouteMSJCorankResidual.matBox_corank_residual_le`, `RouteMSJCorankPure.matBox_corank_*_absZ_*`) and
`RadialResidualPower.Cresid` use a **full-space scaling** trick (`Γ ↦ w^{1/2}·Γ`), which for the
ANISOTROPIC block `frobSq(C·Q̃ + Γ·Q_b)` is the DEAD atom route (integrating `Γ` to full space
manufactures `det(Q_b Q_bᵀ)`, divergent on rank-deficient `Q_b`). The spherical blow-up KEEPS `Γ` on
the box and resolves its origin radially — the pure route. So this brick is the primitive the pure
route needs and the scaling route cannot supply.

## What remains — `decorated_peel_step` (items 2–4): the multi-tide bulk (NO new obstruction found)

Confirmed by an independent trace through the actual Lean interfaces, matching sjpure/r1flip/sjcarrier4's
decorrelated-Codex verdict: `decorated_peel_step` + the recursion + close-out is a LARGE, BOUNDED,
MULTI-TIDE build. STEP-0 stays PASS; the CoV primitive (this brick) exists and lands; **no new
obstruction beyond sjpure's pinned plan.** The remaining crux is the anisotropy-removal ASSEMBLY, not a
missing theorem.

Precise remaining items, in dependency order:

1. **`decLoss` / `SJLinGenState.loss` measurability** (currently unbanked) — needed for any
   integral-level factoring of `SJDecoration.integral` (Tonelli / `lintegral_const_mul`). Gates the
   decoration-level radial-attach integral identity `(radialAttach D j₀).integral c' = K · D.integral
   c'` (`K = ∫_{[0,1]} u₀^{j₀−2c'}`, the integral-level realization of `carrierThreshold_shift`).
2. **The anisotropic-corank ASSEMBLY** (the genuine crux, multi-tide): compose `lintegral_eq_polar`
   (this brick) with the banked Schur split (`frobSq_schur_block_split`), the shear MP
   (`measurePreserving_shearSub`), and the per-`ω`/per-`A'` radial analysis to descend the anisotropic
   block integral `∫_{Γ box} (frobSq(A·Q̃) + frobSq(C·Q̃ + Γ·Q_b))^{−c'}` to the isotropic residual
   (`matBox_corank_residual_absZ_le`) at the shifted exponent `c' − pq/2`. **CRITICAL:** the crude
   pivot-core domination `frobSq(A₀·Q)^{−c'} ≤ frobSq(A·Q̃)^{−c'}` is INSUFFICIENT — it caps finiteness
   at `c' < t/2 ≪ ½·minAdm M` (verified: e.g. `(3,3,4)` gives `t ≤ 3`, so `c' < 3/2`, but the threshold
   is `4`). The `pq`-exponent from the `Γ` blow-up is genuinely required. The rank-deficient-`Q_b` locus
   forces the pivot/corank INTERLEAVING (sjpure), so this is not a single lemma.
3. **The well-founded recursion** on arity → `DecoratedBoxThresholdFinite (trivial M)` →
   (`decoratedBoxThresholdFinite_trivial_iff`) `RouteMBoxThresholdFinite M`. The recursion DRIVER
   already exists sorry-free (`routeMBoxThresholdFinite_of_step` + `SJStepHyp`); the decorated route
   supplies `SJStepHyp` WITHOUT `sjJointResolution` (i.e. proves the step via the CoV, not circularly).
4. **Close-out:** with the independent `RouteMBoxThresholdFinite M` in hand, close `sjJointResolution`
   (`:803`, the SOLE remaining sorry in `RouteMSJResolution.lean`; `sjBoundaryPeel` is already CLOSED)
   via the banked `sjJointResolution_of_boxThresholdFinite`. Leave `:803` UNTOUCHED until item 3 lands
   (else circular).

## Build / ledger

- Files: `RouteMSJSphereBlowup.lean` (NEW, 2 theorems). Controller must wire it into the aggregator
  `DLNFibre.lean` (single-writer) + add both theorems to `AxCheck.lean` if load-bearing.
- Build: `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJSphereBlowup` — FORCED (`touch` + rebuild)
  green (2670 jobs), no warnings. FORCED `#print axioms` both theorems: clean-three.
- `scripts/sorries`: the new module has zero. `sjJointResolution:803` remains the pre-existing sole
  R1-UPPER sorry (UNTOUCHED, per mission).
- LoC: +~110 (module incl. docstring).
- No existing file edited; no aggregator edit; no name clash (`lintegral_eq_sphereProd` /
  `lintegral_eq_polar` unique in `DLNFibre/`).

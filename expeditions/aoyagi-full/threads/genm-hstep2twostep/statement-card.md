# Statement card — general-`L` Step Θ (naive↔conj MP bridge), the LINK-2 half of `hstep2`

Thread `genm-hstep2twostep`. Re-architecting the #120 `hstep2` close to the accepted L=2 two-step
`hstep2 = Step Θ ∘ Step Ψ_conj` (`deepest_diffeo_bridge_L2_assembled`). This card covers **Step Θ**
(LINK-2, the naive↔conjugate core-absorb RLCT bridge), lifted to general `L`. Step Ψ_conj (LINK-1)
and the `hstep2` sorry itself are **not** in this bank.

Lean module: `lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeGenTheta.lean` @ `812fa70f`
(branch `origin/genm-hstep2twostep`, off `origin/genm-hstep2chain` @ `d6cab750`).

## Why the two-step (the finding this re-architecture answers)

The single-Ψ-step reduction `deepest_diffeo_bridge_gen_impl` reduces `hstep2` to a germ `huntwist`
on the **naive** `deepestCoreAbsorb` (cores `S^naive`, pivot `1+X`). That germ is UNSATISFIABLE:
`Score` needs the **honest conjugate** cores `S^conj` (pivot `deepBlkA_s + gaugeReadX_s`), and one
left-shear `Ψ: S↦(1−K)S` with `K(0)=0` (a `1+o(1)` map) cannot change the leading germ. The fix
mirrors the accepted L=2 proof: bridge naive↔conjugate by an MP core-shear (**Step Θ**, chain-free),
and put the shear on the conjugate cores (**Step Ψ_conj**, where the honest chain `Ĉ` lives).

## The five theorems (all sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]`)

> **Claim (Step Θ, chart frame).** For `2 ≤ L`, the naive and conjugate absorbed-core energies have
> the same local RLCT at `wstar`: with `regStraighten.1 = deepestEFull` and (as a hypothesis) the
> conjugate reg-absorb `hRegAbsorbConj`,
> `rlctAtOn (∑ (regStraighten (split x))² + coreF(deepestCoreAbsorbConj (split x))) wstar
>  = rlctAtOn (∑ (regStraighten (split x))² + coreF(deepestCoreAbsorb (split x))) wstar`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.link2_at_wstar_gaugeReg_gen`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeGenTheta.lean` @ `812fa70f`)
>   — with `link2_at_zero_gaugeReg_gen` (gauge-`0` form), `regAbsorb_bare_gen`,
>   `regAbsorbPeel_bare_gen`, `deepestEFull_bare_hTilde_exists_gen`.
> - **Gloss.** `link2_at_zero_gaugeReg_gen`: at gauge `0` over `DeepestSplit`, the reg output is
>   straightened to the gauge reg `∑ q.1²` on both sides — bare via the built `regAbsorb_bare_gen`,
>   conj via the hypothesis `hRegAbsorbConj` — and at gauge reg the banked general
>   `rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` (the det-1, basepoint-and-reg-fixing MP core-shear
>   `Θ = coreShearHomeo(schurCutoffShiftConj − schurCutoffShift)`) peels naive↔conj with no
>   derivative bookkeeping. `link2_at_wstar_gaugeReg_gen` transports that gauge-`0` equality to the
>   chart basepoint `wstar` along the MP homeomorphism `split` (`rlctAtOn_comp_homeomorph`,
>   `split wstar = 0`).
> - **Proved.** All five theorems unconditionally at general `L` (`2 ≤ L`), sorry-free, clean-three:
>   - `deepestEFull_bare_hTilde_exists_gen` — the bare reg-absorb π̃ (`regStraightenOf2 (deepestEFull
>     ∘ deepestCoreAbsorb.symm)`) is a local diffeo at `0` (ContDiff + invertible strict-deriv). The
>     bare shift derivative vanishes (`hasStrictFDerivAt_schurCutoffShift_zero`), so
>     `D(coreAbsorb.symm)(0) = id` and `eTilde = e` from the general `deepestEFull_deriv`.
>   - `regAbsorbPeel_bare_gen` — `rlctAtOn_comp_localDiffeo` peels π̃: straightens
>     `deepestEFull ∘ coreAbsorb.symm` to `∑ q.1²`.
>   - `regAbsorb_bare_gen` — `rlctAtOn_regAbsorb_reduce2` + the peel: straighten `deepestEFull` reg
>     to gauge reg `∑ q.1²`, bare core absorb fixed.
>   - `link2_at_zero_gaugeReg_gen`, `link2_at_wstar_gaugeReg_gen` — the composition above.
> - **Assumed (carried as `hRegAbsorbConj`).** The **conjugate** reg-absorb at gauge `0`:
>   `rlctAtOn (∑ deepestEFull q² + coreF(conjAbsorb q)) 0 = rlctAtOn (∑ q.1² + coreF(conjAbsorb q)) 0`.
>   The L=2 discharge is `regAbsorb_conj` (`DeepestL2ConjSub4`), which rides the `Fin 3` value-fold
>   atom `deepestEFull_coreConstant`. It enters as a hypothesis here (see Deferred).
>   Also carried: `hDA` (each `deepBlkA_s` a unit), `hbdy` (each layer has a vanishing boundary
>   off-diagonal block), the pivot/frame data `J, Pf, Qf` + block facts, and `hregval`
>   (`regStraighten.1 = deepestEFull`) — all supplied by the wire (`deepest_gauge_construction`).
> - **Cited.** none new. Reuses the banked general-`L` `rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb`
>   (Step-Θ MP-shear peel, `DeepestSchurShiftConj`) and the network-free `rlctAtOn_comp_homeomorph`
>   / `rlctAtOn_comp_localDiffeo` / `rlctAtOn_regAbsorb_reduce2`.
> - **Deferred (the remaining Step-Θ geometry).** The **general** conjugate reg-absorb
>   (`hRegAbsorbConj`'s discharge). The obstruction is the general lift of `deepestEFull_coreConstant`
>   (`∂deepestEFull/∂core(0) = 0`): at the reg-zero slice the framed product is the core-independent
>   corner `fromBlocks 1 0 0 junk`, so `deepestEFull` is core-constant there — currently proved only
>   at `Fin 3` (via the two-layer unfold `prodDecode_eq_two_of_L2`). Verdict: **labor, not a wall**
>   (the deepest-point corner structure is general). Discharging it gives the general conj π̃
>   (`deepestEFull_conj_hTilde`) → `regAbsorbPeel_conj_gen` → `regAbsorb_conj_gen`.
> - **Route.** Mirror of the L=2 `link2_at_zero_gaugeReg` / `link2_at_wstar_gaugeReg` /
>   `deepest_diffeo_bridge_L2_assembled` chain; every ingredient is either already general
>   (`deepestEFull_deriv`, `deepestEFull_contdiff`, `deepestEFull_base`, `deepest_regAbsorb_exists`,
>   the `rlctAtOn_*` combinators, `rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb`) or built here.
> - **Status.** sorry-free (pending fidelity review).

## Remaining to close `hstep2` at general `L` (precise)

1. **Step Θ, conj reg-absorb** — discharge `hRegAbsorbConj`: general `deepestEFull_coreConstant` →
   general conj π̃ local-diffeo (`deepestEFull_conj_hTilde`) → `regAbsorbPeel_conj_gen` →
   `regAbsorb_conj_gen`. (Labor: the general corner factorization + the `Fin 3` `DeepestL2ConjSmooth`
   / `DeepestL2ConjSub4` conj-side machinery lifted.) Then `link2_at_wstar_gaugeReg_gen` is fully
   unconditional (drops `hRegAbsorbConj`).
2. **Step Ψ_conj (LINK-1)** — the general conjugate diffeo bridge: the honest chain `Ĉ` +
   `psiSplitRawL2CoreConj` general analog + the germs `hsub3reg`/`hsub4core` (reg-preservation +
   core=`Score`), via `deepestCoreF_coreAbsorbConj_eq_prodSchur` (banked general) +
   `schur_product_ldu_rec` + the `Fin (H k)` reindex casts. This is the coupled geometric bulk.
3. **Compose** Θ (this bank) ∘ Ψ_conj → the general `deepest_diffeo_bridge_gen_assembled` →
   `rw` into `DeepestL2Wiring.deepest_gauge_construction`'s `hstep2` sorry (line 1060), producing the
   naive-`deepestCoreAbsorb` canonical target the wire consumes.

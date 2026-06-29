# Statement card — LINK-2 (the L=2 bare↔conjugated absorbed-core RLCT bridge)

> **Claim.** At the deepest basepoint of a front-pivoted rank-`r` `B` for an `L = 2` DLN, the
> **conjugated** absorbed-core RLCT equals the **bare** one, with the same straightened reg term:
> with `(regStraighten q).1 = deepestEFull q` (`hregval`),
> `rlctAtOn (q ↦ ∑(regStraighten q).1² + coreF(conjAbsorb q).core) 0
>  = rlctAtOn (q ↦ ∑(regStraighten q).1² + coreF(bareAbsorb q).core) 0`,
> under the producer hypotheses (front-pivot `hJfront`, boundary `hbdy`, conj-pivot units `hDA`,
> endpoint frame units/identities `hPf/hQf/hQf0/hPfL/hQf22`, endpoint triangularity `hPtri/hQtri`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.link2_at_zero_gaugeReg`
>   (`lean/DLNFibre/DLN/RLCT/Validate/ScratchL2Link2.lean` @ `cafc288c`)
>   — supporting stack `DLNFibre.DLN.RLCT.{contDiff_schurCutoffShiftConj,
>   deepestEFull_coreInBlock_zero, deepestEFull_conj_hTilde_exists, deepestEFull_bare_hTilde_exists}`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestL2ConjSmooth.lean` @ `cafc288c`).
> - **Gloss.** The bare and conjugated core absorptions (`deepestCoreAbsorb` / `deepestCoreAbsorbConj`,
>   both det-1 core-shears) give the same local RLCT at `0`. Proof: straighten the `deepestEFull` reg
>   output down to the gauge reg `∑q.1²` (the two reg-absorb peels), where the BANKED Θ-peel
>   `rlctAtOn_coreF_bareAbsorb_eq_conjAbsorb` converts bare↔conj with no drag (the MP shear `Θ` fixes
>   the reg slot), then lift back. Each reg-absorb peel is a `rlctAtOn_comp_localDiffeo` on the
>   π̃ = `regStraightenOf2 (deepestEFull ∘ coreAbsorb.symm)`, whose invertible strict derivative at `0`
>   reuses the PIN-1 reg frame `F`.
> - **Proved.** `link2_at_zero_gaugeReg` and the two peels `regAbsorbPeel_conj`/`regAbsorbPeel_bare`,
>   sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`. The conjugated cutoff Schur
>   shift is globally `ContDiff ⊤` (`contDiff_schurCutoffShiftConj`). The conj π̃ is a local diffeo at
>   `0` despite the conj shift's **nonzero** derivative `Dδ`: `Dδ` moves only the core slot, which
>   `D(deepestEFull)(0)` annihilates (`deepestEFull_coreInBlock_zero`, from the value-fold atom
>   `deepestEFull_coreConstant`), so the reg-block is the same invertible `F` and `eTilde = e`.
> - **Assumed.** The producer hypotheses listed in the claim — the genuine deepest-point frame data
>   `deepest_gauge_construction` holds in scope (matches the bare `hTilde` site in `DeepestL2Wiring`).
>   Scope `L = 2` (`H : Fin 3 → ℕ`), the value-fold atom's domain.
> - **Cited.** none (all Mathlib-internal: `rlctAtOn_comp_localDiffeo`, `rlctAtOn_comp_homeomorph`,
>   `HasStrictFDerivAt` chain/prod rules).
> - **Deferred.** Wiring `link2_at_zero_gaugeReg` into `deepest_gauge_construction` to retire the inline
>   bare `hTilde` and complete the conj-side `hstep2` chain (single-writer `DeepestL2Wiring`, controller's
>   integration step). The `L ≥ 3` analogue (the value-fold atom is `L = 2`-specific).
> - **Route.** Drop the reg level to the gauge reg `∑q.1²` (where Θ fixes `q.1`, no comparability
>   obstruction) via two local-diffeo reg-absorb peels; convert bare↔conj by the banked gauge-reg Θ-peel;
>   the conj peel's π̃-invertibility rides the value-fold atom (`D_E` annihilates the core) rather than a
>   `D(shift)(0)=0` fact (which is FALSE for the conj shift). Supersedes the REFUTED comparability route
>   (`rho_residual_epsBound`, removed — `F` and `Φ` had different zero sets, exact-rational witness a44dd7e4).
> - **Status.** sorry-free + reviewed (fidelity PASS, decorrelated-Codex-confirmed atoms, 2026-06-29).

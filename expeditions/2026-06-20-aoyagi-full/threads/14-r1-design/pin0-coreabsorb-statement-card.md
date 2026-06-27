# Statement card — PIN 0: the deepest-point core absorption (#44c, #79)

> **Claim.** At the rank-`r`-exact deepest point of the DLN fibre, the gauge-absorption
> `coreAbsorb` turning the raw reduced-core slot `T_s` into the per-layer **Schur complement**
> `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` exists as a self-homeomorphism of the split coordinate space
> `DeepestSplit`, fixing the regular and spectator slots and the origin, and preserving the local
> RLCT of the comparison function `Φ` (the `coreAbsorb_rlct` peel).
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_coreAbsorb_exists`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean` @ `f0166cc`), built from the
>   concrete `DLNFibre.DLN.RLCT.deepestCoreAbsorb := coreShearHomeo (schurCutoffShift …)` and the
>   shift bedrock in `lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean` (@ `ccccdc8`).
>
> - **Gloss.** `coreAbsorb` is the cross-slot additive shear `(reg, core, spec) ↦ (reg, core +
>   schurCutoffShift(reg, spec), spec)` (`coreShearHomeo`). The shift `schurCutoffShift = χ ·
>   schurShiftRaw` is a gauge-slot `ContDiffBump` `χ` (= 1 near `0`) times the honest per-layer Schur
>   correction `s ↦ −Z_s·(1+X_s)⁻¹·Y_s` flattened into the core slot. `deepest_coreAbsorb_exists`
>   asserts the four `DeepestGaugeChart` obligations: `coreAbsorb 0 = 0`, `(coreAbsorb q).1 = q.1`
>   (regular fixed), `(coreAbsorb q).2.2 = q.2.2` (spectator fixed), and the RLCT equality
>   `rlctAtOn (∑ q.1² + deepestCoreF (coreAbsorb q)) 0 = rlctAtOn (∑ q.1² + deepestCoreF q.2.1) 0`.
>
> - **Proved (unconditionally).**
>   - `schurCutoffShift` is **globally continuous** (`continuous_schurCutoffShift`, via
>     `continuous_of_tsupport`: `tsupport χ = closedBall 0 (ε/2) ⊆ ball 0 ε ⊆ unitSet`, the open
>     det-nonzero set on which the raw Schur correction is `ContinuousAt` — honest resolution of the
>     `(I+X_s)⁻¹` pole, no masking; the `Continuous shift` requirement of `coreShearHomeo` is the
>     safeguard that a poles-shift is unprovable).
>   - `schurCutoffShift 0 = 0` (`schurCutoffShift_zero`; `Z_s(0)=0`).
>   - The four obligations, via the shift-agnostic **measure-preserving** peel
>     `coreShear_satisfies_coreAbsorb` (the shear is `det = 1`, so `rlctAtOn_comp_homeomorph` applies
>     — NO derivative bookkeeping).
>   - Clean-three axioms `{propext, Classical.choice, Quot.sound}`; zero `sorry`/`axiom`.
>
> - **Assumed.** `IsDeepLayers` regime: `B.rank = r`, `∀ s, r ≤ H s`, `1 ≤ L`. (No `L=3`
>   specialisation — general `L`.)
>
> - **Cited.** none (the MP helpers `measurePreserving_coreShear` etc. are proved in-repo, crux2 #83).
>
> - **Deferred (named, NOT done here).**
>   - The **germ-at-0 agreement** `schurCutoffShift = schurShiftRaw` on the inner ball is proved
>     (`schurCutoffShift_eq_raw_of_mem_closedBall`) but its *consumption* — that
>     `deepestCoreF (coreAbsorb (split w)).2.1 = ‖∏ S_s‖²` two-sidedly matches the loss core near `0`
>     — is **PIN 2's** obligation (`deepest_loss_squeeze`), not established here.
>   - The honest reduced core is the **full-product** Schur complement `R(∏C)`, NOT `∏ S_s`
>     (g156: Schur of a product ≠ product of Schurs); the two agree modulo `ideal(E)` (charged to
>     `∑E²` by `core_comparability_squeeze`). `coreAbsorb` produces the `∏ S_s` reading, which is the
>     g156-blessed `deepestCoreF` object; the `R − ∏S_s ∈ ideal(E)` reconciliation lives in PIN 2.
>
> - **Status.** sorry-free; awaiting PIN-0-coupling fidelity review (crux2).

## Notes

- **Coupling (Codex-confirmed Option A).** `coreAbsorb` is wired *concretely* as
  `deepestCoreAbsorb = coreShearHomeo schurCutoffShift` in `deepest_gauge_construction`, not obtained
  existentially, so PIN 2 (`deepest_loss_squeeze`) receives the same definitional map and can unfold
  `(coreAbsorb (split w)).2.1` to the Schur-corrected core via the `coreShearHomeo_*` rfl-lemmas.
- **Route A.** The peel is the measure-preserving `rlctAtOn_comp_homeomorph` on the `det = 1` shear —
  NOT a chart / measure-Jacobian. `coreAbsorb_rlct` is shift-agnostic (any continuous shift vanishing
  at `0` satisfies it); the concrete Schur form matters only for PIN 2.

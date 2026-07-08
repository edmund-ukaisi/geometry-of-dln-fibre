# Statement card — `hcd` (Producer-1 diffeo-triple leaf 3/3)

> **Claim.** The deviation `q ↦ psiSplitRawGen q − q` of the general-`L` joint split-move is
> `C^∞` (`ContDiffAt ℝ ⊤`) on a neighbourhood of the split origin — the smoothness input the
> cutoff→flat-diffeo plumbing (`contDiff_deepestPsiFlatCut`) consumes to build the concrete `psi`
> of `deepest_diffeo_bridge_gen_assembled` (#120 `hstep2`).
>
> - **Lean:**
>   - `DLNFibre.DLN.RLCT.contDiffAt_psiSplitDeltaGen_at`
>   - `DLNFibre.DLN.RLCT.hcd_psiSplitRawGen`
>   - `DLNFibre.DLN.RLCT.eventually_psiInvBundle`, `DLNFibre.DLN.RLCT.psiInvBundle_zero`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiHcdGen.lean` @ `b4d7a2d1`)
> - **Gloss.**
>   - `psiInvBundle … q₀` := the chain-corner `(C q₀ k)₁₁`, partial-product corner
>     `(partProd (C q₀) k)₁₁`, and pivot-mix `nMix (C q₀) k` all have nonzero determinant, ∀ `k`
>     (`C q := deepestChain (framedParamsPivot … q)`).
>   - `contDiffAt_psiSplitDeltaGen_at`: for any `q₀` with `psiInvBundle … q₀`,
>     `ContDiffAt ℝ ⊤ (fun q => psiSplitRawGen … q − q) q₀`.
>   - `hcd_psiSplitRawGen`: for a cutoff bump `χ : ContDiffBump (0 : DeepestSplit …)` with
>     `hχ : ∀ q ∈ tsupport χ, psiInvBundle … q`, one has
>     `∀ q ∈ tsupport χ, ContDiffAt ℝ ⊤ (fun q => psiSplitRawGen … q − q) q` — the exact shape of the
>     `hcd` argument of `contDiff_deepestPsiCutRaw` / `contDiff_deepestPsiFlatCut`.
>   - `eventually_psiInvBundle`: `∀ᶠ q in 𝓝 0, psiInvBundle … q` (so a small-enough bump discharges `hχ`).
>   - `psiInvBundle_zero`: `psiInvBundle … 0` (all three families `= 1` at the origin).
> - **Proved.** All four, sorry-free, forced `#print axioms = [propext, Classical.choice, Quot.sound]`.
>   Route: 20 general-`q` twins of hderiv0's at-`0` entry-smoothness ladder carrying the
>   invertibility bundle; top-level `psiTargetD → forcedDecode{Left,Right} → psiGhat → psiReadBlk`
>   assembly (never built even at `0`); payload lens `psiSplitDeltaGen_eq_payload` + banked read-backs
>   (`regGaugeSlotEquiv_psiSplitRawGen`, `paramsEquivFlatCLE_psiSplitCoreDeltaGen_eq`) + the smooth
>   packing CLEs (`regGaugeSlotCLE`, `paramsEquivFlatCLE`); the region is a `𝓝 0` via det-continuity
>   (chain/partProd global `ContDiff`; `nMix` `ContDiffAt`-at-`0`) + `∀ k` = finite range + trivial
>   tail (`deepestChain_tail_toBlocks₁₁` / `partProd_toBlocks₁₁_stabilize` / `nMix_tail_eq_one`).
> - **Assumed.** `hcd_psiSplitRawGen` carries `hχ` (bump support ⊆ invertibility region). This is a
>   GENUINE hypothesis, not laundering: `psiSplitRawGen` inverts `q`-dependent matrices, so it is NOT
>   globally smooth and the consumer's unconditional `∀ q ∈ tsupport χ, ContDiffAt` is FALSE for an
>   arbitrary large `χ`. `eventually_psiInvBundle` shows `hχ` is dischargeable for a small bump.
>   Structural hyps `hr`, `hL`, `J`, `Pf`, `Qf` are `psiSplitRawGen`'s own definitional arguments.
> - **Cited.** none (pure Mathlib analysis + banked in-repo lemmas).
> - **Deferred.** none for the smoothness leaf itself. Wiring into `deepestPsiFlatCut`'s `hcontdiff`
>   and thence `deepest_diffeo_bridge_gen_assembled` is the Producer-1 top-level assembly (controller),
>   which also picks the concrete `χ` and discharges `hχ` via `eventually_psiInvBundle`.
> - **Status.** sorry-free (reviewer fidelity check pending).

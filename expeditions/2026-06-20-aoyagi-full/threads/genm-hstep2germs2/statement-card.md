# Statement card — `DeepestPsiSplitGenMoved` (the abstract moved-chain algebra, #120 `hstep2`)

Thread `genm-hstep2germs2` (branch `genm-hstep2germs2`, off consolidated `expedition/aoyagi-full` @dc263b8a).
The network-free algebraic core of the general-`L` joint move `psiSplitRawGen` (cert
`expeditions/2026-06-20-aoyagi-full/threads/genm-d1psidesign/cert.md`). Working over the abstract
`Type`-valued chain of `DeepestSchurRecursion` (width family `m : ℕ → Type*`, layer `s` of shape
`Matrix (r ⊕ m s) (r ⊕ m (s+1))`, cast-free `partProd`), this discharges Invariant B in full and the
top-row half of Invariant A.

## Invariant B (core untwist → Score)

> **Claim.** The moved chain's per-layer Schur complement is the target `S̃_s = (1 − K_s)·S_s`, and the
> plain product of the moved Schur cores equals the Schur complement of the original full product
> `blockSchur (partProd C L)` — the `Score = ‖blockSchur(P)‖²` the conj-absorb reads.
>
> - **Lean:** `DLNFibre.DLN.RLCT.blockSchur_movedC` (per layer) and
>   `DLNFibre.DLN.RLCT.prodSchurCore_eq_blockSchur_partProd` (global)
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiSplitGenMoved.lean` @ `<SHA>`)
> - **Gloss.** `blockSchur_movedC`: `blockSchur (movedC C Z0edit s) = schurTilde C s` where
>   `movedC` is the joint move (pivots `A_s` fixed, up-edit `Y'_s = Y_s + ΔY_s`, `Z₀` override, core
>   `T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s`) and `schurTilde C s = (1 − Kcoup C s)·blockSchur (C s)`.
>   `prodSchurCore_eq_blockSchur_partProd`: `∏_{s<L} blockSchur (movedC C Z0edit s) = blockSchur (partProd C L)`,
>   given `Invertible` on each layer pivot `(C k)₁₁` (`k<L`) and each partial pivot `(partProd C k)₁₁` (`k≤L`).
> - **Proved.** Both unconditionally (mod the stated `Invertible` hyps), over any `CommRing`. The per-layer
>   identity is the core-reconstruction cancellation; the global identity is `prodSchurCore_eq_coreProd`
>   (associativity) composed with the banked `schur_product_ldu_rec`.
> - **Assumed.** `Invertible (C k)₁₁`, `Invertible (partProd C k)₁₁` — hold at the deepest point (every pivot `I`).
> - **Cited.** none. **Deferred.** the concrete bridge `blockSchur (partProd C L) = ScoreSchur` (Fin-side).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Invariant A (top-row half — `hsub3reg` up-side)

> **Claim.** For any `Z₀` down-override, the joint move's up-edit `Y'_s = Y_s + N_s⁻¹ u_s (S_s − S̃_s)`
> leaves the top block-row `((partProd)₁₁, (partProd)₁₂)` of every partial product unchanged. At `s = L`
> this is `(P'11, P'12) = (P11, P12)` — the clean half of `deepestEFull` invariance.
>
> - **Lean:** `DLNFibre.DLN.RLCT.topRow_movedC`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiSplitGenMoved.lean` @ `<SHA>`)
> - **Gloss.** `(partProd (movedC C Z0edit) s)₁₁ = (partProd C s)₁₁ ∧ (partProd (movedC C Z0edit) s)₁₂ = (partProd C s)₁₂`,
>   for all `s`, any `Z0edit`, given `∀ s, IsUnit (partProd C s)₁₁` and `∀ s, IsUnit (nMix C s)` (`N_s = I + u_s V_s`).
> - **Proved.** Unconditionally (mod the `IsUnit` hyps), by induction on `s`: the pivot block via
>   `R_mul_movedZ` (`R_0 = 0` and `Z'_s = Z_s` for `s ≥ 1` make the `Z₀` edit invisible to the top row);
>   the up block via `Rstep` (the up-edit cancellation `cancel_up`: `(B_s + R_s V_s)·ΔY_s = R_s (S_s − S̃_s)`).
> - **Assumed.** `IsUnit (partProd C s)₁₁`, `IsUnit (nMix C s)` — hold at the deepest point.
> - **Cited.** none. **Deferred.** the down half (`(partProd)₂₁ = P21`, the `Z₀` accumulator lemma) and
>   the concrete instantiation into `deepestEFull` coords.
> - **Structure & ideas observed (p&p cert §2/§3).** The joint move exists exactly (verified `L≤5, m≤3, r≤2`);
>   the `Z₀` down-edit is invisible to the top row (`R_0 = 0`), decoupling top-row from the `Z₀` accumulator —
>   confirmed numerically here (`toprow_check.py`, arbitrary `Z₀`, all `L,r,m` ✓). The up-edit is exactly the
>   amount that keeps `B_s, u_s` fixed (the cert's mechanism), formalised as the `cancel_up`/`Rstep` cancellation.
> - **Route (controller/cert §6).** items 1–3: normalised data + per-layer targets + up-edit top-row lemma.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Not closed

`hstep2` (`DeepestL2Wiring:1060`) is UNTOUCHED. Remaining, in cert §6 order (precise):
1. **Left-column lemma** (Invariant A down-half): the abstract `Ŵ_{s+1} = Ŵ_s M_s S̃_s` accumulator +
   `a_s/ã_s` + `ΔV_0 = a_L − ã_L`, giving `(partProd (movedC C ((V_0+ΔV_0)·A_0)) L)₂₁ = (partProd C L)₂₁`.
   The genuinely-new `L`-recursive identity (cert's most-likely-to-break); couples the bottom-left with the
   evolving bottom-right block.
2. **Concrete `psiSplitRawGen` def** on `DeepestSplit` coords (write `gaugeReadY` all layers + `gaugeReadZ₀`,
   leave `gaugeReadX`; core-slot edit via `paramsEquivFlat`) + the `Fin`-side bridge `framedParamsPivot ↔ partProd`.
3. **Diffeo triple** (`psiSplitRawGen 0 = 0`, `D(psiSplitRawGen − id)(0) = 0`, `ContDiffAt`) → fire
   `DeepestPsiFlatCutGen`.
4. **`hsub3reg`/`hsub4core` wiring + compose** `deepest_diffeo_bridge_gen_assembled` into `DeepestL2Wiring:1060`.

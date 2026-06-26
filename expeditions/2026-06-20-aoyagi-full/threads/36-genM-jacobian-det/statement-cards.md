# Statement cards — thread 36 det tide (item 2 + the det assembly skeleton)

Branch `worktree-agent-a3901f84e4049cbfa` (off `expedition/aoyagi-full`). All sorry-free, axiom-clean
`[propext, Classical.choice, Quot.sound]` (force-elaborated `#print axioms`, olean deleted first).

---

> **Claim.** Conjugating a nonlinear factor `g : B → B` (pointwise fderiv `gD`), identity on a rest
> space `R`, into the flat ambient via any CLE `E : (Fin N → ℝ) ≃L[ℝ] B × R` yields a `ChartFactor N`
> whose fderiv's absolute determinant at `u` is `|det (gD ((E u).1))|` — the rest washes out.
>
> - **Lean:** `DLNFibre.DLN.RLCT.conjBlock_abs_det`, `conjBlock_hasFDerivAt`, `conjBlockFactor`,
>   `conjBlockFactor_abs_det` (`lean/DLNFibre/DLN/RLCT/Validate/RouteMConjBlock.lean` @ `747b809b`)
> - **Gloss.** `conjBlockMap E g := E.symm ∘ (g ⊕ id) ∘ E`; its fderiv at `u` is `E.symm ∘ (gD (E u).1
>   ⊕ id) ∘ E`; `|det| = |det (gD (E u).1)|` via `det_prodMap`+`det_id` (rest contributes `det = 1`)
>   and `LinearMap.det_conj` (conjugation preserves det).
> - **Proved.** The fderiv `HasFDerivAt` (chain rule on the linear CLEs + `prodMap g id`) and the
>   abs-det `= J ((E u).1)` for any `J` with `∀ b, |det (gD b)| = J b`. A linear-factor non-vacuity
>   witness in-file.
> - **Assumed / Cited / Deferred.** none.
> - **Route.** Codex-recommended (item-2 consult, `codex/`): the det needs only SOME CLE `E`, so the
>   generic workhorse replaces the per-factor `ChartIdx` coordinatization for the determinant.
> - **Status.** sorry-free.

---

> **Claim.** The Schur-frame / LDU-core nonlinear factor maps have `HasFDerivAt` equal to the banked
> Phase-A differentials, and their conjugated full-ambient `ChartFactor`s carry the banked monomial
> determinants; the chain factor is the banked linear det-1 map.
>
> - **Lean:** `DLNFibre.DLN.RLCT.schurFrameMap_hasFDerivAt`, `lduCoreMap_hasFDerivAt`,
>   `schurChartFactor_abs_det`, `lduChartFactor_abs_det`, `chainChartFactor_abs_det`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMFactorMaps.lean` @ `747b809b`), built on
>   `RouteMFactorFDeriv` (`HasFDerivAt.matMul`, the diamond-free matrix pi-norm).
> - **Gloss.** `schurFrameMap (K,N,X,E) = (K, KN, (XK, XKN+E))` has fderiv `schurFrameDeriv X K N`
>   (`|det| = |K.det|^(r+c)`); `lduCoreMap (l,q,u) = split((1+L)·diag q·(1+U))` has fderiv
>   `lduCoreDeriv l q u` (`|det| = ∏|q_i|^{2(t−1−i)}`); the conjugated factors read the block from
>   the prefix `(E u).1`.
> - **Proved.** The two `HasFDerivAt`s (product rule via `HasFDerivAt.matMul` + entrywise match to
>   `schurFrameDeriv_apply` / `lduDerivMat_apply`) and the three conjugated `ChartFactor` dets.
> - **Assumed.** Each factor is parametric in an ambient-split CLE `E` (the SPECIFIC `E` — the chart
>   match — is item 3, NOT supplied here).
> - **Cited / Deferred.** none cited; the SPECIFIC `E` deferred to item 3.
> - **Status.** sorry-free. **This is the item-2 deliverable, complete ∀M.**

---

> **Claim.** `|det (fderiv φ_flat u)| = ∏_j |u_j|^{leafH j}` GIVEN the factored-chart map equality
> `composeFold fs = φ_flat` (item 3) and the per-factor det product = the leafH monomial (item 4).
>
> - **Lean:** `DLNFibre.DLN.RLCT.phiFlat_abs_det_of_factored`, `phiFlat_hasFDerivAt_of_factored`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMPhiFlatDet.lean` @ `747b809b`)
> - **Gloss.** The map equality pins `fderiv φ_flat u = (foldDerivList fs u).prod`; the banked
>   telescope `composeFold_abs_det` turns its det into the per-factor product, which `hdet` equates to
>   `∏_j |u_j|^{leafH j}`.
> - **Proved.** The conditional `phiFlat_abs_det` — the det telescope between the two hypotheses is
>   closed. The fderiv-transfer (`HasFDerivAt.fderiv`) makes the conclusion about the genuine
>   `fderiv ℝ φ_flat`, not just the factored map.
> - **Assumed / Deferred.** `composeFold fs = φ_flat` (item 3, the architectural wall — needs a
>   structured `genBlkFlat` redefinition, see `thread.md` UPDATE) and the leafH summation `hdet`
>   (item 4 bookkeeping). Both deferred — the unconditional `phiFlat_abs_det` is NOT yet established.
> - **Cited.** none.
> - **Status.** sorry-free (conditional). The DET SIDE is complete modulo the two named hypotheses.

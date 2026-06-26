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

---

> **Claim.** The achiever-chart flat coordinates split into DISJOINT per-(boundary, role, entry) slots
> via the banked bijective `chartIdxEquiv` — the foundation that lets the structured decoder + the
> factor CLEs read the same disjoint coords (the item-3 unblock).
>
> - **Lean:** `DLNFibre.DLN.RLCT.schurSlotEquiv`, `liftSlotEquiv`, `readSchur`, `readLift`,
>   `readSchur_index_injective`, `readSchur_ne_readLift_index`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMChartSlots.lean` @ `85d6642d`)
> - **Gloss.** `Fin (schurDim k) ≃ Fin t_k × Fin M_{k+1}` (and the lift analog) via `finProdFinEquiv`;
>   `readSchur … k i j = x (chartIdxEquiv.symm ⟨k, inl (slot (i,j))⟩)` reads a unique flat coord per
>   `(k,i,j)`; distinct triples / distinct roles read distinct coords (injectivity of `chartIdxEquiv`).
> - **Proved.** The slot equivalences + the reader disjointness. Slot↔role alignment verified vs
>   (3,3,3,3): `schurDim k ↔ frame(k+1)`/leaf, `liftDim k ↔ lift W_{k+1}`, `∑ = N`.
> - **Assumed / Cited / Deferred.** none proved here beyond the readers; the structured decoder that
>   USES them (`genBlkFlatStruct`) and the item-3 map equality are the next-tide build (see `thread.md`
>   UPDATE-2).
> - **Status.** sorry-free. The shared coordinate foundation for the item-3 unblock.

---

> **Claim.** The STRUCTURED disjoint-slot decoder `genBlkFlatStruct` keeps the rate ∀M:
> `routeMCore M (phiFlatStruct u) = u²·VvalGen` unconditionally.
>
> - **Lean:** `DLNFibre.DLN.RLCT.genBlkFlatStruct`, `C0_eq_one`, `hC0_struct`,
>   `routeMCore_phiFlatStruct` (`lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean` @ `a94ccf54`),
>   on `RouteMChartSlots` (`bmatStack`/`frameSplitEquiv`/`rmatPad`/readers).
> - **Gloss.** `genBlkFlatStruct` reads K/X/N/E/W from disjoint `chartIdxEquiv` slots, derives
>   `Bmat (k+1) = [K; X·K]`, `Rmat (k+1) = [[0,0],[0,E]]` ⟹ `C_{k+1}` is the Schur frame; identity
>   boundary `k=0`. `C0_eq_one` proves `C 0 = 1` (the `chainQ`-at-`c_0=0` collapse). The rate transfers
>   via the decoder-agnostic `routeMCore_phiGen`.
> - **Proved.** The structured decoder + the unconditional rate ∀M + the identity-boundary `C 0 = 1`.
> - **Assumed.** `StructAdm M t` (the chart side conditions + the achiever descent `Text(k+2) ≤
>   Text(k+1)` + `Text(k+2) ≤ Wext(k+1)`).
> - **Cited / Deferred.** none cited. The factored chart's det (item-4) is deferred to the factor-list
>   assembly.
> - **Status.** sorry-free. The decoder + rate side of the structured chart, COMPLETE ∀M.

---

> **Claim.** The factored chart's Jacobian determinant is the leafH monomial, with NO map equality:
> `|det (fderiv (composeFold fs) u)| = ∏_j |u_j|^{leafH j}`, given the per-factor det product = the
> monomial (item-4 bookkeeping).
>
> - **Lean:** `DLNFibre.DLN.RLCT.composeFold_abs_det_leafH`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMPhiFlatDet.lean` @ `a94ccf54`)
> - **Gloss.** The chart DEFINED as `composeFold fs` has fderiv `(foldDerivList fs u).prod`
>   (`composeFold_hasFDerivAt`); its det telescopes (`composeFold_abs_det`) to the per-factor product,
>   which `hdet` equates to `∏_j |u_j|^{leafH j}`. The map equality is needed only for the rate, not the
>   det.
> - **Proved.** The det theorem (no map equality). Validated end-to-end on the radial-only instance.
> - **Assumed / Deferred.** `hdet` (item-4: the factor list `fs` + the leafH summation — the remaining
>   factor-list-assembly build; the spine is validated, the CLEs + multi-factor product remain).
> - **Cited.** none.
> - **Status.** sorry-free. The genuine `phiFlat_abs_det` for `phiFlat := composeFold fs`, reduced to
>   the item-4 bookkeeping (no deep map-equality induction).

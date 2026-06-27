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

> **Claim.** The achiever-path box-divergence atom `routeMCore_box_diverges_achiever` holds for
> `M = (2,2,1)` — the smallest genuinely-layered node, built end-to-end through the general
> option-(C) machinery (the VALIDATE-SMALL checkpoint for the ∀M chart, decoder-fix +
> achiever-path certificates). A `NodeAchieverChart M221` exists.
>
> - **Lean:** `DLNFibre.DLN.RLCT.nodeChart221`, `routeM221_box_diverges`,
>   `routeMCore_box_diverges_achiever_221`, `routeM221_box_diverges_at_one`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteM221.lean` @ `198aea76`, branch
>   `worktree-agent-ad2564eac0d265652` off `expedition/aoyagi-full`).
> - **Gloss.** `M221 = ![2,2,1]`, `minAdm = 2`, `flatDim = 6`. Chart
>   `phi221 = paramsEquivFlat ∘ pack221 ∘ pivotBlowupOn {0,1} 0`: `A1 = !![u₀; u₀·u₁]` (deepest factor,
>   pivot `u₀` scaling the fixed-1 residual + 1 active `u₁`), `A0 = !![u2,u3;u4,u5]` (free spectators).
>   - RATE field (`leaf_integrand`): `routeMCore M221 (phi221 u) = u₀²·U` exactly
>     (`dlnLoss_chartParams221`, sympy-verified vs certificate §4b), `U > 0` a.e. via the
>     genuine-polynomial null-zero-set route (`UPoly221 ≠ 0`, `MvPolynomial.ae_eval_ne_zero`).
>   - DET field (`cov`): `|det Dφ| = |u₀|¹ = |u₀|^{minAdm−1}` via the chain rule
>     `Q221CLM_abs_det` (`= 1`, measure-preserving pack) · `pb221_abs_det` (`= |u₀|^{card−1}`).
>   - The pack `pack221` is measure-preserving via the BANKED
>     `measurePreserving_paramsPack_of_flatIdxEquiv` with a GENUINE `fin6EquivFlatIdx221 :
>     Fin 6 ≃ FlatIdx M221` (`left_inv`/`right_inv` by `decide` — NO dead slots, the D1 guard from
>     the certificate). Binding axis `(k,h) = (1,1)`, threshold `1 = ½·minAdm`.
> - **Proved.** The `NodeAchieverChart M221` bundle (all fields) and the atom discharge via the
>   M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`. Exercises BOTH chart obligations
>   (rate + det) through the general option-(C) bricks — `pivotBlowupOn`, `pack` via the banked MP,
>   the linear reshape `Q221CLM`, the genuine-polynomial `U > 0`. Unlike the prior anchors this rides
>   the general machinery (the (4,4,2,2)/(3,3,4) anchors hand-built charts; this is the
>   end-to-end-through-the-engine layered validate-small the brief commissioned).
> - **Assumed.** none.
> - **Cited.** `monomial_rlct` (S2, the leaf monomial RLCT atom), reached through
>   `monomialIntegrand_lintegral_box_eq_top` — the SAME single citation the `routeM4422_box_diverges`
>   anchor carries (identical force-elaborated `#print axioms` footprint).
> - **Deferred.** the ∀M `nodeChartGeneral M (hpos)` — needs the opaque-width `e_M : Fin N ≃ FlatIdx M`
>   placing the chosen-`T*` Aoyagi blocks (the dependent-width bijection, KC2), the per-`M` `pack`/`Q`,
>   and the layer-op spectator factors for `L ≥ 3` split-codim nodes. This card is the (2,2,1)
>   instance, the validate-small headline checkpoint — NOT the general atom.
> - **Status.** sorry-free; force-elaborated `#print axioms` (olean deleted first):
>   `nodeChart221` is S2-free `[propext, Classical.choice, Quot.sound]`; the divergence theorems carry
>   only the cited `monomial_rlct`.

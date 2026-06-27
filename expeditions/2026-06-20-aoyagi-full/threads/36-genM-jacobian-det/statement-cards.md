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

---

> **Claim.** The achiever-path box-divergence atom `routeMCore_box_diverges_achiever` holds for
> `M = (2,2,2)` — the smallest genuinely MULTI-BOUNDARY node (`minAdm = 3`, rank drops at the Schur
> boundary `k=1` AND the leaf), built end-to-end through the GENERAL `chainOfMt`/`GenBlk` engine via
> ROUTE 2a (`φ_det := phiGen(B_det222)`, the full-rank decoder). A `NodeAchieverChart M222` exists.
>
> - **Lean:** `DLNFibre.DLN.RLCT.nodeChart222`, `routeMCore_box_diverges_achiever_222`,
>   `chartParamsGen_eq_chartParams222`, `phi222_abs_det`, `routeMCore_phi222`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean`, branch `fm/222det-finish` off
>   `expedition/aoyagi-full`).
> - **Gloss.** `M222 = ![2,2,2]`, `tach222 = (2,1,0)` (the genuine achiever path, `Text=[2,2,1]`,
>   chain-codim `= minAdm = 3`), `routeMAmbient = 8`.
>   - **The bridge** `chartParamsGen_eq_chartParams222`: the chain's layers from the full-rank decoder
>     `B_det222` (identity boundary `k=0`, Schur drop `k=1` with `1×1` E-block, LIVE leaf
>     `Rfin 2 = !![1, x7]`), reindexed to the `M`-widths, ARE the explicit Schur-frame matrices
>     `chartA0_222 = !![x4, x4·x1; x5, x5·x1+x6·x0]` (= `C 1`) and
>     `chartA1_222 = !![x0−x1·x2, x0·x7−x1·x3; x2, x3]` (= `chainA(N1)(W1)(C2)`). S2-free.
>   - RATE field (`leaf_integrand`): `routeMCore M222 (phi222 x) = (x0)²·U` exactly
>     (`routeMCore_phi222`, the product `A0·A1 = x0·M222bar` so `F = x0²·‖M222bar‖²`, sympy-verified),
>     `U > 0` a.e. via the genuine-polynomial null-zero-set route (`UPoly222 ≠ 0`).
>   - DET field (`cov`): `|det Dφ| = |x0|²·|x4| = |x0|^{minAdm−1}·|x4|` — the radial `|x0|²` TIMES a
>     genuine SPECTATOR `|x4|` (the Schur-coupled chart is NOT pure-radial). Via the factorization
>     `chartParams222 = pack222 ∘ T222`, `T222 = bsubst222 ∘ shear222 ∘ pb222`: `pb222 = pivotBlowupOn
>     {0,6,7} 0` (det `|x0|²`), `shear222` the det-1 Schur shear, `bsubst222 = pivotBlowupOn {1,4} 4`
>     (det `|x4|`); `Q222CLM = paramsEquivFlat ∘ pack222` measure-preserving (`|det| = 1`).
>   - `phi222` is `InjOn` off `{x0=0} ∪ {x4=0}` (the det's vanishing locus, both null); the `cov` runs
>     on the doubly-punctured complement with the `{x4=0}` slice added back as a TWO-SIDED null
>     contribution (LHS image null via `phi222_slice_image_null`; RHS weight `|x4| = 0`) — the SAME
>     two-axis structure as the (3,3,4) `{u1=0}` slice. Binding axis `(k,h) = (1,2)`, threshold
>     `(2+1)/(2·1) = 3/2 = ½·minAdm` (the spectator `x4` sits on a `k=0` axis, ratio ∞, so it does
>     NOT lower the threshold).
> - **Proved.** The `NodeAchieverChart M222` bundle (all fields) and the atom discharge via the
>   M-agnostic `routeMCore_box_diverges_of_nodeChart`. ROUTE 2a end-to-end through the GENERAL engine
>   (the bridge to the Schur-frame matrices), so the multi-boundary Schur coupling — load-bearing for
>   the RATE on split-codim nodes (thread FINDING 1: pure-radial FAILS the rate here) — IS genuinely
>   exercised, unlike the pure-radial `(2,2,1)`/`(4,4,2,2)` anchors.
> - **Assumed.** none.
> - **Cited.** `monomial_rlct` (S2, the leaf monomial RLCT atom), reached through
>   `monomialIntegrand_lintegral_box_eq_top` — the SAME single citation the `(4,4,2,2)`/`(2,2,1)`/
>   `(3,3,3,3)` anchors carry (identical force-elaborated `#print axioms` footprint
>   `[propext, Classical.choice, Quot.sound, monomial_rlct]`).
> - **Deferred.** the ∀M `nodeChartGeneral M (hpos)`. This card is the (2,2,2) instance — the
>   multi-boundary validate-small COMPLETE, the headline checkpoint the brief commissioned. NOT the
>   general atom.
> - **Structure & ideas observed.** The cast kernel that cracked the bridge (the recurring
>   dependent-`Fin`-width quirk, now isolated): after `ext`/`fin_cases` the indices are `Fin.mk`s typed
>   at `Fin (Wext/Text M222 …)` (defeq but not syntactic `Fin n`), so the matrix-apply simp lemmas do
>   NOT fire and `Fin.zero_eta`/`Fin.mk_one` do NOT normalize them (the width is not a syntactic
>   succ). The working pattern: prove each entry as a `have` at EXPLICIT `⟨_, by decide⟩` indices (the
>   LHS row rewritten to the `castAdd`/`natAdd` kept/lift form so `chainA_apply_*` fire; the scalar
>   `show`-normalized to the clean typed form), then `exact` it into the `fin_cases` goal (Fin
>   proof-irrelevance unifies `⟨0,⋯⟩` with `⟨0, by decide⟩`). The det-factorization key (Codex
>   `det222-factorization-*`): ORDER the shear BEFORE the `bsubst` blow-up so the shear uses the BARE
>   `x1` (slot 1), and `bsubst` replaces slot 1 with `x4·x1` afterward — dissolving the apparent
>   obstruction (`x1` appearing both as `x4·x1` and bare `x1`).
> - **Route.** ROUTE 2a (controller, `certificate-rate-det-route.md`): one chart `φ_det = phiGen(B_det)`,
>   RATE via the decoder-agnostic banked `routeMCore_phiGen`, DET via the bridge to explicit matrices +
>   the `pack ∘ pivotBlowup ∘ shear` chain-rule (the (3,3,4) two-axis cov template).
> - **Status.** sorry-free; force-elaborated `#print axioms` (olean deleted first): `nodeChart222`,
>   `chartParamsGen_eq_chartParams222`, `phi222_abs_det` are S2-free `[propext, Classical.choice,
>   Quot.sound]`; `routeMCore_box_diverges_achiever_222` carries only the cited `monomial_rlct`.

---

> **Claim.** The `(3,3,3,3)` ROUTE-2a parametric-bridge VALIDATE-SMALL: the full-rank decoder `B_det3333`
> reproduces the banked hand-built explicit chart `chartParams3333` through the general
> `chainOfMt`/`GenBlk` engine, at the genuine 3-boundary node (`t* = (2,1,0)`, `minAdm = 6`, rank drops
> at ALL THREE boundaries). The bridge `chartParamsGen(B_det3333 x) = chartParams3333 x` is the
> width-parametric funext template for the ∀M lift.
>
> - **Lean:** `DLNFibre.DLN.RLCT.chartParamsGen_eq_chartParams3333`, `phiGen_B_det3333_eq_phi3333`,
>   `routeMCore_phiDet3333`, `routeMCore_box_diverges_achiever_3333_route2a`, `B_det3333`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteM3333Det.lean`, branch `fm/222det-finish` off
>   `expedition/aoyagi-full`).
> - **Gloss.** `M3333 = ![3,3,3,3]`, `tach3333 = (3,2,1,0)` (chain-`t`: `t 0 = M 0 = 3`, Aoyagi
>   `T* = (2,1,0)`), `Text = [3,3,2,1,0]`, `Wext = [3,3,3,3]`, `routeMAmbient = 27`.
>   - **The bridge** `chartParamsGen_eq_chartParams3333`: the three chain layers `Agen 0/1/2` (reindexed
>     to the `M`-widths) ARE the banked explicit `chartA3333`/`chartB3333`/`chartC3333` (sympy-verified
>     EXACT, `/tmp/match3333.py`). Proven by per-layer `Agen{0,1,2}_3333_eq` (the kept-row
>     `chainA_apply_castAdd` / lift-row `chainA_apply_natAdd` entry laws + the banked
>     `have`+`exact`-at-explicit-`⟨_,by decide⟩`-index cast pattern) + the `finCongr` (`rfl`-width)
>     reindex collapse. The recursive transitions `C_3 = u·Rfin 3` (`Cgen3333_leaf`),
>     `C_2 = Bmat 2·chainQ(N_2) + u·Rmat 2` (`C2_eq3333`, via `chainQ2_eq3333`), `C_1 = Bmat 1·chainQ(N_1)
>     + u·Rmat 1` (`C1_eq3333`, via `chainQ1_eq3333`). S2-free.
>   - **The full-rank decoder** `B_det3333`: identity boundary `Bmat 0 = I₃` (`c_0 = 0`); Schur frame
>     `Bmat 1` (3×2, the deepest LDU core `K`), `Bmat 2 = [b; ℓb]` (2×1); `Nblk 1 = [m₁;m₂]`,
>     `Nblk 2 = [n₁,n₂]`; `Wblk 1 = [r]`, `Wblk 2 = [h₁;h₂]`; `Rmat 1 = e₂₂` (the fixed-`1` pivot scaled
>     by `u`), `Rmat 2 = [[0],[0,η]]`; LIVE leaf `Rfin 3 = [ζ]` (the D1 fix). Every coord lands in some
>     entry (full-rank).
>   - **Rate** `routeMCore_phiDet3333 = u²·V` (one-line via the banked decoder-agnostic
>     `routeMCore_phiGen` + `hC0_3333`; the drops at all 3 boundaries telescope to ONE `u`).
>   - **Chart equality** `phiGen_B_det3333_eq_phi3333`: the ROUTE-2a chart `phiGen (x 0) M3333 tach3333
>     (B_det3333 x) hleach3333 = phi3333 x` (via the bridge under `paramsEquivFlat`). So the banked
>     `phi3333`-based det (`phi3333_abs_det = |u0|⁵·|u1|⁴·|u4|²·|u9|³`), `nodeChart3333`, and the atom
>     transfer to the ROUTE-2a chart for free — no new bundle.
> - **Proved.** The bridge + the ROUTE-2a chart equality + the rate, all sorry-free; the atom
>   `routeMCore_box_diverges_achiever_3333_route2a` (= the banked `_3333`, reached via ROUTE 2a). The
>   genuine 3-boundary node exercises the multi-boundary Schur/LDU coupling the single-drop anchors
>   `(2,2,1)`/`(4,4,2,2)` and the 2-boundary `(2,2,2)` do not.
> - **Assumed.** none.
> - **Cited.** `monomial_rlct` (S2), reached through the banked `routeMCore_box_diverges_achiever_3333`
>   — identical footprint to the `(2,2,2)`/`(4,4,2,2)`/`(2,2,1)` anchors
>   (`[propext, Classical.choice, Quot.sound, monomial_rlct]`).
> - **Deferred.** the ∀M `nodeChartGeneral M (hpos)` (the `List.ofFn` lift). This card is the (3,3,3,3)
>   validate-small — the 3-boundary parametric-bridge template, NOT the general atom. The bridge proof
>   is per-`M`-concrete here (the explicit `B_det3333`/`chartParams3333`); the ∀M version needs `B_det M`
>   + `pack_M`/`T_M` width-parametric + the bridge funext over opaque `Text`/`Wext` widths.
> - **Regression (gate, the cert's cross-check).** The det `|u0|⁵·|u1|⁴·|u4|²·|u9|³` matches the banked
>   `RouteM3333.phi3333_abs_det` EXACTLY — guaranteed by `phiGen_B_det3333_eq_phi3333` (the ROUTE-2a
>   chart IS `phi3333`). The chain layers `A_0/A_1/A_2` were sympy-verified EXACT against
>   `chartA3333`/`chartB3333`/`chartC3333` before any Lean.
> - **Status.** sorry-free; force-elaborated `#print axioms` (olean deleted first): the bridge / chart
>   equality / rate are S2-free `[propext, Classical.choice, Quot.sound]`; the atom carries the cited
>   `monomial_rlct`. Full `lake build DLNFibre` green (8483 jobs).

---

## Statement card — `exists_achieverUfun_ne_zero_interior` / `achieverUbound_interior` (INTERIOR-drop witness tide)

- **Module.** `lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean` (655 LoC). Dep order:
  imports `RouteMAchieverVvalPoly` (transitively the achiever chain stack); to wire into the aggregator,
  add `import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior` after `RouteMAchieverVvalPoly`.
- **Lean (headline).**
  - `exists_achieverUfun_ne_zero_interior (M : Fin (L+1) → ℕ) (hL : 0 < L) (hN : 0 < routeMAmbient M)
    (hInt : InteriorDrop M) : ∃ w, achieverUfun M hL hN w ≠ 0`
  - `achieverUbound_interior … (hInt : InteriorDrop M) : ∀ δ, ∃ B, 0 < B ∧ (∀ u ∈ box, achieverUfun … u
    ≤ B) ∧ ∀ᵐ u ∂(volume.restrict box), 0 < achieverUfun … u` — the full rate-side `NodeAchieverChart.Ubound`
    field for interior-drop `M` (the box-bound + a.e.-positivity), with NO separate witness hypothesis.
- **Hypothesis `InteriorDrop M`** (chain-native, decidable): `0 < Wext M L ∧ ∃ p, 1 ≤ p ∧ p < L ∧
  Text M (tach M) (p+1) < Text M (tach M) p ∧ ∀ b, p ≤ b → b < L → Text M (tach M) (b+1) < Wext M b`.
  English: some interior chain boundary `p` drops the row rank, the column rank drops at every boundary of
  the tail `[p,L−1]`, and the final width `M_L ≥ 1`. **Validated `InteriorDrop ↔` the cert's interior class
  (`r_p,c_p ≥ 1` at the deepest interior `p*`), 285/285 over the `widths 1..3`/`L∈{2,3,4}` grid** (and
  `M_L=0` never occurs for interior `M`). So this is exactly the 285/351 interior class, expressed in the
  widths the achiever chain reads.
- **Proved.** The witness `wInt := wOnIdx ∘ chartIdxEquiv` realizes the cert's blocks (reader lemmas
  `readK_wInt = I`, `readX/N_wInt = 0`, `readE_wInt = pivot`, `readW_wInt = carrier`); the structured
  decoder's blocks discharge to the abstract-induction hypotheses (`genBlk_Bmat_succ_top/_bot`,
  `genBlk_Bmat_zero_top`, `genBlk_Rmat_succ_zero`, `genBlk_Rmat_pivot`, `genBlk_E_zero`); the three downward
  inductions (`suffix_carrier`, `Hmat_pivot`, `Hmat_row_thread`) over the banked entry laws give the
  surviving entry `Hmat 0 (Text(p+1), 0) = 1`; `sqSumHmat0_ne_zero_of_entry` lifts that to `achieverUfun ≠ 0`.
  All sorry-free.
- **Assumed.** none.
- **Cited.** the banked reduction `RouteMAchieverVvalPoly` (`achieverUfun_eq_eval`, `eval_UPolyGen`,
  `achieverUbound`, `UPolyGen_ne_zero_of_witness`) + the entry laws (`bmatStack_top/_bot`,
  `chainA_apply_natAdd`) + `genBlkFlatStruct`/`chainOfMt`/`Chain` (suffix/Hmat/telescope).
- **Deferred.** the BOUNDARY classes (CLEAN-20 cite `RouteM4422`/`RouteM221`; SMEARED-46 the multi-axis
  bundle) — separate later tides. The `nodeChartGeneral` 4-way assembly. The colPath chart's Jacobian
  `|det| = |u_p|^{minAdm−1}` (thread-36 det programme, separate).
- **Build precision (durable note).** The recurring `c.Wwid` vs `c.toChain.Wwid` projection mismatch (same
  value, distinct projections) breaks `HMul` instance synthesis in matrix products mixing `FactoredChain`
  and `Chain` fields; resolve by ascribing each matrix to its literal `Wext`/`Text` type via a local `let`
  (`Hmat_pivot`), or by a generic `mul_three_reassoc' {p q r s} (a b c)` whose abstract index types unify up
  to defeq (the `lean/CLAUDE.md` fully-applied-term kernel). omega over `Text`/`Wext` needs `k+1+1`
  normalized to `k+2` (distinct atoms otherwise — `simp only [show k+1+1=k+2 from rfl]`).
- **Status.** sorry-free; force-elaborated `#print axioms` (olean deleted first):
  `exists_achieverUfun_ne_zero_interior` + `achieverUbound_interior` are S2-free
  `[propext, Classical.choice, Quot.sound]`. Full `lake build DLNFibre` green WITH the module temp-imported
  (8518 jobs, 0 name clashes); reverted the aggregator edit for the single-writer controller to wire.

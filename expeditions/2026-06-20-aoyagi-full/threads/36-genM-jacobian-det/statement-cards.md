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

---

## Boundary-class tide (CLEAN/SMEARED split + the smeared `cov` gating analysis)

Branch `worktree-agent-a223be0c63e358844` (off `expedition/aoyagi-full`, merged in). The classifier is
sorry-free + axiom-clean; the smeared `cov` analysis is the GATING finding handed back to the controller.

---

> **Claim (LANDED).** The BOUNDARY class (`¬InteriorDrop M`) of the ∀M achiever-chart 4-way splits into
> CLEAN (`deepRank M = deepRows M`, i.e. `r = m1`) and SMEARED (`deepRank M < deepRows M`, `r < m1`),
> EXCLUSIVE and — given the achiever-path bottleneck `r ≤ m1` — EXHAUSTIVE; the three classes INTERIOR /
> CLEAN / SMEARED partition all `M`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.BoundaryClean`, `BoundarySmeared`, `deepRank`, `deepRows`,
>   `not_boundaryClean_and_boundarySmeared`, `boundaryClean_or_boundarySmeared`,
>   `boundary_of_clean_or_smeared`, `not_interiorDrop_and_boundaryClean`,
>   `not_interiorDrop_and_boundarySmeared`, `interiorDrop_or_boundaryClean_or_boundarySmeared`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMBoundaryClass.lean` @ `8e25eea4`).
> - **Gloss.** `deepRank M := Text M (tach M) L` (rank into the deepest factor along the achiever path);
>   `deepRows M := Wext M (L−1) = M (L−1)`. `BoundaryClean M := ¬InteriorDrop M ∧ deepRank = deepRows`;
>   `BoundarySmeared M := ¬InteriorDrop M ∧ deepRank < deepRows`. `InteriorDrop` is the LANDED
>   `RouteMAchieverWitnessInterior` predicate (the interior 285/351 class).
> - **Proved.** Exclusivity (CLEAN∧SMEARED impossible by `omega` on `=`/`<`; INTERIOR∧CLEAN,
>   INTERIOR∧SMEARED by the `¬InteriorDrop` conjunct). Exhaustiveness over boundary + the total
>   trichotomy, each GIVEN `hle : deepRank M ≤ deepRows M` (the bottleneck).
> - **Assumed.** `r ≤ m1` (`deepRank ≤ deepRows`) carried as a hypothesis on the exhaustiveness lemmas —
>   it is the validated front-bottleneck (`pp_smear_GATE.py` (U): 46/46 + 20/20 clean), but the widths are
>   noncomputable argmin values, so it is supplied, not `decide`d.
> - **Cited / Deferred.** none cited. The per-branch CHARTS are deferred (CLEAN radial = a ∀M lift of
>   `RouteM4422`; SMEARED `φ_sm` = blocked on the `cov` decision below).
> - **Decidability caveat (next to the claim).** `tStar` is `Classical.choose`, so `tach`/`Text M (tach
>   M)`/`Wext` are NOT `decide`-reducible: the boundary predicates are genuine `Classical` Props; the
>   instances are `Classical.propDecidable` (the assembly's `if … then … else` shape). The predicate
>   FORMULAE are decidable given widths; the widths are noncomputable.
> - **Status.** sorry-free; force-elaborated `#print axioms` (`lake env lean` scratch): all six results
>   `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. (`Classical.choice` from `propDecidable` +
>   the noncomputable widths, expected — NOT a `sorry`.)

---

> **Gating finding (HANDBACK — the flagged uncertainty, the SMEARED `cov`).** The BOUNDARY-SMEARED
> rational chart `φ_sm` does NOT discharge the EXISTING `NodeAchieverChart.cov` field via the banked
> route; the existing `cov` is dischargeable only via a SPLIT requiring a new structural null-image
> lemma OR a structure variant. **Controller decision needed before the SMEARED chart can be built.**
>
> - **The interface, precisely.** `NodeAchieverChart.cov` (`NodeAchieverChart.lean:95–98`) demands the
>   raw lintegral c-o-v `∫⁻_{phi '' (V\{x p=0})} g = ∫⁻_{V\{x p=0}} ofReal(∏|u_j|^{leafH j})·g(phi u)`,
>   removing ONLY the pivot-zero locus `{x p = 0}`. The banked polynomial charts (`phi4422_cov`,
>   `phi334_cov`) discharge it via Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
>   (`Mathlib/MeasureTheory/Function/Jacobian.lean:1189`), whose hypothesis is `HasFDerivWithinAt f (f'
>   x) s x` for **ALL** `x ∈ s = V\{x p=0}` (NOT a.e.), `InjOn f s`, then rewrites `|det f'| = ∏|u_j|^h`.
> - **Why it fails as-is.** `φ_sm`'s routing `Λ_0 = (P_1ᵀP_1)⁻¹P_1ᵀP_2` is RATIONAL — genuinely
>   non-differentiable (undefined) on the pole `N0 := {det(P_1ᵀP_1) = 0}`, a Lebesgue-null algebraic
>   hypersurface in the FRONT coords. `N0 ⊆ s` (it is NOT inside the removed `{z=0}`), so the all-x∈s
>   differentiability hypothesis of the Mathlib lemma FAILS on `s`. There is NO a.e.-differentiable
>   variant of `lintegral_image_eq_lintegral_abs_det_fderiv_mul` in Mathlib v4.29 (only the all-x∈s form).
> - **S1.1 is the WRONG interface for this field.** `weightedThreshold_le_transport` /
>   `weightedThreshold_transport_aux` (`S1Transport.lean`) DO allow differentiability off a null `E`
>   (`hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π …`), BUT they produce an equality/inequality of `weightedThreshold`
>   (an RLCT sSup), NOT the raw lintegral identity `cov` requires. So "route the smeared `cov` through
>   S1.1" (the cert's hope) does NOT type-check against the `cov` field — these are different objects.
> - **Codex (xhigh, decorrelated; `codex/smeared-cov-gating-{prompt,answer}.md`).** Verdict: the EXISTING
>   `cov` IS dischargeable, but via a SPLIT: apply the Mathlib lemma on `s \ N0` (where `φ_sm` is C¹/InjOn
>   with `|det| = ∏|u_j|^{leafH j}`), then add back `s ∩ N0`. RHS over `s ∩ N0` vanishes (null set, no
>   integrand finiteness needed). The LHS obstruction is `volume(φ_sm '' (s ∩ N0)) = 0` — NOT automatic
>   for an arbitrary extension, NOT a Luzin-N consequence (φ_sm is non-Lipschitz on N0). It closes ONLY
>   if the extension keeps the FRONT block = identity on N0, so `φ_sm '' (s∩N0) ⊆ {target front Gram det
>   = 0}`, a TARGET algebraic null set — a structural containment, provable, but a new lemma. Box-
>   divergence survives deleting N0 (a null set never changes an `ℝ≥0∞` lintegral already `= ⊤`).
> - **The decision (ranked, for the controller).** (a) **Cheapest sound:** prove `cov` for `φ_sm` by the
>   split — c-o-v on `s\N0` + the structural front-identity image-null `volume(φ_sm''(s∩N0))=0 ⊆
>   {target Gram det = 0}`. New work: ~1 structural-null lemma + the careful N0-extension; fits the
>   EXISTING field/structure (no new bundle). (b) Add a `cov'` field/structure variant removing an EXTRA
>   null set `{x p=0} ∪ N0` + a matching M-agnostic assembly (the box-divergence LOWER bound is monotone,
>   so removing more null mass is harmless) — more invasive, touches `NodeAchieverChart` +
>   `routeMCore_box_diverges_of_nodeChart`. **Recommendation: (a).** Both are sound; neither is "as-is".
> - **Bottom line.** GAP: the SMEARED `cov` needs the split-route null-image lemma (option (a)) — a
>   bounded but genuinely-new piece, NOT a banked citation and NOT the S1.1 transport the cert named. The
>   rate (`F=z²U`), `U≢0` (polynomial), det (`|z|^{minAdm−1}`), threshold (`½·minAdm`) are all validated
>   46/46 (`pp_smear_GATE.py`) and unblocked; only the `cov` rung is gated on this decision.
> - **Status.** analysis only (no Lean built for the smeared chart, by the GATING-CHECK-FIRST discipline).

---

## SMEARED `cov` build attempt → SHARPER wall (the validate-small `(1,2,1)` finding)

Branch `worktree-agent-a223be0c63e358844`. Controller chose option (a) (least-disruptive `cov` split,
no bundle change) and directed building the SMEARED chart. Building the validate-small `(1,2,1)` surfaced
a wall EARLIER than the `cov` split — handed back for a structure decision.

---

> **Finding (HANDBACK, supersedes "only `cov` is pole-affected").** The rational chart `φ_sm` does NOT
> fit the EXISTING `NodeAchieverChart` — TWO fields are pole-affected, not one. The `leaf_integrand`
> field (∀ u, POINTWISE) breaks at the rational pole, BEFORE the `cov` split is even reached.
>
> - **Lean (the wall witness, sorry-free + axiom-clean `[propext, Classical.choice, Quot.sound]`):**
>   `DLNFibre.DLN.RLCT.dlnLoss_chartParams121_offpole`, `dlnLoss_chartParams121_pole_pos`,
>   `prod_chartParams121_entry`, + the chart defs `chartA0_121`/`chartA1_121`/`chartParams121`/`phi121sm`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteM121Smeared.lean` @ `36654c1a`). Full `lake build DLNFibre`
>   green with the module temp-imported.
> - **The case.** `M = (1,2,1)`, the smallest boundary-smeared node: `r=1, c=1, m1=2, s=1, minAdm=1,
>   flatDim=4`. Chart coords `(a,b,z,sb)`; `A⁰=[a,b]`, `A¹=[z−(b/a)·sb ; sb]`, pole `N0={a=0}`.
> - **The wall, Lean-checked.** OFF the pole (`a≠0`): `dlnLoss = z²·a²` (`dlnLoss_chartParams121_offpole`,
>   the `b·sb` shear cancels). ON the pole, Lean totalizes `b/a = b·0⁻¹ = 0`, so `A⁰·A¹ = b·sb`:
>   at `(0,1,7,1)` the loss is `1 > 0` (`dlnLoss_chartParams121_pole_pos`), while any `z²·U = z²·a² = 0`.
>   So the rate `F∘φ = z²·U` holds ONLY off `N0`. NO diffeo-preserving extension fixes it: at `a=0`,
>   `A⁰·A¹ = b·(A¹ bottom)` and the bottom row `sb` is a FREE coord, so it cannot be forced to `0`.
> - **Why this breaks `leaf_integrand` (∀ u).** `routeMCore_box_diverges_of_nodeChart` (the banked
>   M-agnostic assembly) rewrites `W.leaf_integrand` via `setLIntegral_congr_fun hPmeas` — POINTWISE on
>   ALL of the box `P = [0,δ]^N`, including the pole slice `N0` (a null subset of `P`). The field asserts
>   `F∘φ = u_p²·U` pointwise, which the rational chart cannot supply. So option (a) ("fits the existing
>   structure, only `cov` changes") does NOT hold: `leaf_integrand` is a SECOND pole-affected field.
> - **Codex (xhigh, decorrelated; `codex/smeared-leafintegrand-{prompt,answer}.md`).** Confirms: option
>   (a) as framed does not survive. Ruled out the `Ufun_sm := |F∘φ|/(u_p)²` dodge — it is NOT a legal
>   `Ufun` (bounded-on-box fails: on `{a=0, z→0}` it is `(b·sb)²/z²`, unbounded). Cheapest sound fix:
>   **(i)** weaken `leaf_integrand` to an a.e. statement (`∀ᵐ u`) AND change the assembly's
>   `setLIntegral_congr_fun` to an a.e. `setLIntegral_congr` dropping the pole-null set — i.e. EDIT the
>   banked M-agnostic core `routeMCore_box_diverges_of_nodeChart` + the structure field type. Existing
>   polynomial instances supply the a.e. field for free via `Filter.Eventually.of_forall`. (Most
>   disruptive alternative: a separate `NodeAchieverChartAE` with a.e. fields + its own assembly.)
> - **The decision (controller-gated).** Fix (i) touches the banked core that all instances + the interior
>   branch consume; the a.e. weakening is a strict generalization (polynomial instances unaffected, free
>   `of_forall`), but it is a structure/assembly change, not a per-instance discharge. Recommend (i): one
>   field type change + one `setLIntegral_congr_fun → congr` swap (drop the `{a=0}∪{z=0}` null set) + the
>   `cov` split (the originally-scoped piece). After (i), the smeared chart's `cov` split + the a.e.
>   `leaf_integrand` + rate/det (validated 46/46) discharge the atom for smeared M.
> - **Status.** the wall WITNESS is sorry-free + axiom-clean; the chart INSTANCE is NOT built (blocked on
>   the (i) structure change). NOT in DLNFibre.lean (single-writer; controller wires + decides on (i)).

---

## a.e. `leaf_integrand` core LANDED (option (i)) + smeared `(1,2,1)` on it

Branch `worktree-agent-a223be0c63e358844` @ `50bf346b`. Controller approved option (i) (a.e.
`leaf_integrand` + a.e. assembly rewrite). The wall is RESOLVED — the box-divergence atom is
intrinsically an a.e./lintegral property, so the a.e. field is the faithful form.

---

> **The a.e. `NodeAchieverChart.leaf_integrand` core (the faithful generalization).** The field
> `leaf_integrand : ∀ c, ∀ᵐ u ∂volume, …` (was `∀ c u, …`); the assembly
> `routeMCore_box_diverges_of_nodeChart` swaps its pointwise `setLIntegral_congr_fun` →
> `setLIntegral_congr_fun_ae` (filter_upwards on the a.e. field). A RATIONAL chart supplies it off its
> null pole; a polynomial chart supplies it ∀u via `Filter.Eventually.of_forall`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.NodeAchieverChart.leaf_integrand` (field type) +
>   `routeMCore_box_diverges_of_nodeChart` (assembly), `NodeAchieverChart.lean` @ `50bf346b`.
> - **Strict generalization (bedrock guards, all PASS).** All 4 existing instances (221/222/4422/3333)
>   updated to `leaf_integrand := fun c => Filter.Eventually.of_forall (leaf_integrand_XXX c)` (free —
>   their charts are polynomial). The (3,3,4) `L2AchieverChart` is a SEPARATE structure, untouched.
>   Full `lake build DLNFibre` green (8519 jobs); force-elaborated `#print axioms` on
>   `routeMCore_box_diverges_achiever_222` + `routeM4422_box_diverges`: STILL `[propext,
>   Classical.choice, Quot.sound, monomial_rlct]` — no new axioms, no `sorryAx`.
> - **Status.** LANDED, sorry-free, axiom-preserving. The honest, more-faithful form.

---

> **Smeared `(1,2,1)` on the a.e. core — rate + a.e. leaf_integrand + det-1 LANDED.** The validate-small
> for the rational `φ_sm`, sorry-free + axiom-clean `[propext, Classical.choice, Quot.sound]`.
>
> - **Lean (`RouteM121Smeared.lean` @ `50bf346b`):** `phi121sm`, `routeMCore_phi121sm_offpole`
>   (`F∘φ = z²·a²` off `{a=0}`), `leaf_integrand121_ae` (THE a.e. field, discharged off the null pole),
>   `Uval121 = a²`, `leafH121 ≡ 0`/`leafH121_pivot`, `chartParams121_eq_pack_shear` (shear factorization),
>   `shear121_injOn` (off-pole), `pole121_null`, `shear121DerivMat_det = 1` (the Jacobian det via a
>   transvection chain — `det_updateRow_add_smul_self`, the row-2 shear det-preserving).
> - **Residual (the `cov`-split assembly — bounded, standard analysis, NOT a wall):**
>   `shear121_hasFDerivAt` off-pole (the rational comp-2 `z−(b/a)sb` is C¹ for `a≠0`; fderiv =
>   `shear121DerivMat u`) → `phi121sm_abs_det = 1`; `phi121sm_cov` via the `phi334_cov` two-slice split
>   (c-o-v on `s\N0` + the FRONT-identity image-null `φ_sm''(s∩N0) ⊆ {a-coord=0}`, target null — NOT
>   Luzin-N); then the `NodeAchieverChart M121` instance (a.e. `leaf_integrand := leaf_integrand121_ae`)
>   + `routeMCore_box_diverges_of_nodeChart` discharges the atom for `(1,2,1)`.
> - **Status.** the conceptually-hard pieces (the a.e. leaf_integrand off the pole + the det-1) LANDED;
>   the `cov`-split `HasFDerivAt`/image-null/assembly is the bounded remaining engineering (a next pass,
>   no design wall). NOT in DLNFibre.lean (single-writer; controller wires).

---

## Smeared `(1,2,1)` cov-split — chart-derivative det `= 1` LANDED; off-pole `HasFDerivAt` residual

Branch `worktree-agent-a223be0c63e358844` (on the integrated a.e. core `85a5636f`). Charging the
cov-split: the Jacobian det of the rational chart derivative is now banked; the off-pole `HasFDerivAt`
(comp-2 quotient) is the bounded residual, blocked on a Mathlib-v4.29 plumbing gap (no `HasFDerivAt.div`).

---

> **Smeared `(1,2,1)` cov-split — det `= 1` of the chart derivative LANDED** (sorry-free, axiom-clean
> `[propext, Classical.choice, Quot.sound]`).
>
> - **Lean (`RouteM121Smeared.lean` @ `0a76ab6b`, new this pass):** `shear121DerivMat` (the explicit
>   transvection matrix — `1` with row-2 shear shifts), `shear121DerivMat_det = 1` (via a 3-step
>   transvection chain `Matrix.det_updateRow_add_smul_self`, each row-add det-preserving), `shear121Deriv`
>   (the chart-derivative CLM `= (toLin' shear121DerivMat).toContinuousLinearMap`), `shear121Deriv_abs_det
>   = 1` (`LinearMap.det_toLin'` + the matrix det).
> - **RESIDUAL — `shear121_hasFDerivAt` off the pole (the one stuck piece):** `shear121` comp-2 is
>   `z − y 1·(y 0)⁻¹·y 3`, C¹ for `u 0 ≠ 0`. The OBSTRUCTION is purely Lean plumbing, NOT math: Mathlib
>   v4.29 has **no `HasFDerivAt.div`** (only `hasFDerivAt_inv'` for `x⁻¹`), so comp-2's fderiv must be
>   assembled `(proj 1).mul ((hasFDerivAt_inv' hu).comp (proj 0))` then matched to the matrix-CLM via
>   `HasFDerivAt.congr_fderiv` (a `ContinuousLinearMap.ext` + `field_simp`/`ring`). That CLM-matching
>   `ext`/`field_simp` fought several passes (the `mulLeftRight`-shaped inv-deriv vs the explicit `smul`
>   form). Rested here rather than force it.
> - **After `shear121_hasFDerivAt`:** `phi121sm_hasFDerivAt` (chain with the measure-preserving linear
>   `Q121 = paramsEquivFlat ∘ pack121`, det 1) ⟹ `|det Dφ121sm| = 1`; then `phi121sm_cov` via the
>   `phi334_cov` two-slice split (c-o-v on `S\N0` + the front-identity image-null `φ_sm''(S∩N0) ⊆
>   {a-coord=0}`); then the `NodeAchieverChart M121` instance + the atom. All bounded, no design wall.
> - **Already banked (prior passes, this module):** `routeMCore_phi121sm_offpole` (rate off-pole),
>   `leaf_integrand121_ae` (the a.e. field off the null pole), `Uval121`/`leafH121`/`_pivot`,
>   `chartParams121_eq_pack_shear`, `shear121_injOn`, `pole121_null`.
> - **Status.** the conceptually-load-bearing pieces (a.e. leaf_integrand + the chart-deriv det `= 1`) are
>   LANDED; the residual is the off-pole `HasFDerivAt` CLM-matching (a Mathlib-`.div`-gap plumbing pass) +
>   the standard `cov`-split assembly. Full `lake build DLNFibre` green with the module temp-imported;
>   aggregator reverted (single-writer). The atom for `(1,2,1)` is NOT yet discharged (pending the fderiv).

---

## Smeared cov-split — off-pole `HasFDerivAt` wall (Lean whnf on the matrix-CLM) + the route

Branch `worktree-agent-a223be0c63e358844`. The chart-derivative det `= 1` is landed (prior card);
the off-pole `HasFDerivAt` (the last piece before the cov + atom) hit a precise Lean wall.

---

> **The off-pole `shear121_hasFDerivAt` wall — Lean whnf on `Matrix.of ![...]`-CLM, NOT math.**
>
> - **The math + the idiom are SOLVED.** Codex (xhigh, `codex/shear-fderiv-{prompt,answer}.md`) gave the
>   exact v4.29 quotient-fderiv idiom (Mathlib has no `HasFDerivAt.div`): `hasFDerivAt_inv` (the scalar
>   `Mathlib.Analysis.Calculus.Deriv.Inv` version, cleaner `toSpanSingleton` CLM than `_inv'`) composed
>   with the coord proj, then `.mul`/`.sub`. Verified the comp-2 sub-piece (`ratio10_hasFDerivAt`) builds.
> - **The WALL.** Matching the per-component fderivs to `shear121Deriv := (toLin' (Matrix.of ![..]))`
>   .toContinuousLinearMap` via `congr_fderiv` + `ext v` + the row `dotProduct` TIMES OUT at `whnf`
>   (200000 heartbeats): expanding `(shear121DerivMat u i) ⬝ᵥ v` for the `Matrix.of ![row0..row3]`
>   representation is whnf-heavy (the `Matrix.of`/`vecCons` row access doesn't reduce cheaply under
>   `simp only [shear121DerivMat, dotProduct, Fin.sum_univ_four, …]`). `shear121Deriv_apply` (the row =
>   `mulVec` law) itself builds via `rw […, Matrix.mulVec]` (NO `rfl` — that whnf-times-out), but the
>   four component matches still time out.
> - **The clean next-pass routes (no design wall, both bounded):**
>   (a) represent the shear derivative as a `ContinuousLinearMap.pi` of explicit per-coord functionals
>   (NOT `toLin' (Matrix.of ![..])`), so the component apply is definitional — then re-derive `|det| = 1`
>   from that pi-CLM (a separate small det bridge);
>   (b) **Codex's recommended route — `MeasurePreserving`** (sidesteps the fderiv+det entirely): the repo
>   already has `Foundations.CoreShearMP` (`measurePreserving_coreShear` via `MeasurePreserving.skew_product`)
>   — the shear is a fiberwise `z`-translation (det 1); prove `MeasurePreserving phi121sm` (off-pole or
>   globally, the pole is null) + `MeasurableEmbedding`, then the `cov` (weight `1` since `leafH121 ≡ 0`)
>   follows from `MeasurePreserving.setLIntegral_comp_emb` — no `HasFDerivAt`/`|det|` needed.
> - **Status.** the off-pole `HasFDerivAt` is NOT landed (the matrix-CLM whnf wall). LANDED this pass:
>   `shear121DerivMat`/`_det = 1`, `shear121Deriv`/`_abs_det = 1`. The `(1,2,1)` atom is NOT discharged
>   (pending the fderiv-or-MP route + the cov-split + image-null). Recommend route (b) for the next pass.

---

## Smeared `(1,2,1)` cov LANDED via route (b) (MeasurePreserving) — `image_subset` residual

Branch `worktree-agent-a223be0c63e358844` @ `04b37988`. Controller approved route (b). The `cov` field
is now LANDED with NO `HasFDerivAt`/Jacobian (the whnf wall sidestepped), sorry-free + axiom-clean.

---

> **Smeared `(1,2,1)` `cov` via MeasurePreserving (route (b)) — LANDED.**
>
> - **Lean (`RouteM121Smeared.lean` @ `04b37988`, all `[propext, Classical.choice, Quot.sound]`):**
>   `measurePreserving_coreShear_measurable` (the banked `coreShear` MP, `Continuous`→`Measurable` shift —
>   `skew_product` needs only measurability); `fin4EquivFlatIdx121`/`pack121`/`measurePreserving_pack121`/
>   `measurePreserving_Q121` (the linear outer reshape MP); `shear121ME` (the rational shear as a GLOBAL
>   measurable bijection — the totalized `b/a` cancels at `a=0`, Codex Q3: NO pole-split); `split121`
>   (`Fin 4 → ℝ ≃ᵐ reg×(core×spec)` via `piFinSuccAbove`+`funUnique`) + MP; `split121_shear121` (the
>   forward conjugation); `measurePreserving_shear121` (conjugate `coreShear_measurable` by `split121`);
>   `measurePreserving_phi121sm` + `measurableEmbedding_phi121sm` (`phi121sm = Q121 ∘ shear121`, packaged
>   `phi121smME` via `flatEquivOf`); **`phi121sm_cov`** — the `cov` field directly from
>   `MeasurePreserving.setLIntegral_comp_emb` (`leafH121 ≡ 0` ⟹ weight `1`).
> - **The win:** route (b) sidesteps the off-pole `HasFDerivAt` whnf wall entirely — no Jacobian, no
>   image-null split. The shear's measure-preservation is the banked `CoreShearMP` skew-product
>   conjugated by `split121`; the cov is a one-liner `setLIntegral_comp_emb` + the weight-1 rewrite.
> - **RESIDUAL — `image_subset` is the THIRD pole-affected field (handback).** The
>   `NodeAchieverChart.image_subset` field needs `phi121sm '' [0,δ]^4 ⊆ cubeBox 4 ε`, but the rational
>   `φ_sm` is UNBOUNDED near its pole `{a=0}` (the flat coord `z − (b/a)·sb → ∞` as `a→0`, `b,sb≠0`), so
>   its box-image is not bounded. The assembly `routeMCore_box_diverges_of_nodeChart` uses `image_subset`
>   for the final `∫_{cubeBox} ≥ ∫_{φ''(box\{z=0})} = ⊤` step. Controller-gated fix: restrict the source
>   box to exclude a pole-neighborhood, OR run the final step via the MP `∫_{cubeBox} = ∫_{φ⁻¹(cubeBox)}`
>   (reuse `measurePreserving_phi121sm`) instead of image-containment. Then `Ubound`/`Umeas`/instance/atom.
> - **Status.** rate + a.e.-`leaf_integrand` + the `cov` (the conceptually-load-bearing pieces) all
>   LANDED sorry-free. The `(1,2,1)` atom is NOT yet discharged (the `image_subset` architecture
>   decision + the instance assembly remain). Full `lake build DLNFibre` green with the module
>   temp-imported; aggregator reverted (single-writer).

---

## Smeared `(1,2,1)` — the reusable MP-final lemma (fix b) LANDED; `hsrc` is the bounded finish

Branch `worktree-agent-a223be0c63e358844` @ `a6b790e6`. Controller approved fix (b). The reusable
MP-final-step lemma is landed; the `(1,2,1)` atom needs only the source certificate `hsrc`.

---

> **`routeMCore_box_diverges_of_MPChart` (the reusable MP-final-step, fix b) — LANDED**
> (sorry-free, `[propext, Classical.choice, Quot.sound]`).
>
> - **Lean (`RouteM121Smeared.lean` @ `a6b790e6`):** `routeMCore_box_diverges_of_MPChart M phi (hmp :
>   MeasurePreserving phi) (hemb : MeasurableEmbedding phi) c' ε (hsrc : ∃ S, MeasurableSet S ∧ S ⊆
>   phi⁻¹(cubeBox N ε) ∧ ∫_S (loss∘phi)^{−c'} = ⊤) : ∫_{cubeBox N ε} (loss)^{−c'} = ⊤`. The whole MP
>   step is a 3-line `setLIntegral_comp_preimage_emb` + `lintegral_mono_set` calc (the loss pulled
>   back to `phi⁻¹(cubeBox)`, lower-bounded by the source sub-box `S`).
> - **Why reusable + additive:** NO `image_subset` (the rational `φ_sm` is unbounded near its pole, so
>   image-containment fails). The banked `routeMCore_box_diverges_of_nodeChart` (image_subset-based) is
>   UNTOUCHED — the polynomial interior/clean charts keep it (they are not MP). The ∀M-smeared lift
>   (46 M) reuses `routeMCore_box_diverges_of_MPChart` with each chart's `hsrc`.
> - **RESIDUAL — the `(1,2,1)` source certificate `hsrc` (the bounded finish, concrete analysis, NO
>   design wall).** `S = subBox121 δ := {a=u 0∈[δ/2,δ] (bounded-away-from-pole), b=u 1∈[−δ,δ],
>   z=u 2∈(0,δ), sb=u 3∈[−δ,δ]}`, `δ=ε/4` (Codex `mp-final-step`). Two sub-goals:
>   (1) **containment** `subBox121 δ ⊆ phi121sm⁻¹(cubeBox 4 (4δ))` — needs a flat-coord bound: each of
>   the 4 flat coords of `phi121sm u = paramsEquivFlat(chartParams121 u)` is a matrix entry `≤ 4δ` on
>   the bounded-away box (the only nontrivial one, `z−(b/a)·sb`, is `≤ δ + δ²/(δ/2) = 3δ` since
>   `a ≥ δ/2`). Plumbing: a `phi121sm`-flat-coord readout through `Fintype.equivFin (FlatIdx M121)`
>   (the opaque flat ordering — NO existing forward readout; RouteM221/4422 never needed one), OR show
>   `Q121 = paramsEquivFlat∘pack121` preserves sup-norm (a coord permutation) so `‖phi121sm u‖_∞ =
>   ‖shear121 u‖_∞ ≤ 4δ`.
>   (2) **divergence** `∫_{subBox121 δ} (loss∘φ)^{−c'} = ⊤` — on `Pδ` the rate `loss∘φ = z²·a²`
>   (`routeMCore_phi121sm_offpole`, `a>0`), `(z²a²)^{−c'} = |z|^{−2c'}·|a|^{−2c'}` (reads only `z,a`);
>   peel `z` (`piFinSuccAbove`/`setLIntegral_prod`), `z`-factor over `(0,δ)` is `⊤`
>   (`abs_rpow_lintegral_Ioo_eq_top`, exp `−2c' ≤ −1` from `c' ≥ minAdm/2 = ½`), rest positive-finite.
>   The `prod_rpow_lintegral_Ioo_box_eq_top` template (`Case222Cover`), adapted to the heterogeneous box.
> - **Then** `routeM121sm_box_diverges := routeMCore_box_diverges_of_MPChart M121 phi121sm
>   measurePreserving_phi121sm measurableEmbedding_phi121sm c' ε hsrc` + the atom shape; expect
>   `#print axioms = [propext, Classical.choice, Quot.sound, monomial_rlct]`.
> - **Status.** rate + a.e.-leaf_integrand + cov-via-MP + the reusable MP-final lemma all LANDED
>   sorry-free. The `(1,2,1)` atom is NOT yet discharged (`hsrc` = the two concrete-analysis sub-goals
>   above). Full `lake build DLNFibre` green with the module temp-imported; aggregator reverted.

---

## Smeared `(1,2,1)` atom LANDED (route b) — `routeM121sm_box_diverges`, S2-FREE

Branch `worktree-agent-a223be0c63e358844`. The smallest boundary-SMEARED achiever box-divergence atom
is discharged sorry-free via route (b) (MeasurePreserving, NO `image_subset`, NO `HasFDerivAt`). The
3-file unit (CoreShearMP + ParamsReshapeMP + RouteM121Smeared) is ready for file-level integration.

---

> **`routeM121sm_box_diverges` — the `(1,2,1)` smeared atom, LANDED** (sorry-free; force-elaborated
> `#print axioms`, olean-deleted: `[propext, Classical.choice, Quot.sound]` — **S2-FREE, NO
> `monomial_rlct`**).
>
> - **Lean (`RouteM121Smeared.lean`):** `∫⁻_{cubeBox 4 ε} |routeMCore M121|^{−c'} = ⊤` for `c' ≥
>   ½·minAdm M121 = ½`, every `ε > 0`. Via `routeMCore_box_diverges_of_MPChart M121 phi121sm
>   measurePreserving_phi121sm measurableEmbedding_phi121sm c' ε hsrc` (route b — the reusable MP-final
>   lemma), with `hsrc = ⟨subBox121 (ε/4), measurableSet_subBox121, subBox121_subset_preimage (4·(ε/4)=ε),
>   subBox121_diverges⟩`.
> - **The hsrc finish (both sub-goals LANDED):**
>   - **Containment** `subBox121_subset_preimage : subBox121 δ ⊆ phi121sm⁻¹(cubeBox 4 (4δ))` — via
>     `phi121sm_entry` (each flat coord = a matrix entry, `rfl` through `Fintype.equivFin (FlatIdx M121)`
>     — the route-(b) sidestep, NO opaque readout) + `chartParams121_entry_bound` (each entry `≤ 4δ` on the
>     bounded-away box; the nontrivial `z−(b/a)·sb ≤ 3δ` since `a ≥ δ/2`).
>   - **Divergence** `subBox121_diverges : ∫_{subBox121 δ} (|loss∘φ|)^{−c'} = ⊤` — the rate `loss∘φ =
>     z²·a²` on `Pδ` (`a > 0`) ⟹ `|z|^{−2c'}·|a|^{−2c'}`; peel the `z`-axis (`piFinSuccAbove`/
>     `setLIntegral_prod`), `z`-factor over `(0,δ)` `⊤` (`abs_rpow_lintegral_Ioo_eq_top`, exp `−2c' ≤ −1`
>     from `c' ≥ ½`), rest positive (`setLIntegral_pos_iff` + `volume_pi_pi`).
> - **Notable: S2-FREE.** Route (b)'s divergence is proven from the 1D `abs_rpow_lintegral_Ioo_eq_top`
>   (the `∫₀ᵟ z^{−2c'} = ⊤` first principle), NOT via the cited `monomial_rlct` S2 atom — so the smeared
>   atom carries NO `monomial_rlct` (stronger than the polynomial charts, which route through it). The
>   geometric content (the rate, the MP chart) is fully self-contained.
> - **Status.** sorry-free + axiom-clean (S2-free). Full `lake build DLNFibre` green with the module
>   temp-imported; aggregator reverted (single-writer — controller integrates the 3-file unit). The
>   reusable `routeMCore_box_diverges_of_MPChart` is banked for the ∀M-smeared lift (the 46 M).
> - **Next:** the ∀M-smeared lift reusing `routeMCore_box_diverges_of_MPChart` — validate a `minAdm ≥ 2`
>   smeared case ((2,3,1)/(1,3,2)) to exercise the radial det `|z|^{minAdm−1}` composed with the shear
>   (here `(1,2,1)` is `minAdm = 1`, no radial blow-up).

---

## ∀M-smeared lift — the radial-MP assembly (minAdm≥2) + the (2,3,1) chart/cancellation

Branch `worktree-agent-a223be0c63e358844` @ `1977e45c`. Toward the 46 boundary-smeared M. The
minAdm=1 chart was MeasurePreserving (weight 1); minAdm≥2 needs the radial blow-up (det |z|^{minAdm−1}).

---

> **`routeMCore_box_diverges_of_RadialMPChart` — the reusable minAdm≥2 assembly, LANDED**
> (`RouteM121Smeared.lean` @ `5fa4d32f`, sorry-free, `[propext, Classical.choice, Quot.sound]`).
>
> - φ = ψ ∘ R: ψ = Q∘shear (measure-preserving + measurable embedding, the rational pole confined to ψ,
>   NEVER differentiated); R the polynomial radial (the ONLY Jacobian carrier: HasFDerivWithinAt/InjOn/
>   |det| = |u_p|^{minAdm−1} on a certified preimage source S). Source certificate `hsrc` is WEIGHTED:
>   ∫_S |u_p|^{minAdm−1}·(loss∘φ)^{−c} = ⊤ (the radial Jacobian absorbed into the binding-axis
>   divergence — exponent minAdm−1−2c ≤ −1 from c ≥ minAdm/2). C-o-v: ψ-preimage
>   (setLIntegral_comp_preimage_emb) + R-image Jacobian (lintegral_image_eq_lintegral_abs_det_fderiv_mul).
> - `routeMCore_box_diverges_of_MPChart` (minAdm=1) is the R=id, h=0 sibling. Codex `radial-mp-assembly`
>   confirmed the factorization + the exponent arithmetic.
> - Validated 46/46 exhaustively (`pp_smear_GATE.py` (D): det Dφ = z^{minAdm−1} across the smeared class).

---

> **(2,3,1) smeared validate-small (minAdm=2) — chart + shear-cancellation LANDED; rate/MP/atom WIP.**
> `RouteM231Smeared.lean` @ `1977e45c` (sorry-free).
>
> - LANDED: M231=(2,3,1) anchor (minAdm=2, flatDim=9); the chart (chartA0/A1_231, chartParams231,
>   phi231sm, lam231 = the rational Λ₀); **P1_lam231** — the load-bearing shear cancellation P₁·Λ₀ = P₂
>   off det P₁ ≠ 0, via (P₁ᵀP₁)⁻¹P₁ᵀ = P₁⁻¹ for an invertible square P₁ (Matrix.mul_inv_rev +
>   nonsing_inv_mul). The 2×2 analog of (1,2,1)'s scalar b/a cancellation — the conceptually-hard piece.
> - RESIDUAL (multi-pass, documented in-file): (1) the rate routeMCore_phi231sm_offpole = z²·U (entry
>   telescoping via P1_lam231 — the opaque-index `i : Fin (M231 0)` vs Fin 2 plumbing, the recurring
>   `lean/CLAUDE.md` have+exact kernel; this fought a pass and is the next chunk); (2) the MP factorization
>   φ=ψ∘R at Fin 9 (R = pivotBlowupOn radial — NEW vs (1,2,1) which had no radial; ψ = Q231∘shear231, the
>   split121/shear121ME pattern at Fin 9); (3) the weighted hsrc (subBox231 bounded away from det P₁ = 0,
>   z-axis divergence at exp 1−2c≤−1); (4) the atom via routeMCore_box_diverges_of_RadialMPChart.
> - Status: the reusable assembly (the ∀M load-bearing piece) + the (2,3,1) chart + the hard cancellation
>   are banked. The mechanical entry-telescoping + the Fin-9 MP-factorization are the bounded fresh-tide
>   finish. Full `lake build DLNFibre` green with both modules temp-imported (8528 jobs).

---

> **(2,3,1) smeared validate-small (minAdm=2) — COMPLETE: rate + MP factorization + atom LANDED.**
> `RouteM231Smeared.lean` (sorry-free; `#print axioms routeM231sm_box_diverges` force-elaborated =
> `[propext, Classical.choice, Quot.sound]`, S2-free — verified after deleting the olean). 1125 LoC.
>
> **Headline theorem** `routeM231sm_box_diverges (c' : ℝ≥0) (hc' : (minAdm M231 : ℝ≥0∞)/2 ≤ c') (ε : ℝ)
> (hε : 0 < ε) : ∫⁻ x in cubeBox (routeMAmbient M231) ε, ENNReal.ofReal (|routeMCore M231 x|^(−(c':ℝ)))
> = ⊤`. The first `minAdm ≥ 2` boundary-SMEARED achiever box-divergence atom, discharged via the banked
> reusable `routeMCore_box_diverges_of_RadialMPChart` (route b).
>
> Pieces (all sorry-free):
> - **Rate** `routeMCore_phi231sm_offpole : routeMCore M231 (phi231sm u) = (u 6)²·Uval231 u` off
>   `det P₁ ≠ 0`, via `dlnLoss_chartParams231_offpole` (entry telescoping `prod_chartParams231_entry`
>   = `z·(a_{i0}+a_{i1}h1)`, the `sb`-shear cancelling through `P1_lam231`).
> - **MP factorization** `phi231sm_eq_psi_R : phi231sm u = psi231 (R231 u)`: `R231 = pivotBlowupOn {6,7} 6`
>   (the radial, sole Jacobian carrier, `D231_abs_det : |det (D231 u)| = |u 6|¹`); `psi231 = Q231∘shear231`
>   measure-preserving (`measurePreserving_psi231`) + measurable embedding (`measurableEmbedding_psi231`).
>   The `shear231` MP (`measurePreserving_shear231`) via the Codex Option-B single 2-core split
>   `split231` + `coreShear_measurable 1 2 6` (the `shear231-mp` consult); the rational `lam231` measurable
>   via the explicit `lam231_explicit` 2×2 `(P₁ᵀP₁)⁻¹P₁ᵀP₂` rational form.
> - **Weighted source** `subBox231_diverges : ∫_{subBox231 δ} |u6|¹·(|loss∘φ|)^{−c'} = ⊤` (`0<δ≤1`,
>   `c'≥1`): on the bounded-away box (`u0,u4∈[δ/2,δ]`, smalls in `[−δ/8,δ/8]`, `z=u6∈(0,δ)`) the rate is
>   `z²·U` (`subBox231_det_ne`, `subBox231_U_pos`), so the integrand is `|u6|^{1−2c'}·U^{−c'}`; the z-axis
>   `∫_{(0,δ)}|u6|^{1−2c'}=⊤` (`abs_rpow_lintegral_Ioo_eq_top`, `1−2c'≤−1`), the rest `U^{−c'}`
>   positive-finite. Containment `subBox231 δ ⊆ phi231sm⁻¹(cubeBox 9 (2δ))` (`chartParams231_entry_bound`,
>   `lam231` bounded `≤9/8` via `subBox231_lam_bound`); atom picks `δ = min(ε/2, 1)`.
> - This realizes the `(2,3,1)` instance of the reusable `RadialMPChart` assembly — the `minAdm≥2`
>   companion to the `(1,2,1)` weight-1 atom. NOT yet wired into `DLNFibre.lean` (single-writer); the
>   controller wires `RouteM231Smeared` when integrating.

---

> **(1,3,2) smeared validate-small — COMPLETE: the `(r,c)=(1,2)` shape's atom LANDED.**
> `RouteM132Smeared.lean` (sorry-free; `#print axioms routeM132sm_box_diverges` force-elaborated =
> `[propext, Classical.choice, Quot.sound]`, S2-free). The genuinely-NEW third smeared shape (scalar
> Gram `r=1` like (1,2,1), `1×2` radial `c=2` `minAdm=2` like (2,3,1)). Completes ALL THREE family
> templates — each smeared (r,c) shape now has a sorry-free validate-small.
>
> **Headline** `routeM132sm_box_diverges (c' : ℝ≥0) (hc' : (minAdm M132 : ℝ≥0∞)/2 ≤ c') (ε > 0) :
> ∫⁻ cubeBox (routeMAmbient M132) ε, ofReal (|routeMCore M132 x|^(−c')) = ⊤`. Via
> `routeMCore_box_diverges_of_RadialMPChart` (route b), `φ = ψ132 ∘ R132`: `R132 = pivotBlowupOn {3,4} 3`
> (radial, `|det|=|u3|¹`); `ψ132 = Q132∘shear132` MP + measurable embedding (the SCALAR shear, `lam132 =
> [u1/u0, u2/u0]` — no matrix inverse; MP via `split132` 2-core {3,4} + `coreShear_measurable 1 2 6`);
> rate `routeMCore_phi132sm_offpole = (u3)²·U`, `U = u0²·(u4²+1)`; weighted source `subBox132 δ` bounded
> away from `{u0=0}`. NOT wired (single-writer DLNFibre.lean) — controller wires `RouteM132Smeared`.
>
> The three family templates are now all banked sorry-free: (1,1)→RouteM121Smeared (minAdm=1, MPChart);
> (2,1)→RouteM231Smeared (minAdm=2, 2×2 Gram, RadialMPChart); (1,2)→RouteM132Smeared (minAdm=2, scalar
> Gram + multi-col radial, RadialMPChart). Next: the family-parametric ∀M lift (each template → ∀ M in
> its (r,c) family, dispatch by shape).

---

> **Claim (the ∀M-(1,1)-smeared front fact).** In the `(1,1)`-smeared regime the front product
> `P = prodAux M A (L−1)` factors through a width-1 inner layer at the first width-1 position `p*`, so
> off the pole `‖col 0‖² ≠ 0` every column of `P` is a scalar multiple of column 0; consequently the
> scalar-Gram shear cancels, `P₁ · (P₁ᵀP₁)⁻¹P₁ᵀP₂ = P₂`, for the pivot column `P₁` and any residual
> block `P₂` selecting columns of `P`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.rankOneColumns_of_factorsThroughOne` (§3a),
>   `prodAux_split_exists` + `prodAux_factorsThroughOne` (§3b),
>   `frontScalarShear_cancel_of_factorsThroughOne` + `prodAux_frontScalarShear_cancel` (§3c)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMFrontBottleneck.lean` @ `cdf345ef`)
> - **Gloss.**
>   - §3a: for `P = U·V` with `U : rows × Fin 1`, `V : Fin 1 × Fin m1`, off `∑ᵢ(P i 0)² ≠ 0`, there
>     exist `c₀ = P.col 0` and `μ` with `μ 0 = 1` and `∀ i j, P i j = μ j · c₀ i`. Mechanism: the
>     literal outer product `(U·V) i j = U i 0 · V 0 j`; `V 0 0 ≠ 0` extracted from the off-pole sum.
>   - §3b: `prodAux_split_exists` — for `p ≤ k`, `prodAux M A k = prodAux M A p * Y` for some `Y`
>     (existential right-factor split, `Nat.le_induction` on `k`, `prodAux_succ` + `mul_three_reassoc`).
>     `prodAux_factorsThroughOne` — with `M ⟨p,_⟩ = 1`, `prodAux M A k = U·V`, `U : Fin(M 0) × Fin 1`,
>     `V : Fin 1 × Fin(M⟨k,_⟩)` (collapse the middle width to `Fin 1` via `finCongr` at the equiv level).
>   - §3c: §3a ∘ §3b ∘ landed `scalarGram_cancel_of_rankOneColumns` ⟹ `P₁·Λ₀ = P₂`.
> - **Proved.** All five results sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`
>   (forced `#print axioms` via `lake env lean`, S2-free — no analysis axioms). The factorization is
>   unconditional; the column-normalization (and the cancellation) hold off the pole `‖col 0‖² ≠ 0`.
> - **Assumed.** `0 < m1` / `0 < M⟨k,_⟩` (the column index `⟨0,_⟩` is well-typed); `p ≤ k`,
>   `M ⟨p,_⟩ = 1` (the width-1 bottleneck position); `hc : ‖col 0‖² ≠ 0` (off-pole). These are exactly
>   the hypotheses the consumer `scalarGram_cancel_of_rankOneColumns` and the chart supply.
> - **Cited.** `scalarGram_cancel_of_rankOneColumns` (LANDED, `RouteMSmearedGenRate.lean`); the
>   `RouteMFrontPeel` cast kernel (`prodAux_succ`, `mul_three_reassoc`, `reindex_finCongr_mul`,
>   `finCongr_refl`/`reindex_refl_refl`); `Matrix.mul_apply`, `Fin.sum_univ_one`, `div_self` (Mathlib v4.29).
> - **Deferred.** The (1,1)-family Option-A CHART (STEP 4 of the dispatch): the generic flat scalar-shear
>   + its MP (`measurePreserving_shearAt` to arbitrary `p`), the generic rate `routeMCore(sheared)=u_p²·U`,
>   the subBox/containment/`routeMCore_box_diverges_of_MPChart` assembly. This front fact is the chart's
>   load-bearing input (the architecture cert's flagged "biggest risk"), now in hand; the chart consumes it.
> - **Structure & ideas observed (p&p certificate, `certificate-frontbottleneck-rankone.md`).** The
>   mechanism is a LITERAL `Fin 1` outer product, NOT rank theory; `p*` is never `L−1` (the right factor
>   `V` always has ≥1 genuine layer); the off-pole hypothesis is load-bearing (Codex `[0 1]` counterexample
>   — columns are multiples of the HIDDEN `U`, not of `P.col 0`, without `V 0 0 ≠ 0`). (1,2) reuses this
>   scalar bridge verbatim; (2,1) needs a `Fin 2` / 2×2-Gram analogue (§3a generalizes by `Fin 1 → Fin r`).
> - **Route (formaliser).** Reformulated §3b as an EXISTENTIAL right-factor split (no canonical suffix
>   product, no entry formula, no shifted-chain reindex) — decorrelated Codex independently recommended
>   the same route (`codex/frontprod-split-answer.md`). The `U·V` form is stated directly (no outer
>   reindex), so it feeds §3a/§3c without a wrapping cast.
> - **Status.** sorry-free (fidelity review pending).

> The R1-LOWER smeared branch's front fact (the architecture cert §3 residual-1 + the dispatch STEPs 1-3)
> is banked. STEP 4 (the (1,1) Option-A chart) remains; its load-bearing dependency is now landed.

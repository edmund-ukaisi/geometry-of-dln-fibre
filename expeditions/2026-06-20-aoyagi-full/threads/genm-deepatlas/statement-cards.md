# Statement cards — `genm-deepatlas` Tide A (deep stratified-resolution atlas, geometric charts)

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeepAtlas.lean`
Branch: `genm-deepatlas` (base `12a7ae38a` = `origin/genm-sj5-capstone`; SHA pinned at integration).
Namespace: `DLNFibre.DLN.RLCT.DeepAtlas`. Standalone (NOT aggregator-wired — controller integrates).
Axioms (all 8 results, force-fresh `#print axioms`): `[propext, Classical.choice, Quot.sound]`. Zero sorry.

Spec: `genm-deepatlas-design/design.md` §2 (charts), §2.1 (per-level big-cell), §2.2 (product-layer
reduction). **Scope: Tide A geometric charts only** — rank stratification `{E = 0}` + measure CoV,
**independent of the loss**; the `F·E` seam (design §4) is a Tide-D loss-monomialisation phenomenon and
enters **no** theorem here.

---

## Deliverable 1 — per-level block-Schur big-cell (re-export; design §2.1)

> **Claim.** At a recursion level with effective last layer `M = [[Δ,U],[V,W]]`, invertible top-left
> size-`r` pivot `Δ`, transverse Schur coordinate `E := W − VΔ⁻¹U`: (a) the `W₂₂ ↦ E` translation is
> Jacobian ≡ 1; (b) `rank M = r + rank E`; (c) `{rank M ≤ r} = {E = 0}` in CoV coordinates.
>
> - **Lean:** `deepLevel_bigcell_cov`, `deepLevel_rank_eq`, `deepLevel_rank_le_iff`.
> - **Gloss.** (a) `∫⁻ (abc,E), f(abc, E + chart5Shift abc) = ∫⁻ f` (block-`W` translation preserves the
>   raw-pi lintegral). (b) `(fromBlocks Δ U V W).rank = r + (W − V Δ⁻¹ U).rank`, for `IsUnit Δ.det`.
>   (c) `(fromBlocks Δ U V (E + chart5Shift (Δ,U,V))).rank ≤ r ↔ E = 0`, for `IsUnit Δ.det`.
> - **Proved.** All three, unconditionally (each `:=` the front chart-5 fact, over `ℝ`).
> - **Assumed.** `IsUnit Δ.det` (pivot invertible), as the claim needs.
> - **Cited.** `chart5_bigcell_cov`, `chart5_rank_eq`, `chart5_rank_le_iff_reassembled`
>   (`RouteMSJIncidenceChart5BigCell`), `Core.SchurChartIff` — banked, sorry-free.
> - **Deferred.** The general `(I,J)` pivot permutation (Jacobian `±1`) — top-left normal form only;
>   the reindexing is Tide B (design §3.1). No new math (re-export, by design).
> - **Status.** sorry-free.

## Deliverable 2 — the product-layer reduction (new; design §2.2)

> **Claim (skeleton).** On the rank-drop stratum `{E=0}` the effective last layer factors through its
> pivot minor: `[[Δ,U],[V,VΔ⁻¹U]] = A·Δ⁻¹·D`, `A = [[Δ],[V]]` (pivot columns), `D = [Δ|U]` (pivot rows).
>
> - **Lean:** `deepReduce_skeleton`
>   `(fromBlocks Δ U V (V*Δ⁻¹*U) : Matrix (Fin r ⊕ Fin nr) (Fin r ⊕ Fin dc) ℝ) = fromRows Δ V * Δ⁻¹ * fromCols Δ U`.
> - **Gloss.** The rank-`r` block matrix with Schur complement `0` equals (pivot columns)·(pivot
>   minor)⁻¹·(pivot rows) — the CUR/skeleton decomposition. **Proved**, `IsUnit Δ.det`.

> **Claim (unit Jacobian).** The completion `G₀ = [[I,0],[VΔ⁻¹,I]]` is unitriangular, `det G₀ = 1`, so
> the reduction change of variables `L ↦ L·G₀` preserves Lebesgue measure.
>
> - **Lean:** `deepReduce_G0_det_eq_one` `(fromBlocks 1 0 S 1).det = 1` (any coupling block `S`); and
>   `deepReduce_cov` `∫⁻ L, g (fun i ↦ L i ᵥ* G) = ∫⁻ L, g L` for any `|det G| = 1`.
> - **Gloss.** `det` of the lower-unitriangular completion is `1`; right-multiplication of the free layer
>   by any unit-`|det|` matrix leaves the raw-pi lintegral unchanged (the product-layer reduction CoV is
>   the instance `G = G₀`). **Proved** unconditionally.
> - **Cited.** `RouteMSJGammaAtom.lintegral_comp_rightMulₚ` (banked raw-pi Haar CoV, diamond-dodge);
>   `Matrix.det_fromBlocks_zero₁₂`.

> **Claim (rank identity).** On `{E=0}`, for any preceding head `X`, `rank(X·M) = rank(X·A·Δ⁻¹)` — the
> reduced free last layer `H = X·A·Δ⁻¹` carries the composed rank; the pivot rows `[Δ|U]` drop out.
> (`X = B·L` gives the design's `rank(B·L·M) = rank(B·H)`.)
>
> - **Lean:** `deepReduce_rank`
>   `(X * fromBlocks Δ U V (V*Δ⁻¹*U)).rank = (X * fromRows Δ V * Δ⁻¹).rank`, `IsUnit Δ.det`.
> - **Gloss.** Composed rank through the effective last layer = composed rank through the reduced free
>   layer. Via skeleton + `rank_mul_eq_of_mul_eq_one` (the pivot rows `D = [Δ|U]` have right inverse
>   `[[Δ⁻¹],[0]]`, so `rank(P·D) = rank P`). **Proved**, `IsUnit Δ.det`.
> - **Helper:** `rank_mul_eq_of_mul_eq_one` — `D·D' = 1 ⟹ rank(X·D) = rank X` (arbitrary Fintype index).
> - **Deferred.** The full reduction identity `L·M = (HΔ, HU+FE)` (descriptive, exhibits the `F·E` seam)
>   is Tide-D territory and deliberately absent here (loss-independence guard). Per-stratum
>   `rlct = C_k/2` is Tide D (OPEN, design §4).
> - **Status.** sorry-free.

---

**Numerical pre-check (before formalising):** 2000 random trials (`r,nr,dc,m,bh = 2,3,2,4,3`) —
skeleton, `det G₀ = 1`, `rank(B·L·M)=rank(B·H)`, and `L·M=(HΔ,HU+FE)` all pass exactly.

---

# Statement cards — `genm-deepatlas` Tide B (deep atlas: bridge, index, coverage, gluing)

Modules: `RouteMSJDeepCover.lean`, `RouteMSJDeepPivot.lean`, `RouteMSJDeepChainPeel.lean`,
`RouteMSJDeepIndex.lean`, `RouteMSJDeepCoverage.lean`. Branch `genm-deepatlas` @ `b458bb430`.
Namespace `DLNFibre.DLN.RLCT.DeepAtlas`. Standalone (NOT aggregator-wired). All sorry-free; force-fresh
`#print axioms` = `[propext, Classical.choice, Quot.sound]`. Design: `gluing-shape` + `atlas-structure`
Codex passes (artifacts in `codex/`).

> **Claim (leaf, §3.2 base).** The exact-rank stratum of a single matrix is the union of size-`r`
> pivot charts cut to `{rank ≤ r}` — non-vacuous (`r=0` cell = `{M=0}`).
> - **Lean:** `rankEqLocus_eq_iUnion_pivot_inter (r) : {M | M.rank = r} = ⋃ ρ κ, (pivotChart ρ κ ∩ {M | M.rank ≤ r})`.
> - **Proved.** Reuse of banked `pivotLocus_eq_iUnion`. **Status.** sorry-free.

> **Claim (bridge).** General-pivot CUR + rank reduction (lift of tide-A's top-left `deepReduce_rank`).
> - **Lean:** `generalPivot_CUR (M)(ρ κ : Fin M.rank ↪ ·)(hU) : M = M.submatrix id κ * (M.submatrix ρ κ)⁻¹ * M.submatrix ρ id`;
>   `generalPivot_reduce_rank (X)(M)(ρ κ)(hU) : (X*M).rank = (X * M.submatrix id κ * (M.submatrix ρ κ)⁻¹).rank`;
>   `generalPivot_reduce_rank_of (…)(r)(hr : M.rank = r)(ρ κ : Fin r ↪ ·)(hU)` — explicit-rank variant (subst).
> - **Proved.** Via banked rank factorization `exists_rank_factorization_gen` + `mul_inv_rev` cancellation;
>   `mul_submatrix_one` column-selection for the two `rank_mul_le_left` bounds. **Status.** sorry-free.

> **Claim (chain descent, loss-independent concrete↔abstract bridge).** The composite-rank recursion on
> the actual DLN chain: `rank(prodAux (k+1) · Q) = rank(prodAux k · Q')`, `Q'` the reduced factor.
> - **Lean:** `effLayer`, `prodAux_succ_mul`, `prodAux_reduce_rank` / `prodAux_reduce_rank_of`.
> - **Proved.** `prodAux_succ` peel + `mul_assoc` + the general-pivot bridge. **Status.** sorry-free.

> **Claim (index §3.1).** The finite CR-tree path index.
> - **Lean:** `CRPath` (dependent `Σ`-tree, terminal `Unit`), `instFintypeCRPath`, `CRIndex`.
> - **Proved.** Structural `Fintype` (noncomputable via `Function.Embedding.fintype`). **Status.** sorry-free.

> **Claim (coverage §3.2 + gluing §3.3).** The deep charts EXHAUST `{rank Z_deep ≤ s}` (invariant-free,
> non-vacuous), and the finite (subadditive) cover gluing gives finiteness from per-cell finiteness (a
> tide-D hyp). The cover need NOT be disjoint — the bound is subadditivity of `∫⁻` over a finite cover
> (`∫⁻_D f ≤ ∑ᵢ ∫⁻_{Cᵢ} f`); no null-overlap is claimed or used (cells share positive-measure overlap).
> - **Lean:** `deepCell` (recursive cell, terminal `{A | (Q A).rank ≤ s}`);
>   `deepCover_aux : ∀ j hj q Q, {A | (prodAux j · Q A).rank ≤ s} = ⋃ path, deepCell … path Q` (chain-length induction, any `Q`);
>   `deepRankLE_eq_iUnion_cells : {A | (prod H A).rank ≤ s} = ⋃ i : CRIndex H, deepCell … i (fun _ ↦ 1)`;
>   `deepRankLE_lintegral_lt_top (f)(hfin : ∀ i, ∫⁻_(deepCell … i) f < ⊤) : ∫⁻_{rank ≤ s} f < ⊤`.
> - **Proved.** Coverage by leaf + `prodAux_reduce_rank_of` descent + IH; gluing = one application of banked
>   `lintegral_lt_top_of_finite_cover`.
> - **Assumed.** In the gluing wrapper, per-cell finiteness `hfin` — a **TIDE-D hypothesis** (the loss tide
>   discharges it, carrying `|det J|`); `f` is a GENERIC `ℝ≥0∞` integrand (loss-independent).
> - **Deferred.** Per-cell finiteness (`rlct = C_k/2`) = tide D (seamrlct native route). Measurability of the
>   cells defers to tide D (the banked gluing lemma needs none). The `ℝ/ℂ` codim bridge for (α) is a separate lane.
> - **Structure observed.** Codex's locked `Q.rank = q` coverage invariant does NOT survive the descent
>   (the reduced `Q'` has rank `r` only on the pivot cell); the fix — terminal-constraint cell + `Unit`
>   terminal path (invariant-free) — was caught by build-verification before it became a false proof.
> - **Status.** sorry-free, clean-three; fidelity review requested.

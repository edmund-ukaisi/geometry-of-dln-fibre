# Statement card — the ∀M-L2 interior-det headline, HONEST free-K engine (RouteMLeafFreeKHeadline)

> **Claim.** For the REAL ∀M-L2 `genBlkFlatLive` + leaf-pivot achiever chart `phiFlatLiveAt M ha hL p₀`,
> the chart Jacobian abs-det is
> `|det Dφ| = |u p₀|^(minAdm M − 1) · ∏_{s:Fin 2} engineFreeK_s`
> with `engineFreeK` the EXPLICIT honest free-K Schur value (`|det K|^(r+c)` at the interior boundary,
> `1` at the leaf), GIVEN the single boundary-factor determinant
> `hDtot : |det (Dtot ha (pbo u))| = |det K|^(r+c)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorDet_leaf_headline_freeK`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLeafFreeKHeadline.lean` @ `294a52bc`).
> - **Status:** `sorry-free`, axiom-clean `[propext, Classical.choice, Quot.sound]` (forced
>   `#print axioms`). Reviewed (fidelity SURVIVED, decorrelated-Codex-corroborated, this session).
>   Carries ONE open hypothesis `hDtot` (the staircase det — a named wall, below).
>
> - **Gloss.** The boundary factor `BchartLeaf ha y = paramsEquivFlat M (chartParamsGen 1 …
>   (genBlkFlatLive … (rfinDirect ha y) y))` reads the residual coords (including the Schur core `K`)
>   DIRECTLY as ordinary `y`-values. So its Jacobian determinant is the **free-K Schur** value
>   `|det K|^(r+c)` (`r = Text 1 − Text 2`, `c = Wext 1 − Text 2`, `K = readK ⟨0⟩` at the blown-up
>   point). The chart Jacobian splits as the radial monomial `|u p₀|^(minAdm−1)` (the blow-up) times
>   this boundary-factor det.
>
> - **FIDELITY CORRECTION (vs the brief's Schur·LDU).** The brief asked for the engine
>   `|det K|^(r+c)·∏ᵢ|qᵢ|^{2(t−1−i)}` (Schur·LDU). For the EXISTING `BchartLeaf` this is FALSE — the
>   chart reads `K` via `readK` free (it does NOT pre-apply the `kLDU` lens, `RouteMKLens`), so the LDU
>   multiplier is absent. The precise false identity is `readK y = kLens (readK y)`. The honest engine
>   is the free-K one. (Numeric validate-(3,3,4): `det (fderiv BparamsLeaf) = (det K)^4` exactly;
>   second case t=2 M=(4,4,5): `(det K)^4` again. At t=1 free-K and Schur·LDU coincide vacuously, since
>   the LDU exponents `2(t−1−i)` vanish; they differ for t≥2. Decorrelated Codex corroborated.)
>
> - **Proved (this session, all sorry-free + axiom-clean):**
>   - `engineFreeK` / `engineFreeK_prod` (`RouteMLeafEngine.lean`) — the honest engine + its product
>     collapse. `engineFreeK` is a closed-form `readK`-based value; NOT `Dtot`/`fderiv`-based (no
>     circularity — verified by the reviewer that the `def` bodies contain no derivative).
>   - `Bchart_abs_det_eq_Dtot` (`RouteMLeafReduce.lean`) — `|det (fderiv BchartLeaf y₀)| = |det (Dtot
>     y₀)|`, stripping the measure-preserving `paramsEquivFlat` reindex (`Dtot = paramsEquivFlatCLE ∘L
>     (fderiv BparamsLeaf)`). Via `HasFDerivAt.unique` + `rfl` (NOT `.fderiv`, which trips the
>     opaque-width `ContinuousAdd` synthesis — a recurring `lean/CLAUDE.md` gotcha).
>   - `interiorDet_leaf_headline_freeK` — the headline, modulo `hDtot`. Strictly SHARPER than the
>     capstone's `hdet`: the opaque `|det DB|` is replaced by the explicit `|det K|^(r+c)`, and the
>     `paramsEquivFlat` reindex is discharged.
>
> - **Open (the named WALL).** `hDtot : |det (Dtot ha (pbo u))| = |det K|^(r+c)`. The staircase
>   determinant of the boundary-factor Jacobian: `Dtot` regrouped into V0 = {Schur frame inputs
>   K,X,N₁,E} and V1 = {lift W₁, leaf} is a 2-block staircase (`stairMap V 2`) with `f 0 =
>   schurFrameDeriv` (det `|det K|^(r+c)`, banked) and `f 1 = chainUnit` (det 1, banked), the shared
>   N₁-coupling strictly head→tail (det-invisible). Discharges via
>   `RouteMStairTwoSided.stairMap_abs_det_twoConj` once the two layer-collecting equivs `eIn/eOut :
>   (Fin N → ℝ) ≃ StairProd V 2` are built + the entry match proven over the opaque `Fin (Text/Wext)`
>   widths. This is the SAME wall as `RouteMInteriorDetReal.interiorDet_phiFlatLiveR1_of_stairConj`'s
>   `hconj` — the cast-heavy multi-tide staircase decomposition (the `frameB` ∀M generalization, done
>   by hand at (3,3,3,3), never for ∀M). `RouteMGradingObstruction` proves the simpler single-grading
>   square `Matrix.BlockTriangular` route is mathematically blocked.
>
> - **Cited / Assumed.** None beyond the hypothesis `hDtot`. The headline is the chart-Jacobian level
>   ONLY — it does NOT give `rlct = ½·codim` (needs the cited Aoyagi equality).

# Statement card — interior-det HEADLINE (b-3 assembly), `genm-detcomp`

> **Claim (interior-det headline, the b-3 assembly).** The interior achiever-chart Jacobian
> determinant, taken off the fused frame `DFrame` that is block-triangular under the layer grading,
> factorizes uniformly in the width tuple `M`:
> `|det DFrame| = |u_p|^{minAdm−1} · ∏_s ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )`,
> with the per-grade diagonal-block determinants identified as the radial value `|u_p|^{minAdm−1}` and
> the per-boundary Schur×LDU engine value `|det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorDet_headline_of_blockTri`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDetHeadline.lean` @ `<pending — based off genm-routeb 3bfa029e>`)
>   Supporting in the same file: `blockTri_abs_det`, `blockTri_headline_regroup`,
>   `det_toSquareBlock_singleton`, `hB_eq_engine`.
> - **Gloss.** For a square real matrix `DFrame : Matrix (Fin N) (Fin N) ℝ`, a grading
>   `g : Fin N → ℕ` with `DFrame.BlockTriangular g`, whose grading image is exactly
>   `{0} ∪ {s+1 : s : Fin L}` (radial grade 0 + one grade per boundary), and per-grade block-det
>   identifications `|（toSquareBlock g 0).det| = |u_p|^{minAdm M − 1}` and
>   `|（toSquareBlock g (s+1)).det| = |Kdet s|^{rc s} · ∏_{i:Fin (t s)} |q s i|^{2(t s − 1 − i)}`,
>   the determinant equals `|u_p|^{minAdm M − 1} · ∏_{s:Fin L} (|Kdet s|^{rc s} · ∏_i |q s i|^{2(t s −1−i)})`.
> - **Proved (unconditional, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):**
>   - `blockTri_abs_det`: `|DFrame.det| = ∏_{a ∈ image g} |（toSquareBlock g a).det|` — the abs form of
>     `Matrix.BlockTriangular.det` (the off-diagonal det-1 shear coupling discarded).
>   - `blockTri_headline_regroup` + `interiorDet_headline_of_blockTri`: the **regrouping** of the
>     per-grade block-det product into the per-boundary headline form (split the radial grade-0 factor;
>     reindex boundary grades `s+1 ↦ s` injectively). This is the genuinely-new combinatorial content.
>   - `det_toSquareBlock_singleton`: a per-layer diagonal block hit by one coordinate has det = its
>     diagonal entry (the b-2/b-3 per-block read for single-coordinate layers).
>   - `hB_eq_engine`: the per-boundary RHS `|K.det|^{r+c} · ∏_i |q_i|^{2(t−1−i)}` IS exactly
>     `|det (schurFrameDeriv X K N)| · |det (lduCoreDeriv l q u)|` (`schurFrame_abs_det` ×
>     `lduCoreDeriv_abs_det`) — confirms `hB` is discharged by the banked engine, not assumed away.
>   - In-file non-vacuity, TWO witnesses: (i) a concrete `L=1` diagonal frame `diag ![up,k]` (`t=0`
>     boundary, exercises `|K|^{rc}`); (ii) `diag ![up, q0², m]` (`t=2` boundary, exercises the LDU
>     pivot `q0` at exponent `2` END-TO-END via `e2blkWitness` + `det_fin_two`). Together they fire both
>     halves (`|K|^{rc}` and the `q`-product) of the per-boundary value through the full assembly.
> - **Assumed (the fenced, separately-gated Frame_M obligations — hypotheses of the headline):**
>   - `hbt : DFrame.BlockTriangular g` — the b-0 off-block-vanishing transported to the fused frame
>     `DFrame_M`. The reader-level / decoder-block off-block-vanishing is BANKED
>     (`Agen_genBlkFlatStruct_reads_le`, `RouteMLayerGrade`); transporting it to `DFrame_M` needs the
>     `DFrame_M` construction (the long pole, below).
>   - `hR`, `hB` — the per-grade block-det identifications (radial = `radial_abs_det_minAdm`;
>     boundary = `schurFrame_abs_det` × `lduCoreDeriv_abs_det`). Each is a banked engine lemma, applied
>     through the per-layer diagonal block of `DFrame_M`.
>   - `himg` — the grading image is `{0} ∪ {s+1}` (the radial-+-per-boundary layout of `bLayer`).
> - **Cited.** none (pure determinant + finite-product algebra; the analytic `rlct=½·codim` is downstream).
> - **Deferred (NOT done here — the long pole, named):** the construction of the fused frame
>   `Frame_M`/`DFrame_M` over opaque `Fin (Wext M k)` widths + `HasFDerivAt` (b-1 toSquareBlock reindex
>   via `card_equiv`; b-2 per-layer diagonal det). The headline consumes `DFrame` + `hbt`/`hR`/`hB`/`himg`
>   abstractly; discharging them on the real chart is the remaining multi-tide b-1/b-2 work. The route is
>   the NON-refuted `BlockTriangular.det` direct-on-`DFrame` route (NOT the Codex-refuted
>   `composeFold fs = φ` prefix-threading, genm-mapeq @d7e75c8d).
> - **Numerical validation (UP-FRONT, sympy exact).** The headline factorization + the spec-gate caveat
>   were #eval-validated across 5 width tuples (`run_*.py`): (3,3,3,3), (2,3,2), (2,2,2,2), (3,3,3)
>   [t=3 K-core], (3,2,2,2,2) [L=4 descent]. All confirm: chart SQUARE (coords==flatDim); identity
>   boundary has 0 free coords (no free B_0/R_0/N_0); kept rows pivot-carrying `X·diag(q)·U` (the
>   `|det K_s|^{r_s}` factor present — verified by the per-piece det reproducing the global det exactly);
>   nearest-neighbor shear dets all 1; per-piece product = global det. The gauge caveat is NOT an
>   obstruction.
> - **Route (controller-synthesized, det_comp / block-triangular, verdict-green-lit).** Take the det of
>   the fused composition directly via chain rule + `Matrix.BlockTriangular.det` on `DFrame` (the b-0→b-3
>   ladder); the C(k+1) nearest-neighbor coupling lands strictly off-diagonal (det-1 shear), discarded by
>   `BlockTriangular.det = ∏ diagonal-block dets`. This card banks b-3 (the assembly) abstractly over the
>   grading.
> - **Status.** sorry-free, axiom-clean (forced `#print axioms` after olean delete: clean-three) — awaiting
>   reviewer fidelity check.

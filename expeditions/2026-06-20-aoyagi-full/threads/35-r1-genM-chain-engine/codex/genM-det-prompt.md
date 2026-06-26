# Lean 4 / Mathlib v4.29: the general-M Jacobian determinant for a DLN achiever chart — reachable or design-wall?

## Setting
I've banked (sorry-free) the ∀M chart RATE identity `routeMCore M (φ_{M,t} u) = u²·V` for arbitrary
`M : Fin (L+1) → ℕ` and weakly-decreasing descent `t`, via a matrix-product telescope (`chainOfMt`). The
chart is `φ_{M,t} := paramsEquivFlat M ∘ chartParamsGen`, where `chartParamsGen : Params M` has layers
`A k = chainA (N_k)(W_k)(C(k+1))` (block-assembled via `chainQ`/`chainA` reindexes on `Fin (M k)`).

I now need the JACOBIAN DETERMINANT field for the `NodeAchieverChart M` bundle:
`|det Dφ_{M,t}(u)| = ∏_j |u_j|^{leafH j}` where `leafH p = minAdm M − 1` on the radial pivot `p` and the
spectator monomial on the LDU-pivot axes. This feeds the box-divergence atom
`routeMCore_box_diverges_achiever ∀M`.

## What the (3,3,3,3) CONCRETE instance does (the template)
`phi3333 = Q3333 ∘ T3333`, `T3333 = Frame3333 ∘ Kparam3333` — all THREE are hand-transcribed
flat-coordinate maps `(Fin 27 → ℝ) → (Fin 27 → ℝ)`:
- `Q3333` = the measure-preserving coordinate reshape (`|det| = 1`, via measure-preservation).
- `Kparam3333` = the LDU-core parametrization (lower-triangular fderiv, `det = (x 1)²`).
- `Frame3333` = the bilinear frame map. Its fderiv `Frame3333Deriv` is BLOCK-TRIANGULAR over a
  HAND-COMPUTED SCC-grading `frameB : Fin 27 → ℕ` (a literal `![9,9,9,11,12,...]`), with per-block dets:
  five `z 0`-blocks, a `z 9³`-block, a 7×7 "K/Kᵀ coupling block" (det `(z1·z4−z2·z3)²`, proven by a
  column-permutation to block-lower-triangular `fromBlocks K7tl 0 K7bl K7br`), and singletons.
  `Frame3333Deriv_det = z0⁵·z9³·(z1·z4−z2·z3)²`. Then `det Dφ = 1·(that)·(x1²) = u0⁵·u1⁴·u4²·u9³`.
The cov field ALSO needs `phi3333_injOn` — a HAND-CODED 27-coordinate triangular recovery (each coord
solved from the matrix entries by divisions / 2×2 systems of det `u1·u4`).

## The banked GENERAL det telescope (what I'm "supposed" to use)
`general_composed_clm_abs_det (N) (fs : List CLM) (m) (hfac) : |det (fs.prod)| = m.prod` — i.e. if I
present `Dφ_{M,t}` as a `List.prod` of full-ambient CLMs with per-factor abs-dets `m`, the telescope is free.

## MY ASSESSMENT (want you to confirm or refute)
To use `general_composed_clm_abs_det`, I must RE-EXPRESS `φ_{M,t}` as a `List.prod` of full-ambient frame
factors (a general `Frame ∘ Kparam ∘ ...` decomposition) AND prove each factor's det via a general
block-triangular grading. But:
1. The flat-coordinate frame maps (`Frame3333`/`Kparam3333`) are HAND-TRANSCRIBED per instance — there is
   no general `Frame_{M,t}` flat map; `chartParamsGen` is built from the abstract `chainA`/`chainQ`
   reindexes, NOT a flat-coordinate frame product.
2. The SCC-grading `frameB`, the K/Kᵀ coupling block, the block sizes — all depend on `M` and `t`
   (number of pivots = #{s : t_s − t_{s+1} > 0}, coupling-block size = function of the t_s). No mechanical
   lift from the (3,3,3,3) `frameB`.
3. The `injOn` triangular recovery is hand-coded per coordinate (27 `have`s for (3,3,3,3)).

So my read: the general det is **NOT a mechanical lift** from the (3,3,3,3) template — it needs (a) a
general flat-coordinate frame decomposition of `φ_{M,t}`, (b) a general block-triangular det grading, (c) a
general triangular injectivity. Each is a substantial DESIGN problem. The rate identity (banked) is
M-agnostic; the DET is not, with the current per-instance frame approach.

## QUESTIONS
1. Is my assessment right that the general det is a design-wall with the per-instance flat-frame approach?
2. Is there a CLEANER route to `|det Dφ_{M,t}| = ∏|u_j|^{leafH j}` that AVOIDS the flat-frame
   decomposition — e.g.:
   (a) Compute `det Dφ` DIRECTLY from the `chainOfMt` structure (the layers are `chainA` of block data;
       is `det` of the assembled `Params M → flat` map computable from the per-boundary block dets via a
       general `BlockTriangular`/`det_comp` argument on the ABSTRACT `chainA`/`chainQ`, without
       transcribing flat maps)?
   (b) A general "frame ∘ LDU ∘ radial" decomposition stated ABSTRACTLY (CLMs parametrized by `M`,`t`,
       block data) with a general per-factor det — i.e. lift `Frame`/`Kparam` to take the block widths as
       parameters, with the SCC-grading replaced by a uniform `fromBlocks`/`BlockTriangular` argument over
       `Fin t_s ⊕ Fin c_s`?
   (c) Some other structural identity (e.g. the det of a bilinear frame `A = P K Q + u E` is computable in
       closed form `|det K|^{r+c}` per the cert — can THAT be the per-factor det, proven once
       block-abstractly, avoiding the per-coordinate `frameB`)?
3. If (b)/(c) is the route: what is the cleanest Lean shape for the general per-factor frame det
   `|det (Schur-frame fderiv)| = ∏|q_{s,i}|^{...}`, and is it a bounded build or a multi-week design?
4. Given the box-divergence atom is the headline gate, is it WISER to (i) push the general det now, or
   (ii) deliver the atom for the THREE banked anchors (3,3,4)/(4,4,2,2)/(3,3,3,3) via the existing
   per-instance dets and report the general det as the precise residual design problem?

Be skeptical and concrete. If the general det is genuinely a multi-week design pass (not a bounded build
on the banked machinery), say so plainly and identify the ONE sub-piece that is the bottleneck.

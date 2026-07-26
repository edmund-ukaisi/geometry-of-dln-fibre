# Statement card — born-native (3,3,4) σ_p fan + `hcover` (the (A) seat)

> **Claim (fan def).** The born-native (3,3,4) resolution fan has shape (b): a 3-node tree whose
> node 1 applies, per pivot `p ∈ {0,1,2,3,4,5,6,7,20}`, the DIRECT native block shear `σ_p` of
> `assembly-extraction.md` §2 (each a rank-≤2 quadratic block shear on the residual block), and whose
> nodes 2, 3 keep the fixed inner block blow-ups `bbA0` (center `{0..7}`) / `bbA1` (center
> `{1,5,6,7}`). Its `9·8·4 = 288` pivot-path leaf composites form one flat family `gFin`.
>
> - **Lean (shears):** `DLNFibre.DLN.Aoyagi.NativeShear334.nativeSel` + `covers_P·` / `jacDet_P·` /
>   `injective_P·` / `nativeSel_covers` / `nativeSel_jacDet` / `nativeSel_differentiable`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2NativeShear334.lean` @ `c82688e40`)
> - **Lean (fan + family):** `DLNFibre.DLN.Aoyagi.NativeFan334.nativeFan` / `gFlat` / `gFin` /
>   `domFin` / `numCharts` (`lean/DLNFibre/DLN/Aoyagi/Corank2NativeFan334.lean` @ `c82688e40`)
> - **Gloss.** `nativeSel p` is `blockShear (qdisp t1P· t2P·)` — the coordinate change `u ↦ u + φ_p u`
>   where `φ_p` is the sum of the ≤2 signed products `±u_a·u_b` given verbatim in §2 (encoded as
>   `t1P·`/`t2P·`, `Bool` sign + source pair). `nativeSel 20` is the landed `shearPhiH` (`dom(0,0)`).
>   `gFin c` is the composite `(blockBlowupMap {0..7,20} p1 ∘ nativeSel p1) ∘ blockBlowupMap {0..7} p2
>   ∘ blockBlowupMap {1,5,6,7} p3` of the leaf `c = (p1,p2,p3)`.
> - **Proved.** Each `σ_p` is a well-formed unipotent block shear: it box-contains
>   (`closedBall 0 t ⊆ σ_p '' closedBall 0 (t + 2t²)`, `nativeSel_covers`), has `jacDet = 1`
>   (`nativeSel_jacDet`), is injective and differentiable. The `qkeep`/`srcKept` source discipline
>   (each corrected coordinate reads only kept coordinates) is discharged by `decide`.
> - **Assumed.** none (the shear data is fixed; the box-containment/Jacobian are unconditional).
> - **Cited.** none.
> - **Deferred.** the entry-equality `hentry` (that `σ_p` monomialises the survivor `coreGen` entry
>   exactly — the (B) seat); the per-leaf `jac`/`unit` normal form and `divisorMin = 8` (the (C) seat).
> - **Structure & ideas observed.** the nine §2 shears are the row/column-swap orbit of `shearPhiH`
>   under σ = colswap(j)∘rowswap(i); each is rank-≤2 (never rank-3), so the box inflation constant is
>   `C = 2` uniformly (`r ↦ r + 2r²`); the pivot `p` is never among its own corrected coordinates, so
>   the outer blow-up sees the un-sheared pivot coordinate.
> - **Route.** generic `qdisp` engine (rank-≤2 signed-quadratic displacement) proving
>   keep/read/norm-bound/covers/`jacDet=1`/injective once; the nine shears instantiate it with
>   machine-generated §2 data; the fan is an explicit 3-node `LeafCoverTiling.FanTree`, `Covers` by
>   direct nesting, flattened to the flat `Fin`-family via `Function.Surjective.iUnion_comp`.
> - **Status.** sorry-free

> **Claim (`hcover`).** The born-native leaf family covers a neighbourhood of the deepest point up to
> a null set: `volume (ball 0 1 \ ⋃ c, gFin c '' domFin c) = 0`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.NativeFan334.native_hcover`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2NativeFan334.lean` @ `c82688e40`)
> - **Gloss.** the Lebesgue measure of the part of the open unit ball not hit by any leaf-chart image
>   is zero — the `hcover` hypothesis of `rlctAt_coreGen334_ge_four_of_survivor_entries`.
> - **Proved.** unconditionally, and in fact as a FULL cover: `ball 0 1 ⊆ closedBall 0 1 ⊆
>   nativeFan.leafImages = ⋃ c, gFin c '' domFin c`, so the uncovered set is empty (a fortiori null).
>   Via `nativeFan_covers` (the tree `Covers (r↦r+2r²) · 1`, each node-1 shear box-containing at
>   `C=2`, the two id nodes trivially) + `leafImages_subset_flat` (the flatten) + the `Fin`-reindex.
> - **Assumed.** none.  **Cited.** none.
> - **Deferred.** none for `hcover` itself. (The `{X=0}` survivor hole of `SurvivorFanCover` never
>   arises: the full input-radial cover discharges the up-to-null obligation directly.)
> - **Status.** sorry-free  ·  axiom footprint: `[propext, Classical.choice, Quot.sound]`
>   (`#assert_banked_clean_batch`, 7 roots banked-clean, no cites).

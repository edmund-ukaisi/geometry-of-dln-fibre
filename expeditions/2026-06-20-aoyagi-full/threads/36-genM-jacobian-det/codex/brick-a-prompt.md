# Lean 4 / Mathlib — brick (a): the cleanest CLE architecture for the achiever-chart bridge

## The bridge to build
`composeFold fs = phiFlatStructV M t ha hN` where
  `phiFlatStructV x := paramsEquivFlat M (chartParamsGen (x p) M t (genBlkFlatStruct M t ha x) hle)`,
  `p = ⟨0,hN⟩`, `N = routeMAmbient M = flatDim M`.

I have BANKED the collapse lemma `composeFold_eq_cleConj_foldr`: if every factor is `cleConjFactor E gᵢ`
(SAME CLE `E : (Fin N → ℝ) ≃L W`), then `composeFold fs = E.symm ∘ (gs.foldr (·∘·) id) ∘ E`. The factor
dets read at `(E u).1` (block) via banked `schurChartFactor`/`lduChartFactor`/`chainVarMap`/`radialFactor`.

## The structures (all banked, opaque dependent widths Text/Wext)
- `chartParamsGen (u) M t B hle : Params M`, layer `s` = `reindex (chainA (Nblk s)(Wblk s)(C(s+1)))`
  where `C k = Bmat k · chainQ(N_k) + u • Rmat k` (interior), `chainA N W C = [C − N·W ; W]` (vertical
  block over Fin (M'_k)). `Params M := ∀ s : Fin L, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ`.
- `genBlkFlatStruct M t ha x : GenBlk M t` — reads K/X/N/E/W role blocks from DISJOINT flat slots of `x`
  via `chartIdxEquiv M (tDesc) ... : Fin N ≃ (Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k))`, then
  `frameSplitEquiv` (K⊕X⊕N⊕E sub-split) + `finProdFinEquiv` (matrix index). `Bmat (k+1) = bmatStack(K,X)
  = [K ; X·K]`, `Rmat (k+1) = rmatPad(E) = [[0,0],[0,E]]`, `Nblk = readN`, `Wblk = readW`. Boundary k=0:
  `Bmat 0 = reindex 1`, `Rmat 0 = 0`. So `C_{k+1} = [[K, KN],[XK, XKN+uE]]` (the Schur frame).
- `paramsEquivFlat M : Params M ≃ᵐ (Fin N → ℝ)` (measure-preserving) / `paramsEquivFlatCLE M` (the CLE),
  built from `FlatIdx M = Σ s : Fin L, Fin (M s.castSucc) × Fin (M s.succ)` via Fintype.equivFin-style.
- The radial scalar `x p = x ⟨0,hN⟩` (one designated flat coord). The achiever det wants the radial
  blow-up `|u_p|^{minAdm-1}` + spectator LDU/Schur exponents.

## The KEY DESIGN QUESTION (the foundational/hardest brick)
The collapse forces ONE CLE `E`. The bridge `(gs.foldr)(E x) = E (chartParamsGen (x p)(genBlkFlatStruct x))`
must hold (after the appropriate .symm). The layer-ops `gs` must reconstruct `chartParamsGen`'s layers
(the chainA/Schur-frame recursion) reading the role data K/X/N/E/W. TWO architectures:

**ARCH-1 (E = paramsEquivFlatCLE.symm, W = Params M):** layer-ops `gs : Params M → Params M`. The start
point `E x = paramsEquivFlat.symm x` is the RAW flat data reshaped to the Params layout. The role reads
`readK/X/N/E/W x` must be re-expressed as functions of this Params point (a permutation: both
chartIdxEquiv and paramsEquivFlat are Fin N bijections). Then the layer-ops build chainA from those.
PRO: bridge lands in Params (matches chartParamsGen's home). CON: the role reads become a
permutation-of-Params-entries — the genBlkFlatStruct chartIdxEquiv-slot layout must be aligned to the
paramsEquivFlat FlatIdx layout. Is that alignment a clean reindex, or a per-(k,role,i,j) index fight?

**ARCH-2 (E = a direct role-slot CLE, W = RoleSpace):** define `E : (Fin N → ℝ) ≃L RoleSpace` where
`RoleSpace = ℝ × ∏_s (K_s × X_s × N_s × E_s × W_s)` (radial + per-layer roles), built from the SAME
chartIdxEquiv. Then layer-ops read roles DIRECTLY (no permutation). But the bridge RHS is
`paramsEquivFlat (chartParamsGen ...)` (a flat vector), and the LHS is `E.symm ∘ (gs.foldr) ∘ E`, so the
final layer-op must produce the Params layout encoded in RoleSpace... mixed-space friction. Does ARCH-2
actually avoid the alignment, or just relocate it to `E.symm` vs `paramsEquivFlat`?

### Questions
1. Which architecture makes the bridge `funext`-cleanest over OPAQUE Text/Wext widths? Specifically, is
   the chartIdxEquiv-slot ↔ paramsEquivFlat-FlatIdx alignment (ARCH-1's role-read-as-Params-permutation)
   a genuine extra obstacle, or is it absorbable because BOTH go through the same `Fin N` and I only need
   `readK x i j = (paramsEquivFlat.symm x) ⟨decode...⟩` definitionally?
2. The det must read the right blocks at `(E u).1`. With ARCH-1, the Schur/LDU factor `E_s` (the per-
   factor block CLE for the det) is SEPARATE from the bridge's `E = paramsEquivFlat` — but
   composeFold_eq_cleConj_foldr needs ONE E for the whole list. Does that mean ALL factors must be
   cleConjFactor (paramsEquivFlatCLE.symm) — i.e. the Schur/LDU layer-ops act on Params, and their dets
   are read on Params-blocks NOT the SchurInc/LDUParam blocks? Then the banked schurChartFactor (which
   conjugates schurFrameMap via a block CLE into SchurInc×Rest) is the WRONG shape — I'd need the
   Schur/LDU ops as Params→Params maps with Params-level dets. Is that a problem (re-deriving the block
   monomial det at the Params level), or does det_conj make it free (det invariant under the Params
   embedding)?
3. Given the (2,2,2) achiever t=![2,1,1] (Text=[2,2,1,1], Wext=[2,2,2], frame K/X/N/E all 1×1 at k=0,
   liftDim=[2,0]): is this a good validate-small case for brick (a) — does it exercise the chainA/C
   recursion AND the role-slot alignment nontrivially? Or is 1×1 blocks too degenerate (products
   collapse) — should I use (3,3,4) (minAdm 8, N=21) or a 2×2-block case instead?
4. Concretely sketch the cleanest brick-(a) Lean definition: the per-layer Params-split structure +
   the ONE recommended architecture's layer-op `gs s` (what it reads, what it writes) + the single
   riskiest sub-lemma of the funext-s bridge.

Recommend ONE architecture with concrete Lean-level definitions. The make-or-break is avoiding a
per-index Text/Wext cast fight in the funext-s. Flag inference vs fact.

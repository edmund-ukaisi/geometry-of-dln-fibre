<task>
Lean 4 + Mathlib formalisation. I found a structural tension and want a strategy adjudication.

CONTEXT: A structured decoder `genBlkFlatStruct M t ha x : GenBlk M t` reads block data from flat coords,
gated by an admissibility structure:

  structure StructAdm (M t : Fin (L+1) → ℕ) : Prop where
    h0 : tDesc M t 0 = M 0
    hc : ∀ p, tDesc M t (p+1) ≤ Wext M (p+1)
    hL : 0 < L
    hdesc : ∀ k, Text M t (k+2) ≤ Text M t (k+1)   -- ∀ k : ℕ, ALL k
    hub   : ∀ k, Text M t (k+2) ≤ Wext M (k+1)      -- ∀ k : ℕ, ALL k

where `Text M t 0 = M 0`, `Text M t (j+1) = (if j < L+1 then t ⟨j⟩ else 1)` (saturates to 1 beyond range),
`Wext M k = (if k < L+1 then M ⟨k⟩ else 1)`.

THE GAP: The ACHIEVER descent path is `tach M = Fin.cons (M 0) (tStar M)` where `tStar M : Fin L → ℕ` is
the Aoyagi minimiser, which has LAST component `tStar M (last) = 0` (admissibility forces the last
exponent to 0). So `Text M (tach M) (L+1) = tach ⟨L⟩ = tStar (last) = 0`, and then
`hdesc L : Text M (tach M) (L+2) ≤ Text M (tach M) (L+1)` becomes `1 ≤ 0` (LHS saturates to 1), which is
FALSE. So `StructAdm M (tach M)` is UNPROVABLE for the achiever path. The existing (2,2,2) instance dodges
this by using a NON-achiever path `t222 = (2,1,1)` (last value 1, so `hdesc L : 1 ≤ 1` holds), but that path
has chain-codim ≠ minAdm, so it cannot carry the achiever Jacobian.

KEY FACT: `hdesc`/`hub`/`hc` are ONLY ever CONSUMED at indices `k < L` (the readers `readK/X/N/E` take
`k : Fin L`, so `k.val < L`; `genBlkFlatStruct` guards interior blocks by `if k < L`; `hleStruct` proves
`∀ k, k < L → ...`). The `∀ k : ℕ` quantification in `StructAdm` is strictly stronger than every use.

OPTIONS:
(A) WEAKEN the structure to `hdesc : ∀ k, k < L → ...` and `hub : ∀ k, k < L → ...` (and likewise drop the
    out-of-range part of `hc`). Then `StructAdm M (tach M)` becomes provable. Cost: ~6 consumer sites
    (readK/X/N/E, genBlkFlatStruct ×2, hleStruct) must pass `k.isLt`/`hk` to the now-conditional fields.
    Touches the shared decoder file. The existing `structAdm222` instance gets EASIER (fewer goals).
(B) BYPASS StructAdm entirely: hand-build `B_det M : GenBlk M (tach M)` directly (like the (3,3,3,3) anchor
    `B_det3333`, which does NOT use StructAdm — it provides explicit per-`k` matrix fields), supplying
    `bmatStack`/`rmatPad` with per-boundary `hdesc k`/`hub k` derived inline for `k < L`. Cost: re-derive the
    reader/slot plumbing without StructAdm (the readers are DEFINED in terms of `ha.h0/hc/hL/hdesc/hub`).
(C) Define a SEPARATE achiever-specific admissibility (a new structure with the `k < L` bounds), and a
    parallel decoder. Cost: duplicates the reader infra.

The downstream RATE is decoder-agnostic (`routeMCore (phiGen u M t B hle) = u²·VvalGen` for ANY GenBlk B
with the identity-boundary `C 0 = 1`), so whichever decoder I build, the rate is one line. The decoder only
needs: `Bmat 0 = reindex 1`, `Rmat 0 = 0` (for `C 0 = 1`); interior `Bmat(k+1) = bmatStack`,
`Rmat(k+1) = rmatPad`; a LIVE leaf `Rfin L` with a fixed-1 pivot (the (3,3,3,3) anchor has
`Rfin 3 = [x24,x25,x26]`).

QUESTIONS:
Q1. Is my diagnosis correct that `StructAdm M (tach M)` is genuinely unprovable for the achiever path
    (last tStar = 0), and that this is an over-specification (`∀ k` where `k < L` suffices)? Confirm or
    refute with the precise failing index.
Q2. Rank options A/B/C by total Lean cost AND by bedrock-quality (weakest-hypothesis, reuse, not breaking
    the (2,2,2) anchor). I lean toward (A) — weaken the shared structure to its actually-used strength —
    is that the right call, or does touching the shared decoder file carry a hidden risk (e.g. definitional
    unfolding of `genBlkFlatStruct` elsewhere that would now see a different `StructAdm` field type)?
Q3. If (A): the cleanest mechanical refactor. The fields become `hdesc : ∀ k, k < L → ...`. At consumer site
    `frameSplitEquiv M t (k.val+1) (ha.hdesc k.val) (ha.hub k.val)` with `k : Fin L`, I'd write
    `ha.hdesc k.val k.isLt`. Are there subtleties with `ha.hub k` in `hleStruct`'s `| (k+1) => exact ha.hub k`
    (there the `k` is the chain index with an implicit `k < L` from the `∀ k, k < L →` wrapper)? Sketch the
    field signatures + the 6 consumer edits.

OUTPUT CONTRACT:
- Q1: one paragraph, the precise failing index + confirm/refute.
- Q2: a ranked list (A/B/C) with one-line cost + bedrock note each, then the single recommendation.
- Q3: the new field signatures and the list of consumer-site edits (call-shape only).
- ≤ 1 page total. Flag any INFERENCE about the consumer sites vs what I stated as fact.
</task>

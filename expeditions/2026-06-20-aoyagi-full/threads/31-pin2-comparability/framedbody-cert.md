# `framedParams_split_eq_frame_raw` body — build-ready sub-lemma decomposition

The cert body (`DeepestGaugeConstruction.lean` ~1490, currently `sorry` with a TRUE conclusion). For
`w ∈ U` it must produce blocks `P00,P01,P10,P11` with: (a) `hconj`; (b) the reg-energy identity
`∑(deepestEFull (split w))² = Sreg`; (c) the leak bound; (d,e) the core comparability. Decorrelated
Codex (xhigh, `codex/framedbody-*`) reordered the risk: **the highest risk is the S3 frame-source
reconciliation, NOT the S1' pivot decode**; and S5 hides three obligations (`P00` unit, leak estimate,
`Rcore↔coreAbsorb` identification). The decomposition below folds those in.

Object names verified against the integrated tree (`bcfb8b60`). `deepestEFull` (`:410`) already packs the
RESIDUAL blocks `(toBlocks₁₁ − 1, toBlocks₁₂, toBlocks₂₁)` — Codex's "must subtract the corner" caveat is
already satisfied.

---

## S0 — frame/pivot reconciliation (the HIGHEST-risk step; do FIRST)

The endpoint frame `QL`/`P0` that telescopes the product (S2) and the pivot `J`/`Q` that normalizes `B`
(S3) MUST be the same data. The caller `deepest_gauge_construction` already co-sources them:
`deepestPoint_frame_pivot_exists H r B hB hr hL hL2` returns `⟨Jb, Pf, Qf, …, hNF, hQf22b, hcorner⟩` —
ONE bundle giving the frame family `(Pf, Qf)` AND `hcorner : reindex(rThr, pivotThr Jb)(deepestPoint_last
· Qf_last) = fromBlocks 1 0 0 0`, with `J := Jb.trans (finCongr …)` and `hpivJ : pivotJSucc J = Jb`. So
`QL := Qf (lastLayer hL)` is BOTH the telescope endpoint AND the `B`-normalizer — definitionally the same
object; no `Q_last = Q_pivot` equality to prove.

**Build-ready sub-lemma (S0):** none new — the cert RECEIVES `Pf, Qf, J` as hypotheses and the caller
supplies the reconciled bundle. The cert's job is to USE `hcorner` (S3) and the SAME `Pf, Qf` in the
telescope (S2). **The one tripwire:** `hcorner` is stated with `pivotJSucc J` (= `Jb`) on the column side;
the cert's `hconj` target uses `pivotThresholdSplit r (H (Fin.last L)) J`. The `finCongr (H_lastLayer_succ)`
cast between `Fin (H (lastLayer).succ)` and `Fin (H (Fin.last L))` must be discharged (the `hpivJ` round-trip).
Flag for the formaliser: keep the column index type uniform — a mismatch is a typecheck failure, not a
silent unsoundness.

## S1 — per-layer round-trip (NON-last layers), exact, banked atoms

**Sub-lemma (S1):** for `s ≠ lastLayer hL`,
`framedParamsPivot H r hr hL J Pf Qf (split w) s = Pf s * ((paramsEquivFlat H).symm w) s * Qf s`.

Proof chain (each step a banked atom):
- `framedParamsPivot_of_ne_last` → `= framedParams … s` → `= framedLayer s (Pf s) (Qf s) (readX) (readY)
  (readZ) (coreRead)` = `corM_s + Pf s · reindex(rThr.symm, rThr.symm)(fromBlocks readX readY readZ
  coreRead) · Qf s` (def `framedLayer`).
- `reindex_fromBlocks_reads_eq_deviation` (banked, threshold both sides): the `reindex(fromBlocks …)`
  term `= ((paramsEquivFlat H).symm (w − wstar)) s` where `wstar = paramsEquivFlat(deepestPoint)`. **This
  is the step the docstring called the "sub-blocker / genuine bulk" — it is ALREADY BANKED sorry-free.**
- `corM_s = Pf s · deepestPoint_s · Qf s` (`deepestPoint_frame_normal`).
- affine bridge `((paramsEquivFlat).symm (w − wstar)) s = (paramsSymm w)_s − deepestPoint_s` (the
  `paramsEquivFlat` linearity + `wstar = paramsEquivFlat deepestPoint`; small exact lemma if not inlined —
  `(paramsEquivFlat).symm` is linear, `symm(w − wstar) = symm w − symm wstar = symm w − deepestPoint`).
- combine: `framedLayer = Pf·deepest·Qf + Pf·(paramsSymm w − deepest)·Qf = Pf·(paramsSymm w)·Qf`
  (`mul_add`/`mul_sub`, `add_sub_cancel`).

## S1' — last-layer pivot-column variant (exact relabel; a SEPARATE bridge lemma)

> **CORRECTION (thread 31 formalisation tide, 2026-06-25): option α below is REFUTED.** Pen-and-paper
> + decorrelated Codex (xhigh) adjudication (`hs1prime-verdict.md`): the clean form
> `framedParamsPivot (split w) last = Pf last · (paramsSymm w) last · Qf last` is **FALSE** for a
> non-front pivot `J`. `framedParamsPivot_last` reindexes the column side by the PIVOT split, but the
> gauge reads are J-INDEPENDENT threshold decodes (`readY/readT_deepestSplit_raw` land block-col
> `inr q ↦` deviation col `r+q`), so the reads term equals the deviation with columns PERMUTED by
> `π_J(j) = (rThr).symm (pivotThr J · j)`. Option-α's premise ("the role index is split-independent so
> the decoders agree per-entry") is the error: the reads ARE threshold, but `framedParamsPivot_last`
> PLACES them at pivot columns. Counterexample `H=(1,1,2)`, `J 0 = 1` (columns swapped). The TRUE
> statement is the permuted form; the fix (verdict option A) is to fold the orthogonal `Pπ`
> (`colPerm_J M = M·Pπ`) into the endpoint `QL` + `B`-pivot normalization — it should cancel against
> the SAME outer `reindex(rThr, pivotThr J)` carried on BOTH `deepestEFull` and `Sreg`. **At the
> deepest gauge `w0` the deviation vanishes (`split w0 = 0`), so `π_J` acts trivially — `hframe0`/`hS2_w0`/
> `hS3b` are SOUND at `w0` (LANDED this tide); only the general-`w` energy identity (the `hproducer`
> `sorry`) needs the cancellation.** See `hs1prime-verdict.md`.

`framedParamsPivot`'s LAST layer (`framedParamsPivot_last`) reindexes the column side by
`pivotThresholdSplit r (H last.succ) (pivotJSucc J)`, not `rThresholdSplit`. The banked
`reindex_fromBlocks_reads_eq_deviation` uses `rThresholdSplit` on BOTH sides, so it does not apply
verbatim. **Build-ready sub-lemma (S1'):**

    theorem reindex_fromBlocks_reads_eq_deviation_pivotColumn (H) (r) (hr) (hL) (J) (wstar w) :
      Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _)).symm
          (pivotThresholdSplit r (H (lastLayer hL).succ) (hr _) (pivotJSucc H r hL J)).symm
          (Matrix.fromBlocks (readX … (lastLayer hL)) (readY …) (readZ …) (coreRead …))
        = ((paramsEquivFlat H).symm (w - wstar)) (lastLayer hL)

PRE-DERIVED (exact): the proof is the banked one's `ext i j` + 4-way case-split, with the COLUMN cases
using `pivotThresholdSplit_symm_inl/inr` (banked, `:176/:182`) in place of `rThresholdSplit_symm_inl/inr`.
The decode RHS index must change accordingly: where the threshold proof recovers column position `r + b`
(via `rThresholdSplit_symm_inr`, the threshold complement), the pivot proof recovers
`(pivotSupport)ᶜ.orderEmbOfFin b` (the b-th non-pivot column). **This means `readY_deepestSplit_raw` /
`readT_deepestSplit_raw` — whose RHS hard-codes the threshold column `⟨r+b,…⟩` — do NOT serve the last
layer directly.** Two clean options for the formaliser:

  (option α, RECOMMENDED) State S1' as the identity above where the RHS is just `((paramsEquivFlat).symm
  (w − wstar)) last` — i.e. DON'T decode to per-block raw entries; instead observe that the LHS and the
  banked threshold version reindex the SAME `fromBlocks` matrix and differ ONLY by a column permutation
  `π_J` on BOTH the reindex and (implicitly) nothing else — but the raw layer `(paramsSymm w)_last` is
  the SAME matrix regardless of how we split its columns. Concretely: `reindex e₁ e₂ M = reindex e₁ e₂' M`
  is FALSE in general, BUT here the two sides decode the SAME entry `M[i][j]` to the SAME raw-layer entry
  because the `fromBlocks` is BUILT from reads at role indices, and the role index of a column is
  split-independent (the read is `regGaugeSlotEquiv` at `⟨s, role⟩`, not at a threshold position). So the
  cleanest statement is per-entry: for the last layer, `reindex(rThr.symm, pivotThr.symm)(fromBlocks
  reads) i j = (paramsSymm w − deepest)_last i j` — proved by the same 4-case `ext` with the column
  decoder swapped. ~30–40 LoC, structurally identical to the banked atom.

  (option β) Add pivot-column variants of `readY/Z/T_deepestSplit_raw` whose RHS is the pivot-recovered
  column. More lemmas; avoid unless α stalls.

**Risk: type/cast/reindex bookkeeping, NOT mathematical soundness** (Codex Q2, concur). The math is a
relabel; the friction is the `finCongr (H_lastLayer_succ)` cast on `J` and the `pivotJSucc` unfold.

## S2 — telescope, banked

**Sub-lemma (S2):** `prod H (framedParamsPivot … (split w)) = Pf first · prod H ((paramsEquivFlat).symm w)
· Qf last`. Apply `endpoint_telescoping H hL ((paramsEquivFlat).symm w) (framedParamsPivot … (split w))
Pf Qf hframe hinterface` where `hframe s := S1/S1'` (the per-layer round-trip) and `hinterface` is the
interior-collapse. For `L = 2`: no strict-interior interface, `hQf0`/`hPfL` (boundary) suffice. For
`L ≥ 3`: thread `deepestPoint_interior_frame_id` (`DeepestFrame.lean:108`). Set `P0 := Pf first`,
`QL := Qf last`.

## S3 — B-normalize → hconj (a subtlety CONFIRMED: `hcorner` is about `deepestPoint`, not `B`)

**Sub-lemma (S3) = conjunct (a):** `reindex(rThr, pivotThr J)(P0·(prod((paramsEquivFlat).symm w) − B)·QL)
= fromBlocks (P00−1) P01 P10 P11`. From S2: `P0·prod(paramsSymm w)·QL = prod(framedParamsPivot)`.
Subtract the `B`-normalization: `reindex(P0·(prod − B)·QL) = reindex(prod(framedParamsPivot)) −
reindex(P0·B·QL)`; if `reindex(P0·B·QL) = fromBlocks 1 0 0 0` then the `−` shifts `P00 ↦ P00 − 1`,
`P01/P10/P11` unchanged (`reindex` + `fromBlocks` linear). Define `P00 := toBlocks₁₁(reindex prod
framedParamsPivot)`, etc.

**CONFIRMED subtlety (I checked the bundle):** `deepestPoint_frame_pivot_exists`'s last component
(`DeepestPivotFrame.lean:290`) normalizes `(deepestPoint … (lastLayer)) · Q`, NOT `B` directly:
`reindex(rThr, pivotThr J)(deepestPoint_last · Q_last) = fromBlocks 1 0 0 0`. So `reindex(P0·B·QL) =
fromBlocks 1 0 0 0` is a SEPARATE sub-step, NOT the bundle's atom. The clean bridge (both facts BANKED):
- `prod H (deepestPoint H r B hB hr hL) = B` (`(deepestPoint_isDeep …).1`, `Skeleton.lean:1046`).
- so `reindex(P0·B·QL) = reindex(P0·prod(deepestPoint)·QL)`; apply the telescope (S2's
  `endpoint_telescoping`) a SECOND time to `A := deepestPoint` (the SAME frames `Pf, Qf`): `P0·prod(deepest)
  ·QL = prod(framedParamsPivot at the deepest gauge slot)`, whose reindexed product is the corner
  `fromBlocks 1 0 0 0` (each per-layer frame carries `deepestPoint_s` to `corM`, and the product of corners
  is the corner — the `reindex_prodAux_framedParamsRegPivot_zero`-style fact, here for `framedParamsPivot`
  at core-0).

**Build-ready sub-lemma (S3b):** `reindex(rThr, pivotThr J)(P0 · B · QL) = fromBlocks 1 0 0 0`. Route:
`B = prod(deepest)` ▸ telescope-of-deepest ▸ product-of-corners-is-corner. The product-of-corners atom is
the `framedParamsPivot`/`framedParamsRegPivot` zero-slot product `reindex_prodAux_framedParamsRegPivot_zero`
(banked for `framedParamsRegPivot`; needs the `framedParamsPivot`-at-core-0 variant, = `framedParamsRegPivot`
by `framedParamsPivot_coreZero`, so it transfers). This is a real sub-step but every piece is banked or a
core-0 collapse. **Not free, but low-risk.**

## S4 — reg-energy identity = conjunct (b)

**Sub-lemma (S4):** `∑ i, (deepestEFull H r hr hL J Pf Qf (split w)) i ^ 2 = Sreg`. `deepestEFull` reads
the residual reg blocks of `reindex(prod(framedParamsPivot (split w)))`. By S2+S3 these are the SAME
`(P00−1, P01, P10)` as `hconj`. Then `regResidualPack` bijectivity packs: this is EXACTLY the structure of
the banked `deepestEPivot_sq_sum_eq_blocks` (`:~1420`) with `deepestEPivot ↦ deepestEFull`,
`framedParamsRegPivot ↦ framedParamsPivot` — re-prove that summing identity for `deepestEFull` (the same
`Equiv.sum_comp` + `Fintype.sum_sum_type`/`sum_prod_type` skeleton). Then rewrite the blocks to `P00−1,
P01, P10` via S3. ~the banked lemma's proof verbatim with the object swapped.

## S5 — the three core/leak obligations (Codex: under-compressed; split out)

S5a — **`P00` unit + shrink `U`:** `P00 = toBlocks₁₁(reindex prod(framedParamsPivot))`; at `w = wstar`,
`P00 = 1` (the corner), so `IsUnit P00` on a neighborhood by continuity (`prod` entries are continuous in
`w`; `det P00` continuous, `≠ 0` at `wstar`). Shrink `U` to `{det P00 ≠ 0}`. Provides `Invertible P00` +
a bound `‖⅟P00‖ ≤ M` on `U`.

S5b — **leak estimate = conjunct (c):** `∑(P10·⅟P00·P01)² ≤ t²·Sreg`. NOT from `fullProduct_core_split`
(Codex). It is a small-neighborhood quadratic estimate: `P01, P10 → 0` as `w → wstar` (off-diagonal reg
blocks vanish at the corner), `⅟P00` bounded (S5a), so `‖P10·⅟P00·P01‖² ≤ ‖⅟P00‖²·‖P10‖²·‖P01‖² ≤ t²·(‖P10‖²
+ ‖P01‖²) ≤ t²·Sreg` for `t² := ‖⅟P00‖²·sup_U(‖P01‖² or ‖P10‖²)` (pick `t` so the product of two small
factors is ≤ `t²` times one of them). **Build-ready sub-lemma:** `∃ t, ∀ w ∈ U', ∑(P10⅟P00 P01)² ≤
t²·Sreg` — a Cauchy-Schwarz / sub-multiplicativity estimate on the shrunk `U'`. Exact-algebra-light but a
genuine analysis lemma (the `t = ‖pivot‖ → 0` story in the `core_comparability_squeeze` docstring).

S5c — **core identification = conjuncts (d,e):** `Rcore := P11 − P10·⅟P00·P01` two-sidedly comparable to
`deepestCoreF (deepestCoreAbsorb (split w)).2.1`. `core_comparability_squeeze` (atom 6) does NOT supply
this — it compares `∑E²+‖Rcore‖²` to `∑E²+‖P11‖²` given the split, but does NOT identify `Rcore` with the
`coreAbsorb` functional. **Build-ready sub-lemma:** the global-Schur ↔ per-layer-coreAbsorb comparability:
`∑Rcore² ≍ deepestCoreF(coreAbsorb …)`, i.e. `Rcore = ∏S_s + (ideal(E) terms)` (g156: the Schur complement
of a product ≠ product of per-layer Schur, but `Rcore − ∏S_s ∈ ideal(reg)`, charged to `∑E²`). This is
the genuinely-new geometric content of the core arm — and it is the SECOND-highest risk after S0. It needs
the per-layer-Schur-shift `deepestCoreAbsorb` (= `schurCutoffShift`) related to the global `Rcore`. Flag:
this conjunct may need its own decorrelated adjudication if the `Rcore − ∏S_s ∈ ideal(E)` membership
isn't already banked; `core_comparability_squeeze` + `fullProduct_core_split` give the FRAME, not the
identification.

## Highest-risk ranking (Codex-corrected)

1. **S0 frame/pivot reconciliation** + S3's `hcorner`-about-`B` check — structural; the `QL`/`J` must be
   one object across telescope + normalize. (Largely discharged by the co-sourced bundle; verify the
   `B`-vs-`deepestPoint` form of `hcorner`.)
2. **S5c** core identification `Rcore ↔ deepestCoreF(coreAbsorb)` — the genuine new geometry; may need its
   own cert if the ideal-membership isn't banked.
3. **S5b** leak estimate — a real (if routine) neighborhood analysis lemma, NOT a corollary of a banked atom.
4. **S1'** pivot-column decode — exact relabel, cast/bookkeeping risk only (option α).

## The exact-algebra step I pre-derived (S1')

The pivot-column decode (S1', option α) is the one I was asked to pre-derive. It is `reindex_fromBlocks_
reads_eq_deviation` with the column-side `rThresholdSplit_symm_inr` swapped for `pivotThresholdSplit_symm_
inr`. Entry-wise (`ext i j`, 4-way `rcases` on the row `rThresholdSplit` and the column `pivotThresholdSplit`):
- `(inl a, inl b)`: `fromBlocks_apply₁₁` → `readX` decode (row threshold, col pivot — the X-block reads at
  role `⟨last, inl(inl(a,b))⟩`, split-independent).
- `(inl a, inr b)`: `fromBlocks_apply₁₂` → `readY` decode at the pivot-recovered column.
- `(inr a, inl b)`: `fromBlocks_apply₂₁` → `readZ`.
- `(inr a, inr b)`: `fromBlocks_apply₂₂` → `readT`.
Because each read is `regGaugeSlotEquiv` at a ROLE index (not a threshold position), the column decoder
(threshold vs pivot) only changes WHICH `Fin (H last.succ)` index `j` the entry sits at — and the raw
layer `(paramsSymm w − deepest)_last` is the same matrix; both decoders agree on the per-entry value
because the reconstruction is `reindex⁻¹` of the SAME role-indexed reads. So the identity holds; the proof
is the banked 4-case `ext` with `pivotThresholdSplit_symm_*`. No new matrix algebra — confirmed exact.

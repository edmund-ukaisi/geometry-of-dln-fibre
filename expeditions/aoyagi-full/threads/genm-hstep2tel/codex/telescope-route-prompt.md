# Consult: general-L Schur→Score telescope (Lean 4 / Mathlib v4.29, DLNFibre)

I am building Producer 3 (`hsub4core` Schur→Score telescope) for #120 `hstep2`, general depth `L`.
I want to **mirror the banked L=2 theorem `prod_deepestM_eq_schur_ldu_readback`** at general `L`,
reusing banked general-`L` lemmas. Please red-team the route + flag the biggest cast/logic risk.
DO NOT write Lean; give the proof route, the exact lemma chain, missing infrastructure, and LoC.

## The L=2 template I'm mirroring (banked, sorry-free)

`prod_deepestM_eq_schur_ldu_readback (H : Fin 3 → ℕ) (r) (B) (hr) (J = frontEmbed) (Pf Qf)
  (frame triangular/22=1 hyps) (hS3b: reindex(P0·B·QL) = fromBlocks 1 0 0 0) (pivot inverts)
  (C : Params (deepestM H r)) (hC0 hC1 : reindex(C s) = per-layer Schur core of reindexed decode layer s)
  : prod (deepestM H r) C = ScoreMatrix x`
where `ScoreMatrix x = of (fun i j => [ (1,1)-Schur integrand of
  reindex(rThr 0)(pivotThr J)(endpointP0·(prod(decode x) − B)·endpointQL) over pivot (M₁₁+1)⁻¹ ] i j)`,
`decode x = (paramsEquivFlat H).symm x`.

Its proof chains: `prod_deepestM_eq_two_of_L2` (unfold LHS to 2 factors) + hC0/hC1 → LDU
`S0c·(1−Kc)·S1c`; `unframedSchur_prodDecode_eq_ldu` (= `reindex_mul_schur_factor`) identifies that LDU
with unframed Schur of `reindex(prod decode)`; `score_eq_unframedSchur_prodDecode` identifies unframed
Schur with the Score integrand (via corner-split `rcore_eq_schur_of_corner_split` on hS3b + frame-strip
`framedSchur_eq_unframedSchur_L2`).

## Banked GENERAL-L lemmas available

1. `prodSchurCore_eq_blockSchur_partProd (C_chain : (s:ℕ)→Matrix (r⊕m s)(r⊕m (s+1)) α) (Z0edit) (L)
   (hLayer: ∀k<L, Invertible (C_chain k).toBlocks₁₁) (hPart: ∀k≤L, Invertible (partProd C_chain k).toBlocks₁₁)
   : prodSchurCore C_chain Z0edit L = blockSchur (partProd C_chain L)`.
   Here `prodSchurCore … (k+1) = prodSchurCore … k * blockSchur (movedC C_chain Z0edit k)`,
   `blockSchur (movedC C_chain Z0edit s) = schurTilde C_chain s = (1 − Kcoup C_chain s)·blockSchur (C_chain s)`.
2. `reindex_prod_eq_partProd (H) (r) (hr) (A : Params H)
   : reindex (rThr 0) (deepestChainCol H r hr L _) (prod H A) = partProd (deepestChain H r hr A) L`.
   `deepestChain H r hr A s = reindex (deepestChainSplit … s)(deepestChainSplit … (s+1)) (deepestChainLayer H r A s)`,
   `deepestChainSplit … s = rThresholdSplit r (deepestChainWidth H s) _`, `deepestChainWidth H s = H ⟨min s L,_⟩`,
   `deepestChainCol H r hr L _ = (finCongr (H⟨L⟩ = chainWidth L)).trans (deepestChainSplit … L)`.
3. `blockSchur_lowerFrame_left`, `blockSchur_rightUpper_right` — one-sided ₂₂=1 frame Schur-invisibility.
4. `score_eq_unframedSchur_prodDecode (H : Fin (L+1)) (r) (B) (hr) (hL) (hL2 : L = 2) (J=frontEmbed) (Pf Qf)
   (frame hyps) (hS3b) (pivot inverts) : [Score integrand] = [unframed (1,1)-Schur of
   reindex(rThr 0)(pivotThr J)(prod decode) over its own pivot]`. I verified its PROOF BODY does NOT use
   `hL2` (it only calls `framedSchur_eq_unframedSchur_L2` + `rcore_eq_schur_of_corner_split`, both general).
5. `framedSchur_eq_unframedSchur_L2` — actually general-L (only uses `schur_frame_transform`); strips
   endpoint frames P0/QL from a single product matrix M. `rcore_eq_schur_of_corner_split` — general.

## The target statement I intend

`prod_deepestM_eq_schur_ldu_readback_gen (H : Fin (L+1) → ℕ) (r) (B) (hr) (hL:1≤L) (J=frontEmbed)
  (Pf Qf) (frame hyps) (hS3b) (x) (C : Params (deepestM H r))
  (hC : ∀ s : Fin L, [cast/reindex of C s] = blockSchur (movedC (deepestChain H r hr (decode x))
        (Z0edit0 (deepestChain H r hr (decode x)) L) (s:ℕ)))
  (invertibility hyps on the chain + frame pivots)
  : prod (deepestM H r) C = ScoreMatrix x`.

## My intended route

(a) **Fin→ℕ reduced-core bridge (NEW):** `prod (deepestM H r) C = prodSchurCore (deepestChain … (decode x)) Z0 L`,
    given `hC`. Mirror of `reindex_prodAux_eq_partProd` but on UNBLOCKED reduced-core matrices
    (widths `H s − r` vs `chainWidth s − r`, a `finCongr` cast; each factor `C s = blockSchur(movedC … s)`).
(b) `prodSchurCore_eq_blockSchur_partProd` → `= blockSchur (partProd (deepestChain … (decode x)) L)`
    (needs the chain layer/partial-pivot invertibility).
(c) `reindex_prod_eq_partProd` (backwards) → `= blockSchur (reindex (rThr 0)(deepestChainCol L)(prod decode))`
    = unframed (1,1)-Schur of `reindex(prod decode)`.
(d) cast-reconcile `deepestChainCol L` (col split from (c)) vs `pivotThr r (H last) J` / `rThr (H last)`
    (col split in `score_eq_unframedSchur_prodDecode`) at `J = frontEmbed` (`pivotThresholdSplit_frontEmbed`
    collapses pivotThr J to rThr; and `deepestChainCol L` = finCongr∘rThr(chainWidth L) with chainWidth L = H last).
(e) `score_eq_unframedSchur_prodDecode` → `= ScoreMatrix x` (with `hL2 := rfl` only if L=2; but I want general L,
    so I'll pass `hL2` ONLY IF it's provable — it isn't for L≥3).

## Questions

Q1. **The `hL2` blocker in (e).** `score_eq_unframedSchur_prodDecode` TAKES `hL2 : L = 2` in its signature
    even though its body ignores it. To use it at general L I must either (i) generalise its signature (drop
    `hL2` — safe since body ignores it, but it's a shared canonical module I should not edit), or (ii) restate
    a general-L copy of it in MY module. Is (ii) — re-proving `score_eq_unframedSchur_prodDecode` general-L in
    my own module from `framedSchur_eq_unframedSchur_L2` + `rcore_eq_schur_of_corner_split` — the right move?
    Any hidden L=2 dependence in `framedSchur_eq_unframedSchur_L2` / `rcore_eq_schur_of_corner_split` I'm missing?

Q2. **Is bridge (a) sound + the cleanest?** Is `prod (deepestM H r) C = prodSchurCore (deepestChain(decode x)) Z0 L`
    the right connective, or is there a cleaner statement of the whole telescope that avoids re-deriving a
    reduced-core Fin→ℕ induction? Note `prodSchurCore`'s width family is `m s = Fin (chainWidth H s − r)`
    while `prod (deepestM) C` runs over `Fin (H s − r)`; `chainWidth H s = H⟨min s L,_⟩` is defeq to `H s`
    for `s ≤ L` but needs `min s L` reduction. Flag the cast hazard.

Q3. **The `movedC` corner vs the `−B` corner.** `prodSchurCore` = `blockSchur(partProd chain)` includes the
    FULL product (the `deepestPoint` corner `diag(I_r,0)` at the boundary). The Score integrand is over
    `prod decode − B` (corner removed via hS3b). Does `score_eq_unframedSchur_prodDecode` fully absorb the
    `−B`/corner difference so that step (c)'s `blockSchur(reindex(prod decode))` [FULL product, no −B] matches
    its LHS `[unframed Schur of reindex(prod decode)]`? I.e. is the `−B` entirely inside `score_eq_unframed…`'s
    Score-side and NOT on its unframed-Schur side? (Reading its statement: RHS = unframed Schur of `prod decode`
    (no −B); LHS = Score integrand (with −B). So (c)'s output matches its RHS. Confirm.)

Q4. Biggest risk + rough LoC for (a)+(d)+the general-L restatement of (e). Is any piece a genuine wall
    (STOP-and-report) vs bounded cast plumbing?

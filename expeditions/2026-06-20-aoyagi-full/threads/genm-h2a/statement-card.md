# Statement card — H2a `lduleafH` + `lduleafH_pivot`

The fs-independent multi-axis Jacobian-exponent vector of the LDU-lensed interior achiever chart, and
its value at the binding pivot axis. fs-INDEPENDENT atoms wired by genm-r1lower (H1) into
`RouteMInteriorLDUContract`'s `interiorLDU_leafH` / `interiorLDU_leafH_pivot` sorries.

> **Claim (atom 1, `lduleafH`).** The LDU-lensed interior chart's Jacobian-exponent vector
> `Fin (routeMAmbient M) → ℕ` is `minAdm M − 1` at the binding pivot axis `structPivot M hN = ⟨0,_⟩`
> (the radial blow-up exponent), `(r_s + c_s) + 2·(t_s − 1 − i)` at the lensed K-core diagonal flat
> slot `(s, q_{s,i})` (the Schur frame `r_s+c_s` + LDU core `2(t_s−1−i)` exponents), `0` on spectator
> axes; with boundary-`s` widths (`s = k+1`, `k : Fin L`) `t_s = Text M (tach M) (k+2)`,
> `r_s = Text M (tach M) (k+1) − Text M (tach M) (k+2)`, `c_s = Wext M (k+1) − Text M (tach M) (k+2)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.lduleafH`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDULeafH.lean` @ `<commit-sha>`)
> - **Gloss.** A total `Fin (routeMAmbient M) → ℕ` function defined by: at the pivot index it is
>   `minAdm M − 1`; at every other index it consults `lduleafHOnIdx` after decoding the index through
>   the chart bijection `chartIdxEquiv`. `lduleafHOnIdx` places `(r_s+c_s)+2(t_s−1−i)` on the K-role
>   diagonal entries (decode the frame split to the K branch `Sum.inl (Sum.inl (Sum.inl qK))`,
>   read `(i,j) = finProdFinEquiv.symm qK`, test `i = j`), and `0` on every other role / off-diagonal
>   / lift slot.
> - **Proved.** The def type-checks at the frozen contract signature (the `interiorLDU_leafH` shape);
>   the construction is total and the K-diagonal placement mirrors the banked witness `wOnIdx` /
>   reader `readK` addressing (same `chartIdxEquiv` + `frameSplitEquiv` + `finProdFinEquiv` route).
> - **Assumed.** `ha : StructAdm M (tach M)` (the achiever-path admissibility — supplies `h0/hc/hL`
>   for `chartIdxEquiv` and `hdesc/hub` for `frameSplitEquiv`); `hN : 0 < routeMAmbient M`.
> - **Cited.** none.
> - **Deferred.** The exponent VALUES `(r_s+c_s)+2(t_s−1−i)` are pinned to the actual per-factor
>   Jacobian dets ONLY by the SEPARATE det-bookkeeping atom `ldu_det_bookkeeping` (H2b — NOT in this
>   file, waits on H1's `fs`). This card claims the construction + pivot value, not the det match.
> - **Status.** sorry-free.

> **Claim (atom 2, `lduleafH_pivot`).** The binding pivot axis carries the radial blow-up exponent:
> `lduleafH M ha hN (structPivot M hN) = minAdm M − 1`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.lduleafH_pivot`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDULeafH.lean` @ `<commit-sha>`)
> - **Gloss.** Evaluating the exponent vector at the pivot index `⟨0,hN⟩` returns `minAdm M − 1`.
> - **Proved.** Unconditionally (`rw [lduleafH, if_pos rfl]` — the pivot override is the `if`'s
>   `then` branch). Mirrors the banked `(3,3,3,3)` `leafH3333_pivot`.
> - **Assumed.** Same `ha`, `hN` as atom 1.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free.

**Axioms.** `lduleafH`, `lduleafH_pivot`, `lduleafHOnIdx` each depend on exactly
`[propext, Classical.choice, Quot.sound]` (the clean three) — no new axiom, no `monomial_rlct`
(fs-independent atom does not touch the rlct interface).

**Design note (Codex-vetted).** The pivot is the raw flat index `⟨0,_⟩` (the radial scalar is read
directly as `x ⟨0⟩`, NOT through `chartIdxEquiv`), while the K-diagonal slots are images of
`chartIdxEquiv.symm`. Since `chartIdxEquiv` is opaque (`Fintype.equivFin`), one cannot decide at opaque
width whether index 0 coincides with a K-diagonal slot. The override-at-pivot design
(`if j = structPivot then minAdm−1 else …`) makes the pivot lemma `if_pos rfl` and keeps the radial
bookkeeping (`pivotBlowupOn` det `|u_p|^{minAdm−1}`) separate from the K bookkeeping by construction —
the faithful encoding of the brief's "radial at pivot ⊕ K-exponents at K-slots ⊕ 0 elsewhere". H2b's
det-bookkeeping must use the same support (the K-diagonal placement excluding the pivot).

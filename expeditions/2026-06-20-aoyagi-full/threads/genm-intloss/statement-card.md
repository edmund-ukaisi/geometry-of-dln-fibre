# genm-intloss — statement cards (interior-cell per-`p` loss finiteness)

Thread `genm-intloss` (aoyagi-full Stage 2/3a): the INTERIOR loss side of the (□) discharge — the
per-`p` box-RLCT finiteness of the front loss `E_top + E_tr`. Branch `origin/genm-intloss`, off
`genm-integration@89f3f5fc5`. File `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorLoss.lean`.

Context correction banked here: couplerad §w3-interior (iii) flagged the box-RLCT-of-a-PSD-quadratic atom
as "the one genuinely-new piece"; it was ALREADY banked as
`RouteMSJRankRCodim.lintegral_cube_frobSq_neg_of_finrank_range` (genm-sj5, Brick D-B). So the thread's long
pole was done; what remained new was the RANK computation (no `rank_kronecker` in Mathlib v4.29) + the
finiteness instantiation.

---

> **Claim (a) — the matrix-multiplication-map rank.** For `A : Matrix (Fin c) (Fin d) ℝ`, the linear map
> `X ↦ X · A` on `Matrix (Fin r) (Fin c) ℝ` has `finrank (range) = r · rank A`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.finrank_range_matMulRight`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorLoss.lean` @ `a2fc2db6d`)
> - **Gloss.** Right-multiplication by a fixed `c×d` matrix `A`, viewed as a linear endomorphism of the
>   space of `r×c` matrices, has range of dimension `r · rank A` (each of the `r` rows independently
>   ranges over the `rank A`-dimensional row space of `A`).
> - **Proved.** The equality, over `ℝ`, unconditionally. Route: `X↦X·A = LinearMap.compLeft (mulVecLin Aᵀ)`;
>   `range_compLeft = Submodule.pi univ (fun _ => range)`; a constant-fibre `Submodule.pi` finrank
>   (`finrank_pi_submodule_const`, built here — Mathlib v4.29 lacks it) `= card · finrank`; `Matrix.rank Aᵀ = rank A`.
> - **Assumed.** none (network-free; arbitrary `A`).
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free.

> **Claim (b) — the interior loss box-RLCT finiteness.** For fixed `S : Matrix (Fin cW) (Fin n) ℝ`,
> `K : Matrix (Fin cC) (Fin n) ℝ` and `q ≥ 0` with `2q < rW·rank S + rC·rank K`, the integral over the
> unit two-matrix box `(W, C)` of `(frobSq(W·S) + frobSq(C·K))^{−q}` is finite.
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorLoss_twoMat_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJInteriorLoss.lean` @ `a2fc2db6d`)
> - **Gloss.** `∫⁻ (W,C) in matBox rW cW 1 ×ˢ matBox rC cC 1, ofReal((frobSq(W·S) + frobSq(C·K))^(−q)) < ⊤`
>   whenever `2q < rW·rank S + rC·rank K`. The loss `frobSq(W·S) + frobSq(C·K)` is a PSD quadratic in
>   `(W, C)` of rank `rW·rank S + rC·rank K`; its box-RLCT is `rank/2`, so the `−q` power is integrable
>   below the sharp threshold.
> - **Proved.** The finiteness, unconditionally in `S, K` (arbitrary matrices), for every `q` below the
>   sharp rank threshold. Pure instantiation of the banked `twoMatBox_rankR_lintegral_lt_top` at
>   `L = interiorLossL S K` (rank via (a), twice, through the block-diagonal `lossMapₗ`; integrand identity
>   `∑ⱼ (L (E (W,C)) j)² = frobSq(W·S)+frobSq(C·K)` via `sum_sq_twoMatFlatL` — the flatten preserves the
>   squared-sum).
> - **Assumed.** `2q < rW·rank S + rC·rank K` (the sharp rank threshold; `NeZero (rW·cW+rC·cC)`, i.e. the
>   variable space is nonempty). For the DLN interior cell (arch1build's bridge): `S = [Q_inl;Q_inr]`,
>   `K = Q_inl·(1−Π)`, `W = [P|B₁₂]`, and `rank S = min(M₁,ρ_d)`, `rank K = rank S − b` are corankrec's
>   cell-genericity facts (§w3-interior ★3), holding a.e. on the generic locus.
> - **Cited.** none (native; no `cited_aoyagi_dln`). Consumes the banked box-RLCT atom
>   `lintegral_cube_frobSq_neg_of_finrank_range` (genm-sj5, itself axiom-clean).
> - **Deferred.** This is PER-`p` finiteness; the bound is NOT uniform in `p` — the value blows up as
>   `[Q_inl;Q_inr]` loses rank (`~‖z0‖^{−(2q−ub)}` at the deep-degeneration locus; MC-witnessed,
>   `(4,4,4,4)@u=3`). The coupled `∫_p charge·loss < ⊤` (the (□) interior arm's actual obligation) is a
>   SEPARATE boundary estimate — couplerad's joint (x,p) monomial resolution — NOT this file, and NOT a
>   `(uniform D) × charge` factorization (that factorization is false; red-flagged + confirmed by arch1build).
> - **Structure & ideas observed.** The interior loss DECOUPLES (couplerad §w3-interior ★1): `E_tr` is
>   pure-`C` because `Q_inr·(1−Π) = 0`, so `f = E_top ⊕ E_tr` is block-diagonal in `([P|B₁₂], C)`, giving
>   the additive rank `u·r_stack + a·r_K`. The rank identity `finrank(range(X↦X·A)) = (#rows)·rank A` is the
>   Kronecker fact `rank(I⊗Aᵀ) = (#rows)·rank A` realized without `rank_kronecker` (absent at v4.29) via the
>   `compLeft` / `Submodule.pi` route.
> - **Route.** couplerad §w3-interior (decoupling + rank + box-RLCT) + the banked genm-sj5 atom; the rank
>   computation and the two-matrix-box instantiation are this thread's.
> - **Status.** sorry-free.

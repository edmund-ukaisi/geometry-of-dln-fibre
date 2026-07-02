# Statement card — `interiorLive_abs_det'Gen` (interior atom, layer (a))

> **Claim.** For a general-`L` admissible interior dimension vector `M : Fin (L+1) → ℕ`
> (`ha : StructAdm M (tach M)`, `hL : 0 < L`, nonempty leaf boundary `h0r : 0 < Text M (tach M) L`,
> `h0c : 0 < Wext M L`), the interior LIVE-leaf ∘ kLDU achiever chart `interiorLivePhiGen` has
> absolute Jacobian determinant equal to the single-axis monomial
> $\lvert\det D\varphi(u)\rvert = \prod_j \lvert u_j\rvert^{\text{leafHGen}(j)}$,
> where `interiorLive_leafHGen` places `minAdm−1` on the binding pivot axis and, on each interior
> boundary's diagonal K-axis `diagAxisGen k i`, the exponent `(r_k+c_k)+2(t_k−1−i)` with
> `t_k=Text(k+2)`, `r_k=Text(k+1)−Text(k+2)`, `c_k=Wext(k+1)−Text(k+2)`; `0` elsewhere.
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorLive_abs_det'Gen`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenDetDecode.lean` @ `1bc77fc1`)
> - **Gloss.** `|LinearMap.det (fderiv ℝ (interiorLivePhiGen M ha hL h0r h0c) u).toLinearMap|
>   = ∏ j, |u j| ^ (interiorLive_leafHGen M ha hL h0r h0c j)`. The general-`L` lift of the
>   `Fin (2+1)`-pinned, boundary-0-only `RouteMInteriorLiveAtom.interiorLive_abs_det'`; the
>   single-axis monomial the R1-LOWER leg consumes.
> - **Proved.** The full equation, unconditionally in `u`, for every admissible interior `M` (any
>   `L ≥ 1`). Assembled from the banked `DtotGen_abs_det` (Factor 1: boundary-factor Schur staircase
>   det, `∏_s |det (readK · s)|^{r_s+c_s}`) × `kLDU_ambient_det_pbo_gen` (Factor 2: ambient LDU lens
>   det, `∏_k ∏_i |u(diagAxisGen k i)|^{2(t_k−1−i)}`), merged per pivot by `lhs_collapse_multiboundary`,
>   the diagonal K-axis exponents matched by `leafHGen_diagAxisGen`, then the injective Sigma reindex
>   `diagAxisSigmaGen` (`diagAxisSigmaGen_injective`) + off-image collapse
>   (`mem_image_diagAxisSigma_of_leafHGen_ne_zero`) recovering `∏_{j ≠ leafPivot}`, and the radial
>   `|u leafPivot|^{minAdm−1}` (via `radialComp_abs_det_at`) filling the pivot slot.
> - **Assumed.** `hL : 0 < L`, `h0r : 0 < Text M (tach M) L`, `h0c : 0 < Wext M L` — the genuine
>   interior-stratum data (positive depth + nonempty leaf boundary). No `hreg` gate (the L=2 version
>   carried one; `DtotGen_abs_det` already discharged the regauge unconditionally).
> - **Cited.** none. Axiom profile of `interiorLive_abs_det'Gen` = `[propext, Classical.choice,
>   Quot.sound]` (clean-three, no `sorryAx`, no cited axiom).
> - **Deferred.** none for this statement. It is layer (a) of the interior atom; layer (c) (#281,
>   the box-divergence atom consuming this monomial) is downstream and separate.
> - **Route.** Controller's genm-glift ladder: Factor 1 × Factor 2 → `lhs_collapse_multiboundary`
>   → the `diagAxisGen ↔ leafHGen` Sigma reindex → `radialComp_abs_det_at`. All inputs banked on
>   `5415aa2b`; the reindex glue (`diagAxisSigmaGen_injective`, `leafHGen_diagAxisGen`,
>   `mem_image_diagAxisSigma_of_leafHGen_ne_zero`) built fresh in this module.
> - **Status.** sorry-free + reviewed.

## Machine-`.val` fidelity (item-123)

Verified at the concrete general-`L` instance `M = ![2,4,3,2] : Fin (3+1) → ℕ` (L=3, three
boundaries), NOT by "looks-right" assertion:

- `diagAxisSigmaGen` injective: `(Finset.image (diagAxisSigmaGen M ha) univ).card =
  Fintype.card (Σ k : Fin 3, Fin (Text M (tach M) (k.val + 2)))` — image card = domain card, so the
  reindex neither collapses nor double-counts (the prior flatten X↔N-swap failure mode is
  machine-ruled-out).
- `leafHGen_diagAxisGen` re-derived at the concrete `M`: the decode `.val` maps land on the diagonal
  `(i,i)` K-tag at every boundary `k`, giving exactly `(r_k+c_k)+2(t_k−1−i)`.

## Review

Independent fidelity review (reviewer teammate, + decorrelated Codex at xhigh on the reindex):
**PASS** on all five items — faithful lift of the L=2 template, correct exponent, sound reindex
(injective onto the nonzero-exponent support, no dropped/double-counted axis, no `.val` tag swap),
non-vacuous, axiom-clean. Only cosmetic style-linter nits (long lines, `show`→`change`), no semantic
issue.

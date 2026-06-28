# Sub-tide 2b GRADING SPEC — the opaque-width Jacobian determinant route (spec-first gate)

Branch `genm-interior` @30e4eca9. The focused design pass on 2b's grading, gated before deep-fill.
Decorrelated: Codex xhigh (`codex/item3-2b-grading-{prompt,answer}.md`). Verified against the (3,3,3,3)
det machinery (`RouteM3333Atom` `frameB`/`K7sub`, `RouteM3333Det` `B_det3333`).

## THE CHART + THE MONOMIAL DECOMPOSITION (verified exact at (3,3,3,3))
phi = paramsEquivFlat ∘ chartParamsGen ∘ kLDU. The target monomial decomposes EXACTLY as:

  |det Dφ| = |u_p|^{minAdm−1} · ∏_{boundaries s} ( |det K_s|^{r_s + c_s} · (LDU-pivot monomial of K_s) )

where under kLDU each K_s is read via the LDU lens so det K_s is ITSELF a monomial in the LDU pivots.
VERIFIED at (3,3,3,3) (leafH = u0^5·u1^4·u4^2·u9^3, minAdm=6):
- u0^5 = |u_p|^{minAdm−1} (radial).
- boundary 1 (K-core 2×2, r=c=1): det K_1 = x1·x4 (LDU `[[x1,x1x2],[x1x3,x1x2x3+x4]]`), |det K_1|^{2} =
  x1^2 x4^2; times the LDU-core det (x1)^2 → x1^4 x4^2. ✓
- boundary 2 (K-core 1×1, r=1 c=2): det K_2 = x9, |det K_2|^{3} = x9^3. ✓ (this is Codex's flagged `z9^3`:
  RESOLVED — it is the boundary-2 K-pivot, NOT a missing factor. `B_det3333` `Bmat 2 = [x9; x10·x9]`.)
NO factor dropped; the decomposition is complete.

## THE GRADING (Codex-adjudicated): TWO-LEVEL, radial SEPARATED
- **OUTER — layer filtration, UPPER-triangular.** Rows = output layer `A_k`, cols = boundary-k' coords.
  `A_k = chainA(N_k, W_k, C(k+1))`, `C(k+1)` reads boundaries ≥ k+1 ⟹ `∂A_k/∂(boundary k') = 0` for k' < k.
  So the Jacobian is block-triangular over `b_layer : coord ↦ its layer`; det = ∏_k det(layer-k diagonal block).
  **CRITICAL CAVEAT (Codex): the radial `u = x_p` has ALL-LAYER dependence (via `u·Rmat`/`u·Rfin` in every
  `C`), so it MUST be factored out as a separate front factor — if left as an ordinary layer coord it breaks
  the clean layer grading.** Hence the radial-extraction below is a PREREQUISITE, not optional.
- **INNER — per layer k:** the layer-k diagonal block (future `C` held fixed) differentiates
  `A_k = chainA(N_k, W_k, C(k+1))`; its det = `|det K_k|^{r_k+c_k} · LDU-monomial_k`, the banked
  `schurFrame_abs_det` × `lduCoreDeriv_det`. The chainA/chainQ shears are det-1 (unipotent — confirmed by the
  banked `chainChartFactor_abs_det = 1`); VERIFY `schurFrame_abs_det`'s kept/lift row ordering matches chainA's.

## THE RADIAL-EXTRACTION (the load-bearing prerequisite, (4,4,2,2)-precedented)
`chartParamsGen ∘ kLDU = normalizedChart ∘ pivotBlowupOn(active)(p) ∘ kLDU`, giving the clean front factor
|u_p|^{minAdm−1} and keeping the per-layer dets u-free. The (4,4,2,2) instance ALREADY did this for the
pure-radial case (`phi4422 = Q4422 ∘ pb4422`, `pb4422 = pivotBlowupOn {0,1,2,3} 0`); the active set is the
codim-minAdm blow-up coords. Must prove the factorization holds with the Schur/LDU layers present (the radial
commutes to the front because `u` enters only linearly via `u·Rmat`/`u·Rfin`, multiplying the residual
blocks that the blow-up's active set targets). This is the radial-separability Codex flagged earlier; (4,4,2,2)
is the witness it CAN separate.

## THE LEAN ROUTE (Codex ranking, least brittle first) — AVOID the global flat N×N matrix
1. **`det_comp` of per-layer insertion maps + the radial factor** [PREFERRED]: factor phi's structural part as
   a COMPOSITION `∘_k (layer-k insertion map)`, each layer-k map block-diagonal-with-identity-elsewhere, so
   det = ∏_k det(layer-k map) by `LinearMap.det_comp` — NO global grading, NO single N×N block-triangular
   matrix. paramsEquivFlat handled as det 1 (banked `measurePreserving` ⟹ det 1, generalize `Q3333CLM_abs_det`).
2. structured block-triangular BEFORE flattening (on layer/boundary product types) — fallback.
3. one global flat `Fin N` block-triangular through opaque chartIdxEquiv — AVOID (cast-heavy; chartIdxEquiv is
   Classical, not rfl). If unavoidable, prove off-block-vanishing by "unflatten, cancel Equiv.symm_apply_apply,
   apply the layer-dependency lemma" (the readK_wInt pattern), NEVER fin_cases / literal indices.

## DEPENDENT-FIN-CAST HANDLING (baked in)
The within-layer det reads K_s/the LDU pivots through `chartIdxEquiv.symm ∘ frameSplitEquiv.symm ∘
finProdFinEquiv` (Classical, opaque). Compute through it ONLY by `Equiv.apply_symm_apply` cancellation — the
witness file's `readK_wInt`/`readW_wInt` pattern (forward-decode the role slot so the round-trip cancels), then
the heterogeneous `Fin.cast` chain through `Text(k+2)`/`Wext(k+1)−Text(k+2)` block sizes. The per-layer-map
det_comp route (option 1) localizes this to ONE layer at a time, avoiding the global N-index cast fight.

## REVISED SUB-TIDE 2b PLAN (under the det_comp + radial route)
- 2b-i: the radial-extraction factorization `chartParamsGen ∘ kLDU = normChart ∘ pivotBlowupOn ∘ kLDU` ∀M
  (generalize the (4,4,2,2) `chartParams4422_eq_pack_pb`; the active set = codim-minAdm coords). The front
  factor |u_p|^{minAdm−1} via the banked `pivotBlowupOnDeriv_det`/`radialFactor_abs_det`.
- 2b-ii: the per-layer insertion-map factorization of `normChart` + det = ∏_k det(layer-k map) via det_comp.
- 2b-iii: the per-layer det = `|det K_k|^{r_k+c_k}·LDU-monomial_k` via `schurFrame_abs_det`+`lduCoreDeriv_det`
  (the within-layer dependent-Fin reads via apply_symm_apply).
- 2b-iv: paramsEquivFlat det = 1 (generalize `Q3333CLM_abs_det`); assemble the monomial.

## RECOMMENDATION
Grading SOUND (Codex-adjudicated, upper-triangular layer filtration; within-layer = banked Schur×LDU; z9^3
factor RESOLVED as the boundary-2 K-pivot — no dropped factor). The radial-extraction is the load-bearing
PREREQUISITE (Codex: radial must be a separate front factor or the layer grading breaks); (4,4,2,2) is the
witness it separates. Lean route: per-layer det_comp + radial front factor (option 1), AVOIDING the global
opaque-cast N×N matrix. Ready to open 2b deep-fill, starting 2b-i (the radial-extraction ∀M) — the highest-risk
piece (the separability proof with Schur/LDU layers present). Recommend a pen-and-paper `witness` adjudication
of the radial-separability over the design space BEFORE the Lean deep-fill, since it's the load-bearing claim.

## ROUTE CORRECTION (from the genm-radsep WITNESS certificate, 2026-06-28) — supersedes the pivotBlowupOn route
The radial-separability WITNESS landed (HOLDS ∀ interior M; exact sympy on anchors + L=4/L=5 multi-t≥2 +
structural proof + Codex). It carries a LOAD-BEARING route correction to §"THE RADIAL-EXTRACTION" above:

**DO NOT use `pivotBlowupOn ∘ normChart`.** Its "u-free normChart" premise is FALSE for general interior M:
`chartParamsGen` is u-dependent in EVERY layer; only the DETERMINANT's u-content collapses. (4,4,2,2) — where
one block carries all u³ — is the MISLEADING special case.

**USE the AFFINE-IN-u COMMON-COLUMN-FACTOR route** (cert, sympy-verified): the chart is AFFINE in u
(degree ≤ 1, NO u²; structural from `Cgen` linear in u: `C k = Bmat·chainQ + u·Rmat`, `C L = u·Rfin`, +
`chainA` affine in C(k+1)). Flattened: `Phi(u,h,z) = P(z) + u·r0 + u·Σ_a h_a·r_a` where `h_a` = the free
angular coords, `r_a` = fixed output directions. So:
  D_z Phi = D_z P(z) [u-free];  D_{h_a} Phi = u·r_a [angular column carries factor u];  D_u Phi = r0 + Σ h_a r_a [u-free].
Factor `u` from each of the `q = minAdm−1` angular columns ⟹ det = u^{minAdm−1}·G(z,h), ∂_u G = 0. The
per-layer u-powers ACCUMULATE to the front (3333: D_0→u^0, D_1→u^2, D_2→u^3 = u^5), NOT one block's prefactor.
The layer-filtration grading (2b) STILL HOLDS — det = ∏_k det D_k; the radial extraction WITHIN it is the
affine-in-u column factor. The `chainA` shear is unipotent (det 1, z-dependent entries only) so the `−N_k W_k`
shear cannot leak u into the cofactor; fixed interior R_k of ANY rank (incl. t≥2 coupling) cannot leak u.

**THE GENUINE 2b-i RESIDUAL (the real risk, per the cert + controller): the BUDGET IDENTITY** —
#free-coords = flatDim, with EXACTLY #angular = minAdm−1 free R_k/Rfin entries (the rest of R_k = fixed pivots;
one pivot = u; one Rfin pivot fixed = 1 → exponent active.card−1). Cert caveats: (i) inert B_0 free coords must
be fixed/discarded (else zero Jacobian columns, non-square); (ii) one Rfin pivot fixed = 1. This is the
dependent-Fin accounting / square-chart well-definedness over opaque widths — NOT the radial math, which is
settled. The sympy engine's `n != NC` (non-square) guard is exactly this budget check.

REVISED 2b-i: realize det J = u^{minAdm−1}·(u-free) via the affine-in-u angular-column factoring, WITHIN the
per-layer det_comp (2b-ii). The budget identity (#angular = minAdm−1, square chart) is the delicate piece —
spec it carefully before the column-factor deep-fill.

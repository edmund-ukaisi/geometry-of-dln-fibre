<task>
Lean 4 / Mathlib v4.29 (DLNFibre harness). I am scoping the ONE residual blocker for the fully-general
`routeMCore_box_diverges_achiever ∀M` atom: the general achiever-chart Jacobian determinant
`|det Dφ_{M,t}| = ∏_j |u_j|^{leafH j}`. A prior consult (yours, decorrelated) concluded this is a
"multi-week parametric Schur-frame/LDU determinant" and recommended shipping only the 3 anchor instances.
I have since done structural work that I believe COLLAPSES the cost, and I need you to red-team that,
NOT re-confirm the prior pessimism.

## State of the art (banked, sorry-free)
- The RATE identity `routeMCore M (φ_{M,t} u) = u²·V` is banked ∀M (`routeMCore_phiGen`), for the ABSTRACT
  chart `phiGen := paramsEquivFlat M ∘ chartParamsGen`, where `chartParamsGen`'s layers are
  `A k = chainA(N_k)(W_k)(C(k+1))` — built from abstract `chainA`/`chainQ` matrix reindexes (network-product
  algebra), NOT a flat-coordinate frame product. So `phiGen` has NO clean flat fderiv; the radial `u` is a
  scalar argument, the block data `B` is opaque.
- The det-FREE NodeAchieverChart fields (`leaf_integrand`, `V≥0`) are banked ∀M (`RouteMGenLeafIntegrand`).
- The (3,3,3,3) anchor `phi3333 = Q3333 ∘ Frame3333 ∘ Kparam3333` is built ENTIRELY as explicit flat
  `(Fin 27→ℝ)→(Fin 27→ℝ)` maps with HAND machinery: a literal SCC-grading `frameB : Fin 27 → ℕ`, a hand
  7×7 K/Kᵀ coupling block, a 27-coord triangular injOn. This is NOT a lift.
- Banked det-telescope: `general_composed_clm_abs_det (N) (fs : List CLM) (m) (hfac) : |det fs.prod| = m.prod`
  — telescopes a List of full-ambient CLMs GIVEN their per-factor dets.

## My NEW structural finding (sympy-confirmed, decorrelated from your prior answer)
The cert's per-boundary atomic Schur map S(X,K,N,E) = [[K, K N],[X K, X K N + E]] (K: t×t FULL free entries,
X: r×t, N: t×c, E: r×c) is a SQUARE chart of the (t+r)×(t+c) matrix space (#inputs = t²+rt+tc+rc =
(t+r)(t+c) = #outputs). I computed its DIFFERENTIAL as a linear map on increments (dX,dK,dN,dE) and found
it is BLOCK-LOWER-TRIANGULAR in the natural pairing (output blocks TL,TR,BL,BR) ↔ (inputs dK,dN,dX,dE):
  dA_TL = dK                          (diag block: identity,       det 1)
  dA_TR = K·dN  + [dK·N]              (diag block: dN ↦ K·dN,      det (det K)^c)
  dA_BL = dX·K  + [X·dK]              (diag block: dX ↦ dX·K,      det (det K)^r)
  dA_BR = dE    + [X·dK·N + X·K·dN + dX·K·N]   (diag block: identity, det 1)
the bracketed terms are STRICTLY lower-triangular couplings (don't affect det). So
  |det DS| = 1 · (det K)^c · (det K)^r · 1 = |det K|^{r+c}.
Verified symbolically for (t,r,c) ∈ {(1,1,1),(2,1,1),(1,2,1),(1,1,2),(2,2,2),(2,1,2),(2,2,1),(1,2,2),(3,1,1),(3,2,1)}:
block-lower-tri holds AND det = (det K)^{r+c} in every case.

Crucially, this means the det does NOT need a per-instance SCC `frameB` grading. The two nontrivial diagonal
blocks are "left-mult-by-K" on `Matrix (Fin t) (Fin c) ℝ` and "right-mult-by-K" on `Matrix (Fin r) (Fin t) ℝ`,
whose dets are `(det K)^c` and `(det K)^r` — and in Mathlib v4.29 BOTH are instances of `LinearMap.det_pi`
(det of `c` (resp `r`) independent copies of `K.mulVecLin` acting columnwise/rowwise = ∏ (det K) = (det K)^c),
composed with `det_conj`/`det_submatrix_equiv_self` to land on the matrix-space basis. I have confirmed these
Mathlib lemmas EXIST: `LinearMap.det_pi`, `LinearMap.det_comp`, `LinearMap.det_conj`, `Matrix.det_blockDiagonal`,
`LinearMap.det_toLin'`, `Matrix.BlockTriangular.det`, `Matrix.det_fromBlocks_zero₁₂`/`₂₁`,
`Matrix.det_submatrix_equiv_self`.

## The two ROUTES to wire this into NodeAchieverChart.phi
(a) Keep the abstract `phiGen` (banked rate transfers for free via `routeMCore_phiGen`), and somehow compute
    `det Dφ_{M,t}` directly from the `chainOfMt` structure. PROBLEM: `phiGen`'s layers are abstract
    `chainA`/`chainQ` reindexes with a SCALAR radial u and opaque block data — there is no flat fderiv to
    differentiate; you'd have to reify all GenBlk entries as source coords first, which IS the
    coordinatization problem. My read: (a) is the harder route — the abstract chart can't be differentiated
    as-is.
(c) Re-architect: build a NEW flat chart `φ_flat,{M,t} : (Fin N→ℝ)→(Fin N→ℝ)` as a List.prod of CLM factors
    [radial blow-up] ∘ [per-boundary Schur frame, parametric in (t_s,r_s,c_s)] ∘ [per-boundary LDU core],
    get `|det Dφ_flat| = ∏|u_j|^{leafH j}` via `general_composed_clm_abs_det` over the per-factor dets
    (each Schur factor's det = |det K_s|^{r_s+c_s} via the block-triangular lemma above; LDU factor's det =
    ∏|q|^{2(t-i)}; radial = |u|^{D-1}), THEN re-derive the chart identity `routeMCore M (φ_flat u) = u²·V`
    for φ_flat — either by proving `φ_flat = phiGen` (so the banked `routeMCore_phiGen` transfers) or
    re-proving it directly on φ_flat.

## QUESTIONS (be skeptical, concrete; do NOT default to "multi-week")
1. Given the block-triangular collapse (no `frameB`, det = `det_pi`-of-left/right-mult), is route (c) now a
   BOUNDED build broken into ~6-10 scoped Lean lemmas, or is there a hidden cost I'm missing? Identify the
   single riskiest sub-piece.
2. For route (c), is it cheaper to (i) prove `φ_flat = phiGen` and transfer the banked rate identity, or
   (ii) re-prove `routeMCore M (φ_flat u) = u²·V` directly on φ_flat via the same telescope? The
   identity-transfer needs a per-entry equality of two differently-built `Params M`; the re-proof reruns the
   telescope. Which is less Lean?
3. The `injOn` for `cov`: the (3,3,3,3) version is a 27-`have` triangular recovery. With the parametric
   Schur frame, is `injOn` off the bad axes obtainable structurally (each factor is a diffeo on the sector
   where its K is invertible, so the composition is injective on the intersection) — i.e. an `InjOn.comp`
   chain over the List of factors, each factor's injectivity from its block being a bijection? Or does it
   still need per-coordinate recovery?
4. The "prefix pullback" wrinkle you flagged before (factor i's det is evaluated at the output of previous
   factors, like `Frame3333Deriv (Kparam3333 u)`): does my List-of-CLM-factors framing need a
   ChartFactor-with-prefix-evaluation structure, or does the fact that each factor's |det| is a MONOMIAL in
   that factor's OWN K-block coords (which are unchanged by the LDU/radial substitutions up to the
   |det K_s| = ±(spectator monomial) pullback) let the telescope stay a flat List.prod with a clean
   substitution at the end?
5. Net recommendation: route (c) vs (a) vs a hybrid, and is the keystone the parametric Schur-frame det
   theorem (matrix-indexed `|det DS_{t,r,c}| = |det K|^{r+c}`) or the φ_flat = phiGen identity transfer?
</task>

<output_contract>
Five numbered answers matching Q1-Q5. For Q1: a yes/no on "bounded build" + the single riskiest sub-piece
named. For Q5: a one-line route recommendation + the named keystone. Be concrete about Lean lemma names and
the Mathlib API where you can. Flag any place my structural claim might be wrong (e.g. the block-triangular
reading failing for some degenerate r_s=0 or c_s=0 boundary, or det_pi not applying to the matrix-space
left-mult as cleanly as I claim).
</output_contract>

<grounding_rules>
Distinguish what you can verify from the math/API I've stated vs what is inference. If you think a sub-piece
is harder than I claim, say which Mathlib gap or cast-hell makes it so, concretely. Do not invent Mathlib
lemma names; if unsure a lemma exists, say "verify X exists".
</grounding_rules>

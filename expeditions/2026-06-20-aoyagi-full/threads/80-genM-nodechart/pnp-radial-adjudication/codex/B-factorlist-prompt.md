<task>
Finalize the factor-list structure of a "de-radialized chart" map B for a Lean determinant proof.
B : R^N -> R^N is the boundary part of a structured DLN achiever chart phi = B ∘ pivotBlowupOn(active,p).
We must pin: (i) B's exact factor list as a composeFold of banked per-boundary ChartFactors, and
(ii) whether the map-identity phi = B ∘ pivotBlowupOn reduces to banked per-block value lemmas or needs
a new lemma, with its forall-M shape. Derive structure yourself; the sympy facts below are exact.
</task>

<banked_factor_maps>
Three banked nonlinear/linear factor MAPS on per-boundary block spaces, each with HasFDerivAt + abs-det:
- schurFrameMap (X,K,N,E) := (K, K·N, (X·K, X·K·N + E))   [the Schur frame; E un-scaled]   |det D| = |det K|^(r+c)
- lduCoreMap (l,q,u) := matrixSplit((1+L(l))·diag(q)·(1+U(u)))   [coordinatize K = LDU]    |det D| = ∏_i |q_i|^{2(t-1-i)}
- chainUnitCLM N : (W,C) ↦ (W, C - N·W)   [linear det-1 chaining shear]                    |det D| = 1
Each is conjugated to a FULL-AMBIENT ChartFactor N via a per-factor CLE E : (Fin N -> R) ≃L (block × R),
with banked _abs_det reading the block off (E u).1. composeFold_abs_det telescopes a ChartFactor-list
composition to the product of per-factor abs-dets.
</banked_factor_maps>

<chart_structure_exact_sympy>
The chart phi is built from a chain decoder over boundaries s=0..L-1 (s=0 the identity boundary, no content):
  C_L = u·Rfin ;  C_k = Bmat_k·chainQ(N_k) + u·Rmat_k ;  A_k = [ C_{k+1} - N_k·W_k ; W_k ].
Here Bmat_k·chainQ(N_k) + u·Rmat_k = the Schur frame [[K_k, K_k N_k],[X_k K_k, X_k K_k N_k + u·E_k]]
(verified exactly at N=8 and N=27: RouteMSchurValue's schurFrameProd_block_K/_KN/_XK/_XKNuE are banked
matrix-value identities Bmat·chainQ + u·Rmat = [[K,KN],[XK,XKN+u·E]]).
B is phi DE-RADIALIZED: the u·E_k becomes E_k (un-scaled) and u·Rfin becomes the leaf read directly, with
the bare-pivot fixed-1 anchor reading the pivot coordinate y_p.
Verified exactly at N=27: |det DB| = (per-boundary product) ∏_s |det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s-1-i)},
u-free; and the per-boundary triple decomposition (schur·ldu·chain) reproduces it.
</chart_structure_exact_sympy>

<questions>
1. Given the per-boundary frame [[K,KN],[XK,XKN+E]] = schurFrameMap output, K coordinatized by lduCoreMap,
   and the chaining A_k = [C_{k+1}-N_k W_k ; W_k] = chainUnitCLM applied to (W_k, C_{k+1}): what is the EXACT
   factor list (order) of B as a composeFold of [schur_s, ldu_s, chain_s] over boundaries? Within one boundary,
   is the order ldu (innermost, builds K) -> schur (builds the frame) -> chain (lifts C into next layer)? And
   across boundaries, deepest (s=L-1) first or last in the fold? Give the precise composeFold list ordering so
   the prefix-evaluation (each factor's deriv at the output of factors to its right) is correct.
2. The per-boundary CLE E for each ChartFactor reads its block off (E u).1. The Schur factor needs E_schur:
   (Fin N -> R) ≃L SchurInc t r c × R; the LDU factor E_ldu: ≃L LDUParam t × R; the chain factor E_chain:
   ≃L (W-block × C-block) × R. These E's must be consistent with the chart's ACTUAL coordinate slots
   (the chartIdxEquiv per-boundary frame/lift slots). Is the right E per boundary just the existing
   chartIdxEquiv composed with the frameSplitEquiv role-split (i.e. reuse the banked coordinatization), or
   does each factor need a bespoke E? Reason about whether one global chartIdxEquiv-derived family of E's serves
   all three factor types per boundary.
3. The map identity phi = B ∘ pivotBlowupOn(active,p): given the banked schurFrameProd_block_* (the matrix
   VALUE identity Bmat·chainQ + u·Rmat = [[K,KN],[XK,XKN+u·E]]) and that pivotBlowupOn multiplies the active
   E/leaf coords by u, does phi = B ∘ pivotBlowupOn reduce to: (a) the banked block-value identities +
   (b) the observation "u·E_k = E_k evaluated at the blown coord", i.e. NO new deep lemma — just per-boundary
   per-block value equalities? Or is there an irreducible NEW map-equality lemma needed? State its forall-M shape
   (per-boundary, per-block) and whether it is the same GRAIN as the banked schurFrameProd_block_* lemmas.
</questions>

<output_contract>
For each question a direct answer. Q1: the exact ordered composeFold list (per-boundary triple + cross-boundary
order). Q2: verdict on whether chartIdxEquiv-derived E's serve, or bespoke E needed. Q3: verdict reduces-to-banked
vs new-lemma, + the forall-M per-block shape. Mark proof vs heuristic.
</output_contract>

<grounding_rules>
Reason from the chain/Schur-frame structure. sympy facts exact. Don't rubber-stamp; if the cross-boundary
prefix-evaluation forces a subtle ordering or an extra reindex, flag it.
</grounding_rules>

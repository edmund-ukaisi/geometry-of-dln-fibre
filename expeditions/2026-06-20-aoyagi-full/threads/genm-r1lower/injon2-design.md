# injOn#2 (`interiorLive_BparamsLeaf_injOn`) — Route A design (block readback, L=2)

## Verdict: Route A (explicit left-inverse on the slot blocks). Complete + well-defined.

`chartIdxEquiv : Fin (routeMAmbient M) ≃ ChartIdx M t` is a FULL Equiv (RouteMChartSlots:13), with
`ChartIdx = Σ k:Fin L, Fin(schurDim k) ⊕ Fin(liftDim k)`. So EVERY coord of `y` is read by exactly one
reader. At L=2 the slots are:
  - boundary k=0 schur slot: K/X/N/E ⟨0⟩ (the Schur frame, `schurDim 0`)
  - boundary k=0 lift slot:  W ⟨0⟩ (`liftDim 0`)
  - boundary k=1 schur slot: the leaf residual (`schurDim 1`); liftDim 1 = 0 (k+1=2 ≮ L=2)

## What the two chart-layer matrices expose

`BparamsLeaf ha y = chartParamsGen 1 (genBlkFlatLive (rfinDirect y) y)`; layer `s` = reindex(`Agen 1 B_y s.val`),
reindex by value-preserving finCongr ⟹ `BparamsLeaf y = BparamsLeaf y'` ⟹ `Agen 1 B_y k = Agen 1 B_{y'} k`
for k ∈ {0,1} (peel reindex via finCongr injectivity, OR just read entries — the readers are entry-wise).

`Agen 1 B k = chainA(genWidthEq k)(N_k)(W_k)(C(k+1))`, vertical block `[ C(k+1) − N_k W_k ; W_k ]`
(`chainA_apply_castAdd` = kept = C−NW; `chainA_apply_natAdd` = lift = W). Banked entry laws.

  - **Agen 0**: N_0 = Nblk 0 = 0, W_0 = Wblk 0 = 0 ⟹ Agen 0 = [ C_1 ; 0 ]. Kept block = `C_1`.
    `C_1 = Cgen 1 = Bmat(1)·chainQ(N_1) + Rmat(1) = schurFrameProd(K,X,N,E)` (reader ⟨0⟩) =
    `[[ K, K·N ],[ X·K, X·K·N + E ]]`.
  - **Agen 1**: lift block (natAdd rows) = `W = readW ⟨0⟩`. Kept block (castAdd rows) = `rfinDirect − N·W`,
    with N = readN ⟨0⟩, W = readW ⟨0⟩ (SAME readers as C_1's N and the lift). Leaf C_2 = Rfin 2 = rfinDirect y.

## The readback chain (recover each reader value, then funext on chartIdxEquiv)

1. **K = readK ⟨0⟩**: top-left Text(2)×Text(2) block of `C_1`. Direct.
2. **N = readN ⟨0⟩**: `C_1` top-right = K·N. On D, K invertible (kLens form `(1+L)diag(q)(1+U)`, q≠0)
   ⟹ N = K⁻¹·(K·N). [Or: match via the equality K·N = K'·N' + K=K' ⟹ N=N' by `mul_left_cancel` on the unit.]
3. **X = readX ⟨0⟩**: `C_1` bottom-left = X·K ⟹ X = (X·K)·K⁻¹ (K invertible). [Or right-cancel.]
4. **E = readE ⟨0⟩**: `C_1` bottom-right = X·K·N + E ⟹ E = (br) − (X·K)·N (X·K and N already matched).
5. **W = readW ⟨0⟩**: `Agen 1` lift block. Direct.
6. **leaf = rfinDirect y = Rfin 2**: `Agen 1` kept block + N·W ⟹ rfin = kept + N·W (N, W matched).

KEY simplification: I do NOT need explicit K⁻¹. Since I prove block-EQUALITY `block(y) = block(y')`, the
products give: K=K', K·N = K'·N' ⟹ (K=K') K·N = K·N' ⟹ N=N' by `mul_left_cancel₀`/`Matrix.mul_left_inj`
using K a UNIT (K invertible on D). Likewise X·K = X'·K' ⟹ X=X' by right-cancel. So the ONLY fact I need
is **K = readK ⟨0⟩ y is invertible (IsUnit / right+left cancel) on D**. Then E, W, leaf are direct adds.

## The K-invertibility on D  [CORRECTED per Codex xhigh]

`y = kLDU z`, `z = pbo x`, `x ∈ injDom`. `det(readK y ⟨0⟩) = readK_kLDU_det = ∏ i (matrixSplit(readK z
⟨0⟩)).2.1 i`. Each factor `(matrixSplit(readK z ⟨0⟩)).2.1 i = (readK z ⟨0⟩) i i = z(K-diag-slot)`, a
SINGLE coord of `z = pbo x`, nonzero (pbo of an all-nonzero injDom point). So `∏ ≠ 0` ⟹ K nonsingular.

CORRECTION (Codex): do NOT try "all coords of y nonzero AFTER kLDU" — that can fail by cancellation
inside `(1+L)·diag(q)·(1+U)`. What holds and what's needed is only `det(readK y ⟨0⟩) ≠ 0`, via the
PRE-kLDU K-DIAGONAL coords being nonzero (those are individual `z`-coords, not lensed combinations).

## ACTUAL BUILT ROUTE (packed Route A, reusing genm-ambdet's `eIn`/derivative machinery)

Rather than peel raw `chainA` indices, reuse the banked objects from `RouteMHDtotEihd` / `RouteMProjV0Gate`:
  - `schurFrameMap_inj_of_det_ne_zero` (NEW, mine): the readback algebra on `SchurInc` (K=K', N=N'
    left-cancel, X=X' right-cancel, E=E'). Only invertibility fact needed: `K.det ≠ 0`.
  - `slotReadV0_K_det_ne_zero_of_mem` (NEW, mine): K-det≠0 on D (above).
  - `slotReadV0_eq_of_BparamsLeaf0_eq` (NEW, mine): V0 recovery via `reindexL0_BparamsLeaf0` (banked) +
    `flatBlockLE`.injective + the readback lemma. Recovers (K,N,X,E).
  - `Wfun_Lfun_eq_of_BparamsLeaf1_eq` (NEW, mine): V1 recovery via `rsL1_BparamsLeaf1` (banked). W direct,
    leaf = kept + N·W (N from V0).
  - `Nfun_eq_slotReadV0` (NEW, mine): the `Nfun = slotReadV0.2.1` bridge.
  - assembly: `eIn ha y = eIn ha y'` (V0 via `eIn_projV0`, V1 via `dWdC_eq_eInV1`, PUnit tail `rfl`),
    then `(eIn ha).injective`.
All axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Build order (incremental, bank each)
  a. `interiorLive_K_isUnit`: K = readK⟨0⟩ y invertible on D (det ≠ 0 via kLens_det + q≠0).
  b. block-extraction lemmas: from `Agen 1 B_y k = Agen 1 B_{y'} k` peel C_1 / W / kept blocks (chainA entry laws).
  c. C_1 Schur-frame readback: K=K', N=N', X=X', E=E' (using K unit + cancel).
  d. W match (direct), leaf match (kept + N·W).
  e. funext on chartIdxEquiv: assemble all reader matches ⟹ y = y'.

## Risk flags
  - The reindex peel: `chartParamsGen` value is `reindex (finCongr…) (finCongr…) (Agen…)`. To go from
    `BparamsLeaf y = BparamsLeaf y'` to `Agen … = Agen …` I peel `reindex` (a `submatrix` by Equivs,
    injective). Alternatively work ENTRY-WISE: `BparamsLeaf y s i j = BparamsLeaf y' s i j` ⟹ pick the
    entries that ARE the reader values. The entry-wise route avoids reindex algebra. PREFER entry-wise.
  - The K-unit cancel on dependent-width matrices (`Matrix (Fin (Text 2)) (Fin (Text 2))`): need
    `Matrix.mul_left_cancel` form, i.e. K unit ⟹ K * N = K * N' → N = N'. Mathlib:
    `(Matrix.mul_right_inj_of_invertible)` / via `K⁻¹` left-mult. Have IsUnit → invertible instance.

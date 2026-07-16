# T2 — crux→shell BRIDGE adjudication (`shellSpine_le_hsQ_box`)

**Seat:** pen-and-paper (obstruction, decorrelated), aoyagi-full Stage 2, `genm-t2adjud`.
**Date:** 2026-07-14. **NO Lean, NO build.** Exact algebra (spectral invariants, exact
homogeneous-singularity codimension thresholds) + decorrelated `local-codex-consult` (xhigh, my
conclusion WITHHELD): `codex/bridge-{prompt,answer,run.log}.md`.

**Adjudicated against** branch `origin/genm-sj5-step2 @e395121c`: `RouteMSJHeadSplitDom.lean`
(`pivotShell` L63, `hsSplit_good_of_shell` L182, `shellSpine_le_hsQ_box` L210 = the sorry),
`RouteMSJPivotDom.lean`, `RouteMSJPivotFin.lean` (crux `pivotPeel_domination` L1240, sorry-free),
`RouteMSJChartShear/ChartWeld.lean` (`freedSchurLoss`/`schurLoss`), `RouteMSJShellCover/Contain.lean`,
`RouteMSJDeeperFlagCore.lean` (L1 `deeperFlag_shell_core_le` sorry-free; Brick D stub L513). Cross-read
`genm-couplingfin/coupling-verdict-cert.md`.

---

## ★ VERDICT — the bridge has a genuine OBSTRUCTION for `j ≥ 1`; it is sound only for `j = 0`.

`shellSpine_le_hsQ_box` as stated (RHS integrated over `matBox ∩ pivotShell`) is **FALSE for `j ≥ 1`**
and is **NOT** "pure measure reorganization". It is sound for `j = 0` (shell-0 = pivotShell exactly).
The `pivotShell` was **mis-identified** with the Ky-Fan "good set"; the actual Ky-Fan reduction lands in
the **deep-factor** good set, not `pivotShell`. **Signature verdict: `hfloor`/`U_sf` ARE load-bearing
(the controller's strip must be reversed), AND the `pivotShell` restriction must be removed** (RHS → full
`matBox`; the domination then routes through the deep-factor floor / S3, not the whole-block floor).

---

## 1. The objects, verified against the code (not paraphrase)

- `hsQ M u Zf z A_cor = fromRows( (prod(redChain u M) z) ; A_cor·Zf z )` is `Matrix (Fin u ⊕ Fin (M1−u))
  (Fin n)`, i.e. **`M1 × n` — the WHOLE front product** `W = prod(tailChain M) A'` reindexed. Rows
  `u + (M1−u) = M1` (since `u = t+j ≤ M1`). Pivot rows = `(κ-image rows of A'₀)·Z_deep`, corank rows =
  `A_cor·Z_deep`; on the shell `Zf z = Z_deep z` (via `hagree`). Row reindexing is a permutation ⟹
  **`hsQ` and `W` have identical singular values.**
- `pivotShell M u ε Zf z = {A_cor | hsQ·hsQᵀ ⪰ ε²·1}` = `{σ_min(hsQ) ≥ ε}` = `{weakEigCount ε hsQ = 0}`
  = **shell-0**, exactly (its own docstring L57 concedes "the `j=0` good set `G`").
- `singularShell ε r j = {W | min(weakEigCount ε W, r) = j}`; for `1 ≤ j < r`, `weakEigCount ε W = j ≥ 1`,
  so **`σ_min(W) < ε`**.
- `freedSchurLoss x Γ Q` (ChartShear L146) `= schurLoss(of(blockSplitD.symm(x, Γ+schurShift x))) Q`
  (`schurLoss_of_blockSplitD_symm_shift`) and on the chart `schurLoss B Q = frobSq(B·Q)`
  (`frobSq_schur_split_inv`, ChartWeld). `blockFront_inner_eq` (PivotFin L541) reassembles the inner
  `(x,Γ/D)`-integral to `∫ frobSq(of B · Q)^(−c')` over the `M0×M1` front block box.

⟹ **Both sides reduce to the SAME integrand** `G(Q) := ∫_{T∈[−1,1]^{M0×M1}} frobSq(T·Q)^(−c') dT`,
differing only in the integration DOMAIN: LHS over `{weakEigCount ε W = j}`, RHS over
`matBox ∩ {weakEigCount ε hsQ = 0}`.

## 2. The obstruction (exact)

The change of variables `hsSplit` is measure-preserving and `weakEigCount` is a **spectral invariant**
(unchanged by the row permutation and by Tonelli/row-split). Hence `hsSplit` maps
`{W ∈ singularShell ε r j}` bijectively onto `{(z,A_cor) | weakEigCount ε hsQ = j}`, which for `j ≥ 1`
is **DISJOINT** from `pivotShell = {weakEigCount ε hsQ = 0}`.

- **The claimed proof method cannot work.** Dropping the shell indicator with `≥ 0` gives
  `shellSpineIntegrand(shell-j) ≤ ∫_{matBox} G` (the FULL box) — **not** `≤ ∫_{matBox ∩ pivotShell} G`.
  To reach the stated RHS one needs `1_{wec=j} ≤ 1_{wec=0}`, false for `j ≥ 1`. No measure-preserving
  reorganization can replace one disjoint spectral stratum by another. (Codex Q1 concurs, independently.)

- **The inequality is false as a real statement.** `G(Q)` is finite iff `c' < M0·(M1−k)/2`, `k = corank
  of Q` (exact homogeneous-singularity codimension `M0(M1−k)`, certified `scripts`-free by the radial
  exponent `M0(M1−k) − 1 − 2c' > −1`). On `pivotShell` (`σ_min ≥ ε`, `k = 0`) `G` is BOUNDED and finite
  for `c' < M0·M1/2`. On shell-`j` (`j` singular values `→ 0`) `G` is UNBOUNDED: `G ~ C·σ_min^{−1}` as
  `σ_min → 0` (MC guide `G·σ_min → 41–46` const at `M0=M1=2, c'=3/2`). The rank-`(M1−j)` stratum sits in
  the closure of shell-`j`, where `G = +∞` once `c' ≥ M0(M1−j)/2 < M0M1/2`. **Concrete refuter**
  (`M0=M1=M2=n=2, Z=I, j=1, 0<ε<1, c'=3/2`): RHS finite (`3/2 < M0M1/2 = 2`), LHS `= ∫₀^ε σ⁻¹dσ = +∞`.
  So `LHS ≤ RHS` is `∞ ≤ finite` — FALSE. (Codex Q2 produced this same counterexample independently.)

## 3. What the crux actually proves — and its scope

`pivotPeel_domination` (full-block route, S3-free, approved 2026-07-14) proves `pivotDomLHS ≤ C·RHS` where
`pivotDomLHS = ∫_{matBox ∩ pivotShell} G`. Its floor `shell_fullBlock_le` uses `frobSq(T·Q) ≥ ε²·frobSq(T)`
(`frobSq_mul_ge_of_gramFloor`), which genuinely needs `σ_min(hsQ) ≥ ε`. Its own docstring (L1238) states
`hfloor`/`U_sf`/`hcvg` are **UNUSED**. So the crux is a **shell-0-only** result — it bounds the
well-conditioned sub-region and says nothing about the near-singular region where the `j ≥ 1` shells live.
It is SOUND but its scope is `pivotShell = shell-0`; it does not connect to `shellSpineIntegrand(shell-j)`
for `j ≥ 1`.

## 4. The correct floor-factorization (the deep-factor floor, already built)

Ky-Fan (`shell_subset_goodSet`, sorry-free in `RouteMSJShellContain`) shows: on shell-`j`, the DEEP factor
retains a strong `m`-frame, `m = min(M1,n) − j`:
`weakEigCount ε' Z_deep ≤ M2 − m`, i.e. `Z_deep Z_deepᵀ ⪰ ε'²·(U_s U_sᵀ)` for an orthonormal `M2×m`
`U_s`, `ε' = ε/√(M1·M2)`. This is the floor `hfloor`, on the **deep factor** (M2×n), NOT on `W`/`hsQ`.
`W = A'₀·Z_deep` can create `j` weak directions while `Z_deep` keeps `m` strong ones. The correct route:

1. **Corrected bridge** `shellSpineIntegrand ≤ ∫_{z}∫_{A_cor ∈ matBox}∫_x∫_Γ freedSchurLoss(hsQ)^(−c')`
   — RHS over the **FULL `matBox`** (drop `pivotShell`). Sound, pure reorganization (CoV + drop indicator
   to the full box + Tonelli + row split). No `pivotShell`.
2. **Corrected domination** `∫_{matBox} freedSchurLoss(hsQ)^(−c') ≤ C·deeperFlagCoreIntegrand` — the S3
   route: P-radial blow-up exposes `decLoss` + the corank `frobSq(Ccross+Γ·(A_cor·Z))`, and
   `shell_corankOffSector_le_unif` (sorry-free, DeeperFlagCore) bounds the corank over the full `matBox`
   using **`hfloor`** with the `ab/2` charge. This is where `hfloor`/`U_sf` are load-bearing.
3. **L1** `deeperFlag_shell_core_le` (sorry-free) then bounds `deeperFlagCoreIntegrand ≤ C·comparator.integral`.

Only step 2's genuine analytic content (P-radial blow-up + `B₁₂→Γ'` shear + the `C`-absorption) is the
remaining brick — matching the ORIGINAL Brick D docstring (DeeperFlagCore L49–52: "Ky-Fan → shell ⊆ G,
S3/L1 assembly"). The whole-block `pivotShell` crux is a detour that only covers `j = 0`.

## 5. Signature verdict + cross-check

- **`shellSpine_le_hsQ_box`:** its RHS must change `matBox ∩ pivotShell` → `matBox` (full box). As a pure
  reorg it does not itself need `hfloor`; but its composite (`headSplit_domination`) does.
- **`headSplit_pivotDom` / `headSplit_domination`:** LHS domain must change `matBox ∩ pivotShell` → `matBox`
  (full box), and **must retain `hfloor`/`U_sf`** — load-bearing via S3 for the `j ≥ 1` shells. The step2
  `headSplit_domination_impl` already carries `hfloor`/`U_sf` in its signature; the ERROR is its PROOF,
  which routes through the false `shellSpine_le_hsQ_box` (pivotShell) + the shell-0-only crux.
- **cruxfin's full-block simplification does NOT subsume the floor factorization.** It made the crux
  S3-free by restricting to `pivotShell` (= shell-0); it discards exactly the `j ≥ 1` coverage the S3
  route provides. `couplingfin` (2026-07-13, decorrelated) had already found the whole-block/free-`A_cor`
  threshold DEGRADES off-shell (`uρ/2 → 5/2`) and that `j ≥ 1` is charged by the reduced comparator — i.e.
  the whole-block floor is insufficient off-shell. The S3 / deep-factor floor is required for `j ≥ 1`.

## 6. Most likely thing to break this / next step

- **Most likely to break:** if the endgame only ever invokes `headSplit_domination` at `c' <
  carrierThreshold` where each shell IS finite, one might hope `∫_{shell-j} G ≤ ∫_{shell-0} G` holds
  numerically. It does not in general (LHS integrand pointwise larger; §2), and §2-Q1 shows the proof
  method cannot reach the `pivotShell` RHS regardless. So the fix is architectural, not a threshold tweak.
- **Next construction that settles the open part:** build step-2 above (the S3 domination over the full
  `matBox` with `hfloor`) — the P-radial blow-up brick. This is the genuine remaining analytic content; the
  corank half (`shell_corankOffSector_le_unif`) and L1 are already sorry-free. The `pivotShell` crux
  `pivotPeel_domination` can be retired from the `j ≥ 1` path (it remains a valid shell-0 statement).

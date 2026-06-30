# Statement card — injOn#2 (`interiorLive_BparamsLeaf_injOn`)

> **Claim.** The radial-free chart-parameter map `BparamsLeaf` is injective on the LIVE-leaf interior
> achiever domain `D = kLDU '' (pivotBlowupOn (activeM) leafPivot '' interiorLiveInjDom)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorLive_BparamsLeaf_injOn`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean` @ `9718d12c`)
> - **Gloss.** For `M : Fin 3 → ℕ` (so `L = 2`), the achiever admissibility `ha`, and the deepest-width
>   positivity `h0r : 0 < Text M (tach M) 2`, `h0c : 0 < Wext M 2`: the map
>   `BparamsLeaf ha : (Fin (routeMAmbient M) → ℝ) → Params M` (the two reindexed chain-layer matrices
>   `(A 0, A 1)`, radial scalar hardwired to `1`) restricted to the set `D` is injective. `D` is the
>   `kLDU`-lens image of the `pivotBlowupOn`-image of `interiorLiveInjDom = {u | u leafPivot ≠ 0 ∧
>   ∀ j ∈ univ, u j ≠ 0}` (i.e. all coordinates nonzero).
> - **Proved.** Injectivity on `D`, unconditionally, by an explicit value-level readback: from the two
>   chart-layer matrices recover all reader slots of the input. V0 (boundary-0 Schur frame
>   `[[K,KN],[XK,XKN+E]]`) recovers `(K,N,X,E)` using K nonsingular (`schurFrameMap_inj_of_det_ne_zero`,
>   the SOLE invertibility fact, discharged by `slotReadV0_K_det_ne_zero_of_mem`); V1 recovers the lift
>   `W` and the leaf via `rsL1`; the `eIn` LinearEquiv packs all readers, and `(eIn ha).injective`
>   forces `y = y'`. Reuses genm-ambdet's banked `eIn`/`slotReadV0`/`rsL1`/`reindexL0_BparamsLeaf0`/
>   `dWdC_eq_eInV1` derivative machinery (imports `RouteMHDtotEihd`, `RouteMProjV0Gate`; no cycle).
> - **Assumed.** Achiever admissibility `StructAdm M (tach M)` + deepest-width positivity `h0r`/`h0c`
>   (the same the whole LIVE contract carries). The domain `D` excludes the zero locus (injDom forces
>   all coords nonzero) — this is the genuine injectivity hypothesis, NOT an assumed-away gap.
> - **Cited.** none (no S2 axiom; pure matrix algebra + finite equivalences + the banked derivative
>   infrastructure, all axiom-clean).
> - **Deferred.** none for this atom. (The SIBLING contract leaves `interiorLive_BdetMonomial`
>   ←genm-ambdet, `Umeas`/`Ubound`/`image` ←genm-ubound are distinct atoms, outside this dependency
>   chain.)
> - **Structure & ideas observed.** The chart is NOT affine after fixing the radial to `1` — `kLDU`
>   does not collapse `K` to the identity, it LDU-coordinatizes it to `(1+L)·diag(q)·(1+U)`. The only
>   nonlinearity-breaker is the invertibility of `K`, and on `D` that reduces to the PRE-kLDU K-diagonal
>   coords being nonzero (single coordinates of `pbo x`, not lensed combinations). The achiever's last
>   pivot (`r+c = 0`) would escape an `E = {leafH > 0}` domain, so `E = univ` is load-bearing for the
>   full LDU recovery.
> - **Route.** Packed Route A (controller-confirmed; decorrelated Codex xhigh confirmed the route + the
>   K-det-only correction): explicit left-inverse via the banked `eIn` staircase rather than raw
>   `chainA`-index peeling. Five supporting lemmas in the same file:
>   `schurFrameMap_inj_of_det_ne_zero`, `slotReadV0_K_det_ne_zero_of_mem`,
>   `slotReadV0_eq_of_BparamsLeaf0_eq`, `Wfun_Lfun_eq_of_BparamsLeaf1_eq`, `Nfun_eq_slotReadV0`.
> - **Status.** sorry-free + reviewed (independent reviewer + decorrelated Codex xhigh, PASS on
>   statement-fidelity / no-vacuity / no-overclaim / axiom-cleanliness `[propext, Classical.choice,
>   Quot.sound]` / build-green, 2026-06-30).

## Why this atom matters

This is the off-radial half of `interiorLive_injOn` — the InjOn hypothesis the n-fold null-slice
change-of-variables engine (`ldu_cov_of_differentiable_injOn`) consumes for the interior-branch achiever
box-divergence. injOn#1 (`interiorLive_kLDU_injOn`, the `kLDU`-lens half) was closed earlier
(@370a9a59). With both halves closed, `interiorLive_injOn` is sorry-free, leaving the contract gated only
on the determinant monomial (genm-ambdet) and the unit measurability/bound/image (genm-ubound).

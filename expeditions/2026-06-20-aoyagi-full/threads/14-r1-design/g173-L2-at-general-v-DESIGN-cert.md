# L2-at-general-v: the D1 full-B bridge for non-rank-exact v — DESIGN cert (pp-hall, 2026-06-22, #62)

**The genuinely-remaining D1 ≥-leg piece** (`rlctAt_deepest_le_of_optimal`): lift the PROVEN core-P1
(`rlctAt(F0, 0) ≤ rlctAt(F0, w)` on the homogeneous `B=0` core, @152ef0d) to the full-B loss at a GENERAL
`v ∈ optimalSet`. Fibre points are NON-rank-exact (their layers have varying ranks). The verdict: a
**constant active-block split** (NOT the maximal Morse split) dissolves the apparent obstruction; NO new
primitive, NO second citation. core-P1 applies directly after peeling the constant block.

## The split to AVOID — the maximal Morse split (varying n_v, the trap)
At a non-rank-exact `v`, the product-residual generators `(∏C − B)_ij` have a Morse-leading structure
with **more** independent linear parts than at the rank-exact deepest. Worked (2,2,2), `B = [[1,0],[0,0]]`
rank 1 (`g173_fullB_nv_varies.py`):
- **deepest** (rank-exact, layers `(1,1)`): Jacobian rank of the residual generators at `v` = **3**.
- **`v(2,1)`** (`A1=I` rank 2, `A2=B` rank 1, product `B`): Jacobian rank = **4**.
- **`v(1,2)`** (`A1=B`, `A2=I`): Jacobian rank = **4**.

So the MAXIMAL Morse dimension `n_v` is **NOT constant** (3 at the deepest, 4 at non-rank-exact `v`). The
naive bridge `rlctAt(v) = n_v/2 + core(v_core)` with a **constant** shift `n_v ≡ r(H_0+H_L−r)` is **FALSE**.
(And after the maximal split, the residual core is stratum-dependent — at `v(2,1)` it is trivial, the fibre
is smooth there.) This was the controller-flagged risk, confirmed real: over-peeling makes the shift vary
and the core stratum-dependent.

## The split to USE — the CONSTANT active-block split (the fix)
Peel only the **constant-dimension active block** (the rank-`r` "transmitted chain" regular residuals),
the SAME `N_active` at every `v`:

    N_active  =  H_0 · H_L − (H_0 − r)(H_L − r)   =   r(H_0 + H_L − r)   =   nReg   (the g150 regular dim).

It depends only on `r = rank B`, NOT on `v`'s layer ranks — **CONSTANT on optimalSet**. After peeling
exactly this block, the residual is the SAME homogeneous core `F0_{H−r} = ‖D_1···D_L‖²` (the per-layer
Schur-reduced quotient maps `D_s` on the reduced widths `M = H − r`, the g172 `S_s` object), evaluated at
the induced basepoint `D(v)`:

    rlctAt(dlnLoss H B, v)      =  N_active/2  +  rlctAt(F0_{H−r}, D(v)),        D_1(v)···D_L(v) = 0.
    rlctAt(dlnLoss H B, deepest)=  N_active/2  +  rlctAt(F0_{H−r}, 0).            (D(deepest) = 0.)

Then **core-P1 (PROVEN) applies directly:** `rlctAt(F0_{H−r}, 0) ≤ rlctAt(F0_{H−r}, D(v))` ⟹

    rlctAt(dlnLoss H B, deepest)  ≤  rlctAt(dlnLoss H B, v).    ∎

**`r = 0`:** `N_active = 0`, the statement reduces exactly to core-P1 (the `d1_222_strata` core case).

## Where the varying-n_v went (the reconciliation — verified, `g173_constant_active_split.py`)
The "extra Morse direction" at `v(2,1)` (rank 4 vs 3) is NOT an extra active-block direction — it is an
extra smooth direction **INSIDE the core stratum**, captured by `rlctAt(F0, D(v))` being evaluated at
`D(v) ≠ 0` (on the core's OWN zero-fibre) rather than at `0`. Worked: `(2,2,2)`, `r=1`, `M=(1,1,1)`,
`F0 = (s_1 s_2)²`:
- deepest: `D=0`, `rlctAt(F0, 0) = 1/2` ⟹ total `3/2 + 1/2 = 2`. ✓
- `v(2,1)`: total `= 2` (direct calc), so `rlctAt(F0, D(v)) = 1/2`. And `F0 = (s_1 s_2)²` at a point on the
  axis `{s_1 = 0, s_2 ≠ 0}` is `≈ (s_2^*)² · s_1²` — a nondegenerate quadratic in `s_1`, `rlctAt = 1/2`.
  ✓ MATCHES. core-P1 gives `1/2 = rlctAt(F0,0) ≤ rlctAt(F0,D(v)) = 1/2` — TIGHT here.

So peeling ONLY the constant active block moves all the `v`-dependence into the core basepoint `D(v)`,
where core-P1 does the work. The maximal split double-counts: it peels the core's internal smooth
direction as if it were an active-block direction, breaking the constant shift.

## The cheaper DIRECT-LB route — probed, NOT cleaner (the rejected alternative)
The controller invited a direct `rlctAt(v) ≥ rlctAt(deepest)` avoiding the chart. Probed
(`g173_lsc_direction_check.py`): the mechanism would be the SAME nbhd-monotonicity as g170/core-P1
(`∃U∈𝓝` swallows nearby points), but along a **fibre path** `w(s) → deepest` (not the scaling ray). On the
(2,2,2) example there IS such a path (`A1(t)=[[1,0],[0,1−t]]`, `A2=B`; `A1(t)A2 = B` for all `t`, `t=1`
the rank-exact deepest), and the residual-generator Jacobian rank drops `4 → 3` exactly at `t=1` (the
deepest is the most singular point — `rlctAt` lower-semicontinuous, deepest at the bottom). BUT:
- The honest direction is **lower-semicontinuity** `rlctAt(deepest) ≤ liminf_{s→0} rlctAt(w(s))`, NOT a
  pointwise `≤` for all nearby points (the admissible nbhd `U*(c)` shrinks as `c → rlctAt(deepest)` — the
  naive "every point a local min" is FALSE, caught adversarially in `g173_lsc_direction_check.py`).
- To turn `liminf` into `rlctAt(v)` you need `rlctAt` constant along the fibre-path interior
  (deformation-invariance within the connected stratum) — a fibre-connectivity + path-existence claim
  that is NOT obviously lighter than the active-block split, and is harder to make uniform over all `v`.

**Verdict: use the constant active-block split + core-P1 (R-chart, the safe bridge).** The direct-LB
route is real but needs fibre-path-connectivity-to-the-deepest + `rlctAt`-constancy-along-the-path, which
is no cheaper and less mechanical than the constant-block L2.

## The cleanest Lean statement (what cobuild-sub34/crux2 build)
**`L2_at_general_v`** (the named obligation extending the deepest #44 chart to arbitrary `v`):

    For v ∈ optimalSet H B (rank B = r): there is a chart at v peeling the CONSTANT active block
    (dim N_active = r(H_0+H_L−r)) with germ
        dlnLoss H B ∘ chart_v  =ᶠ[𝓝 0]  (∑ N_active nondeg squares)  +  F0_{H−r}(D(v) + core coords),
    where F0_{H−r} = ‖∏ S_s‖² (the g172 per-layer Schur core) and D(v) ∈ {∏ = 0} (the core fibre).
    ⟹ rlctAt(dlnLoss H B, v) = N_active/2 + rlctAt(F0_{H−r}, D(v))   (via the banked NON-MP transport,
       rlctAtOn_unit_invariant_aux + germ-locality, the same g150 machinery, broader basepoint).

This is the SAME chart approach as the deepest #44 (g150/g172), with **two changes**: (i) basepoint `v`
(not the deepest) — the gauge slice is taken at `v`'s transmitted rank-`r` chain, not the deepest's;
(ii) the core basepoint `D(v)` is not `0`. Everything banked for the deepest (the det-unit Jacobian, the
exact germ, `N_active = nReg`, the Schur core `S_s`) transfers. NOT a new primitive, NOT a citation.

The ONE thing that needs care (the honest residual): at a non-rank-exact `v`, the "transmitted rank-`r`
chain" must be chosen — `v`'s layers have ranks `≥ r` but not `= r`, so the rank-`r` gauge slice is a
SUB-block of `v`'s (larger) image, not the full layer. `block_elimination` at `v` gives the rank-`r`
factorization on the transmitted block; the surplus rank (`v(2,1)`'s extra rank in `A1=I`) lands in the
core coords (as the `D(v) ≠ 0` offset), NOT the active block. This is the "broader-split" content:
`block_elimination` applied to the **product `∏C = B`** (rank `r`), not to each layer (varying rank).

## Most likely thing to break this
The chart at a non-rank-exact `v` needs `block_elimination` on the rank-`r` PRODUCT to give a det-unit
gauge slice whose complement is the core — but at `v` the layers are NOT rank-`r`, so the per-layer gauge
units `P_s, Q_s` (g150) must be replaced by a slice of the rank-`r` transmitted chain THROUGH `v`. The
existence of that chain (a rank-`r` factorization of `B` compatible with `v`'s larger layers) is the
constructibility crux — plausible (`B` has rank `r`, so a rank-`r` chain exists; `v`'s surplus is the
core offset `D(v)`), but it is the obligation to verify, analogous to the deepest `block_elimination` but
at the product level. If the transmitted chain can't be chosen continuously/uniformly over the stratum,
the chart fails — but for the RLCT (a germ at a single `v`) only the local chart at `v` is needed, so the
uniformity worry is moot per-point. crux2/cobuild-sub34 build the chart; this cert pins the target.

## Decorrelation
pp-hall exact algebra (`g173_fullB_nv_varies.py` — the varying-n_v finding; `g173_constant_active_split.py`
— the constant-block reconciliation; `g173_lsc_direction_check.py` — the direct-LB probe + the lsc
direction catch) + decorrelated Codex (gpt-5.x xhigh, `g173-d1-route-codex-answer.md`) — CONVERGED
independently: Codex flagged the SAME maximal-split trap ("`n_v` jumps, residual stratum-dependent —
FALSE") and gave the SAME fix (constant active-block `N_active = H_0 H_L − (H_0−r)(H_L−r)` + core-P1 at
`D(v)`). I had found the varying-n_v obstruction first (the worked example); Codex supplied the
constant-block resolution; I verified it reconciles the example exactly. Builds on core-P1 (@152ef0d,
PROVEN), g172 (the per-layer Schur core `S_s`), g150 (the deepest chart / `nReg` / NON-MP transport),
`block_elimination` (`Skeleton.lean:279`), `d1_222_strata.py` (#112, the non-rank-exact finding).

# General-v squeeze datum — one cert for #44 sub-3 (deepest) + D1 (a) (arbitrary v) (pp-hall, 2026-06-22, #155)

**Extends #48/#150 to the general-v squeeze datum.** crux2's D1 #111-check: the general-v
homogeneous-residual chart is NEW (not banked) AND shares technique with #44's deepest squeeze — so ONE
cert serves BOTH: #44 sub-3 (v = deepest) + D1 (a) (`rlctAt_deepest_le_of_optimal`, arbitrary
v ∈ optimalSet). Core = the GAUGE-NORMALIZED `T̃` (g150-fix / g153 basis; raw-∏T stays refuted). Reuses
crux2's PROVEN primitives (`rlctAtOn_squeeze`, `rlctAtOn_mono`, `weightedThreshold_weight_unit_invariant`,
`rlctAtOn_spectator_peel` in `S1NonMPTransport`/`S1Spectator`). The Lean consumers differ only in
basepoint + a homogeneous-scaling step.

## Part 1 — the general-v squeeze datum (SOLID, no degeneration)
At ANY rank-exact `v ∈ optimalSet H B` (`v ∈ optimalSet ∧ ∀ s, (v s).rank = r` = `IsDeepLayers` minus
the deepest-specific part — just rank-exactness), the per-layer gauge slice
`C_s = [[I_r + X_s, Y_s], [Z_s, T_s]]` (via `block_elimination` at `v`, units `P_s, Q_s` with
`P_s (v s) Q_s = blockdiag[I_r, 0]`) is **structurally IDENTICAL** to the deepest case (g150). The squeeze

    c₁·Φ ≤ dlnLoss H B(·) ≤ c₂·Φ   near v,    Φ = (∑ E_i²) + ‖T̃_1···T̃_L‖²

holds VERBATIM, with `T̃_s` the GAUGE-NORMALIZED blocks (the `(I − V_s Y_s)^{-1}`-absorbed product Schur
complement, g150-fix — NOT raw `T_s`), `‖T̃_1···T̃_L‖² = dlnLoss M 0` (`M = H − r`). The squeeze constants
`c₁ = (2(1+T²))^{-1}`, `c₂ = 2+2T²` depend ONLY on the local bounded pivot-column norm `T` near `v` —
**NOT on `v` being the deepest point** (g155). So:

> **The general-v datum = the deepest datum (#48/#150) with basepoint `v` (not `0`).** The gauge slice,
> the gauge-normalized `T̃`, the squeeze, and the det-unit/non-MP transport
> (`weightedThreshold_weight_unit_invariant` + `rlctAtOn_squeeze`) are all basepoint-agnostic. NO
> degeneration in this half — feasible at any rank-exact `v`.

Consequence (via the banked `rlctAtOn_squeeze` + `schur_recursion_step_squeeze` shape, at basepoint `v`):

    rlctAt H (dlnLoss H B) v  =  nReg/2 + rlctAtOn (v-core) v,    nReg = r(H_0 + H_last − r),
                                                                  v-core = ‖T̃-chain at v‖² = dlnLoss M 0.

## Part 2 — the v=deepest specialization (EXPLICIT, = #44 sub-3 / cobuild-sub34)
Set `v = deepestPoint H r B`. Then the basepoint is `0` in the gauge coords (the deepest point IS the
gauge origin), the squeeze is the #48/#150 deepest datum, and `v-core = the deepest core = dlnLoss M 0`.
This is EXACTLY cobuild-sub34's #44 sub-3 (`deepest_loss_in_gauge_coords` at the deepest point) — the
two AGREE by construction (the deepest case is the `v = deepestPoint` instance). The #51 R-squeeze
collapse (`‖T·(I−VY)^{-1}·S‖² ≍ dlnLoss M 0`, cobuild-sub34) is the gauge-normalized `T̃`-form of this
same datum — convergent with g150-fix. So:

    rlctAt H (dlnLoss H B) (deepestPoint …)  =  nReg/2 + rlctAtOn (deepest-core) 0,
                                                deepest-core = dlnLoss M 0  (the homogeneous core).

## Part 3 — D1 (a): `rlctAt(deepest) ≤ rlctAt(v)` via the homogeneous-scaling domination
`rlctAt_deepest_le_of_optimal` wants `rlctAt(deepest) ≤ rlctAt(v)`. Both sides reduce (Parts 1+2) to
`nReg/2 + rlctAtOn(core)`, so D1 (a) reduces to the CORE domination

    rlctAtOn (deepest-core) 0  ≤  rlctAtOn (v-core) v.

**Direction (verified, g155_direction):** the deepest core is MAXIMALLY DEGENERATE — `deepest-core =
(homogeneous ‖∏T̃‖²)` vanishes on ALL the reduced rank-walls (e.g. `(y_1 y_2)²` vanishes on `{y_1=0} ∪
{y_2=0}`); a general-`v` core is LESS degenerate (off-deepest offsets `c ≠ 0` remove walls, e.g.
`((c+y_1)y_2)²` vanishes only on `{y_2=0}`). Fewer walls ⟹ larger rlct ⟹ `rlctAt(deepest) ≤ rlctAt(v)`.
The bridge is `rlctAtOn_mono` (the banked Aoyagi Lemma 1(1)): `|deepest-core| ≤ |v-core|` near the
basepoints + `(deepest-core = 0 ⟹ v-core = 0)` on the shared reduced zero-set.

**The homogeneous-scaling step** (D1's only addition over #44 sub-3, the docstring's "homogeneous normal
form domination"): for scaling-reachable `v` (v-core = deepest-core with reduced coords damped by
`t_i ∈ [0,1]`), `Σ t_i^{2n_i} f_i'² ≤ Σ f_i'²` (since `t_i^{2n_i} ≤ 1`, `n_i ≥ 1`) — the `rlctAtOn_mono`
`|G| ≤ |F|` input directly. So D1 (a) for scaling-reachable `v` is: Part-1 datum at `v` + Part-2 at
deepest + `rlctAtOn_mono` via the `Σt^{2n}≤1` scaling.

## The early D1 FEASIBILITY FLAG (find-confound, before the D1 grind)
The Part-1 datum (general-v gauge squeeze) is SOLID for all rank-exact `v` — no degeneration. The
SCALING step has a scope to name honestly:
- **Scaling-reachable `v`** (v-core = a `t`-damping of the deepest core): the bare `Σ t^{2n_i}f² ≤ Σ f²`
  bound is the `rlctAtOn_mono` input. Clean. ✓
- **Fully general `v ∈ optimalSet`** (v off-deepest by genuine OFFSETS, not a pure scaling): the v-core
  is NOT a `t`-scaling of the deepest core (it has fewer walls, not damped walls). The domination
  `rlctAtOn(deepest-core) ≤ rlctAtOn(v-core)` STILL holds, but its `rlctAtOn_mono` input
  (`|deepest-core| ≤ |v-core|` near the basepoints) is a **GERM-DOMINATION**, not the bare scaling — it
  needs the fact **`deepest = the pointwise-min (max-vanishing) core over `optimalSet`** (Aoyagi 2013
  Thm 2 / the `deepestPoint` construction: the deepest singular point maximises the vanishing). NAME
  that as the `rlctAtOn_mono` `|deepest-core| ≤ |v-core|` input — do NOT smuggle it into the scaling.
- **Net:** D1 (a) IS feasible for all `v` (the deepest is the min-core, so `rlctAtOn_mono` applies), but
  the cert states BOTH routes: the explicit scaling for scaling-reachable `v` (light), and the
  germ-domination (`deepest = min-core`, Aoyagi Thm 2) for general `v` (the named cited/assumed input).
  **No degeneration** — the squeeze constants and the gauge chart are fine at any `v`; the only
  not-bare-algebra piece is the general-`v` `|deepest-core| ≤ |v-core|` domination, which is the Aoyagi
  Thm 2 monotonicity (cited), realised as the `rlctAtOn_mono` hypothesis. This is the find-confound flag:
  D1 (a)'s scaling step is NOT a bare `Σt^{2n}≤1` for general `v` — it is the Aoyagi-Thm-2
  deepest-is-min-core fact fed to `rlctAtOn_mono`. Flagging before the D1 grind so crux2 names it, not
  asserts a too-clean scaling.

## What the consumers transcribe
- **#44 sub-3 (cobuild-sub34), v = deepest:** Part 2 — the deepest gauge squeeze, `rlctAt(deepest) =
  nReg/2 + rlctAtOn(dlnLoss M 0) 0`. The gauge-normalized `T̃` (g150-fix / the #51 R-squeeze) is the core.
- **D1 (a) (crux2 #42), arbitrary v:** Part 1 (general-v datum, basepoint `v`) + Part 3 (the core
  domination): `rlctAt(deepest) ≤ rlctAt(v)` via `rlctAtOn_mono` with the `deepest = min-core` input
  (scaling-reachable: the `Σt^{2n}≤1` bound; general: Aoyagi Thm 2). Both reduce to `nReg/2 +
  rlctAtOn(core)` via the banked `rlctAtOn_squeeze` at the respective basepoints.
- Both share: the gauge slice + gauge-normalized `T̃` (g150-fix), the squeeze (`rlctAtOn_squeeze`), the
  non-MP transport (`weightedThreshold_weight_unit_invariant`), and the regular-block spectator-peel
  (`rlctAtOn_spectator_peel`). The deepest is the `v = deepestPoint` instance — the two agree.

## Most likely thing to break this
The general-`v` `|deepest-core| ≤ |v-core|` germ-domination (the `rlctAtOn_mono` input for non-scaling-
reachable `v`). It rests on `deepest = pointwise-min core over optimalSet` (Aoyagi Thm 2). If that fact
is NOT available value-independently (R1-separable) — i.e. if proving "deepest core ≤ every v's core"
needs the resolution VALUE — then D1 (a) is L2-downstream (as the docstring flags: "whether provable
from L1 block_elimination + the deepest-point structure ALONE or genuinely needs the resolution value").
The cert's Part-1 datum is value-independent (the gauge squeeze is local); the Part-3 domination is where
the value-dependence (if any) lives. crux2's D1 scoping (#42) should pin whether `deepest = min-core` is
L1-provable (block_elimination + deepest structure) or L2-gated. My read: it is the
`block_elimination`-homogeneous-domination (the deepest core is the leading homogeneous part of every v's
core, which dominates near 0) — L1-separable — but that is the one thing to confirm, not assert.

## Provenance
Extends #48/#150 (the deepest gauge-chart cert, corrected `T̃` form) to general `v`. Reuses crux2's
banked `rlctAtOn_squeeze`/`rlctAtOn_mono`/`weightedThreshold_weight_unit_invariant`/
`rlctAtOn_spectator_peel` (`S1NonMPTransport`/`S1Spectator`). The deepest specialization = #44 sub-3 /
cobuild-sub34 / the #51 R-squeeze (`‖T·(I−VY)^{-1}·S‖² ≍ dlnLoss M 0`) — convergent. Scripts:
`g155_generalv.py`, `g155_direction.py`, `g155_feasibility_flag.py`. Builds on g150-fix (gauge-normalized
`T̃`), g153 (det-1 peel), `rlctAt_deepest_le_of_optimal` (`Skeleton.lean:973`, the D1 consumer),
Aoyagi 2013 Thm 2 (the deepest-is-min-core monotonicity, the general-`v` domination input).

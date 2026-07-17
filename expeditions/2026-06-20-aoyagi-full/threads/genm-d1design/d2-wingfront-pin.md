# d2-wingfront-pin — the #2 wing-front general-rank det-resolution recipe (corrects the POWER-Codex Δ-model)

**Seat:** pen-and-paper (design), `genm-d1design`, Lane 1. **Date:** 2026-07-17. **NO Lean.** The #2 pin
(REGIME #2 of the two-regime N3): the a=0/b=0-POWER wing FRONT rank-sector, general-rank (incl. the square).
Consumes jointpnp's TEST-4 (decorrelated single-factor confirmation) + my charge reconciliation
(`scripts/d2_charge_reconcile.py`) + the two-regime finding (`d1_wing_stratum_rank.py`). Corrects the
POWER-Codex source-rank Δ-model (WRONG: the wing front is full-rank, the TAIL A₁ drops) and the unsound
"A≤2Δ fold" (Codex 2b). Template: the SQUARE M=(2,2,3,3)@s=0 (rank-2).

---

## ★ VERDICT: single-matrix determinantal resolution of the FREE tail layer A₁ — DETAIL-AT-SCALE (standard), NOT a wall, NOT a cite, single-factor NATIVE

**The wing front rank-sector is the STANDARD determinantal resolution of ONE free matrix's rank-drop (the
tail layer A₁), pushed through the full-rank front X over the dominant-minor chart.** NOT a 2-matrix
product-corank (X can't drop — dominant-minor keeps it full-rank), NOT the POWER-Codex source-rank Δ-blow-up
(that mis-modeled the front as rank-dropping). jointpnp TEST-4 decorrelated-CONFIRMS single-factor for all
ranks incl. the square. It is the genuinely-new heart's HARDEST piece, but it is a KNOWN object (the RLCT of
a determinantal variety) + wiring — buildable, detail-at-scale.

## 1. The object + widths (a=0 wing; b=0 mirror in §4)

a=0 wing (M₀≤M₁, cut t=M₀): `freedSchurLoss = frobSq(X·Q)`, `X=[P|B₁₂]` (`M₀×M₁`, FULL ROW RANK M₀,
P invertible), `Q = A₁·Z_deep` (`A₁` the first tail layer, `M₁×M₂`; `Z_deep = prod(M₂,…,M_last)`, `M₂×q`).
`W := X·A₁` (`M₀×M₂`). Reduce to `redChain M₀ M = (M₀, M₂, …)` — but `ρ(W)` is singular (POWER, `M₂≥b+2`,
`b=M₁−M₀`), so the front rank-sector.

## 2. The resolution (PEEL-FIRST, dominant-minor, single-matrix det) — jointpnp TEST-4 foundation

1. **Dominant-minor chart of X (the LOAD-BEARING kill).** Cover by which `M₀×M₀` minor `X_σ` of `X` is
   dominant; on that chart `X` is FULL ROW RANK M₀, `σ_min(X) ≍ ‖X‖` controlled. This is what makes it
   single-factor: `X` never drops ⟹ `rank(W) = rank(X·A₁) = min(rank A₁, M₀)` (jointpnp: exact when
   `rank A₁ ≤ M₀`, else caps at M₀) ⟹ only `A₁` drops. **Never off-chart `{rank X<M₀}`** (that tube is the
   product-corank cited-wall counterpart, dispatched out).
2. **Stratify `rank(A₁) = σ`, `σ ∈ [0, min(M₁,M₂)]`** — the STANDARD determinantal variety of the FREE
   `A₁` (`M₁×M₂`). `{rank(W)≤σ}` is the surjective-`X` preimage of `{rank A₁≤σ}` (jointpnp TEST-4). Blow up
   each `{rank A₁=σ}` by the STANDARD determinantal resolution (the free-matrix rank-variety resolution —
   a KNOWN object; the exceptional coords + monomial Jacobian `|det DΦ| = u(ξ)·∏|z_j|^{ν_j−1}` are the
   determinantal-variety resolution's, NOT bespoke). Single-matrix (A₁), so single-factor.
3. **Push through the surjective X** (`W = X·A₁`, `X` full-rank M₀). The pushforward is submersive on-chart
   (X full row rank), so the `{rank A₁=σ}` resolution transports to `{rank W}` cleanly.
4. **Charge reconciliation (VERIFIED, `scripts/d2_charge_reconcile.py`).** Stratum `σ ↔` reduced cut `s`
   (`rank W = s`); reduce to `redChain s M` at **peelCharge `(M₀−s)(M₁−s)`** (NOT the raw W-codim
   `(M₀−σ)(M₂−σ)`). `min_s[(M₀−s)(M₁−s) + minAdm(redChain s M)] = minAdm(M)` EXACTLY (756/756; the global
   0/5292). **The EXCESS** `(M₀−σ)(M₂−σ) − (M₀−s)(M₁−s) = (M₀−s)(M₂−M₁)` (when `M₂>M₁`) **is NOT extra
   charge — it is the reduced chain's OWN `(s, M₂)` leading-layer resolution, absorbed by
   `hIH(redChain s M)`.** (This is the POWER-Codex's "charge ≠ W-codim" observation, now correctly read: the
   det variety is `A₁`'s, W-codim `(M₀−σ)(M₂−σ)`, but the front-collapse CHARGE is peelCharge, excess into
   the reduced layer.)
5. **`|det P|` / conditioning disposal.** The dominant-minor CoV Jacobian (`|det X_σ|`, controlled on-chart)
   and the `X`-integration: the free front `X`'s Gram disposes as the LANDED `frontCollapse_wide_bounded`
   family / a qbox on the free front (X free box), NOT a product-Gram. The reduced core → `hIH(redChain s M)`
   at `c' − ½·peelCharge`.
6. **Sum over strata** (`ENNReal.sum_lt_top`), min `= ½minAdm(M)`. Corner finite for `c' < ½minAdm(M)`.

## 3. Template — the SQUARE M=(2,2,3,3)@s=0 (rank-2, jointpnp-covered)

`M₀=M₁=2`, front `P` (2×2 invertible), `A₁` (2×3 free), `W=P·A₁` (2×3), `P` invertible ⟹ `rank W = rank A₁`.
Strata `σ∈{0,1,2}`: `σ=2` full (submersive, fixedF top); `σ=1` `{rank A₁≤1}` codim `(2−1)(3−1)=2`; `σ=0`
`{A₁=0}` codim 6 (LINEAR, rlct 3). Binding `s*=0` (or 1), peelCharge `(2−0)²=4 = minAdm` (½·4=2=½minAdm).
The `{A₁=0}` stratum (codim 6, W-codim `(2−0)(3−0)=6`) reduces at peelCharge 4; excess `6−4=2=(2−0)(3−2)` =
the reduced `(0,3)`-layer (in `redChain 0 M=(0,3,3)`). Single-matrix det of the free `A₁` throughout — jointpnp
TEST-4: `{A₁=0}` linear (single-factor rlct 3), `{rank A₁≤1}` single-matrix det codim 2. NO 2-matrix
product-corank (P invertible).

## 4. b=0 mirror (M₁≤M₀, tall front [P;C])

Same recipe, front `[P;C]` (`M₀×M₁`, FULL COL RANK M₁, injective) — `A₁↦[P;C]·A₁` INJECTIVE (not surjective),
so the pushforward is to a subvariety; the single-matrix det of `A₁` transports via the injective front (the
`b0mirror` distinctness: injective not surjective). Same charge reconciliation, dominant-minor chart of
`[P;C]` (keep full col rank M₁), single-matrix det of the free `A₁`. `hIH(redChain M₁ M)`.

## 5. Banked pieces + new sub-lemmas

**Banked:** `frontCollapse_wide_bounded_lt_top` (the submersive top sector + the `|det P|`-family qbox),
`minAdm_le_peelCharge_add_redChain` (charge/cut-soundness), the MP front-split + box CoV, `hIH`.
**NEW sub-lemmas (the standard-det-resolution kit, single free matrix A₁):**
- **(D1)** the finite rank-stratum cover `{rank A₁=σ}`, `σ∈[0,min(M₁,M₂)]`, measurable off a null boundary.
- **(D2)** the standard determinantal-variety CoV/blow-up of `{rank A₁=σ}` (the free-matrix rank-variety
  resolution — KNOWN; the exceptional coords + monomial Jacobian).
- **(D3)** the surjective-X (resp. injective-[P;C]) pushforward transport (submersive on the dominant-minor chart).
- **(D4)** the charge-reconciliation reduction: per-stratum `→ hIH(redChain s M)` at `c'−½peelCharge`, the
  `(M₀−s)(M₂−M₁)` excess absorbed by the reduced `(s,M₂)` layer.
- **(D5)** the dominant-minor cover of the front (keep X/[P;C] full-rank — the KILL) + null-boundary + sum.

## 6. Kill-conditions (bake)
1. **Keep the front FULL-RANK (dominant-minor chart)** — the load-bearing single-factor kill; off-chart
   `{rank X<M₀}` is the product-corank cited-wall counterpart, dispatched out. (jointpnp KILL#1.)
2. **Single-matrix det of A₁ only** — NEVER a 2-matrix (X,A₁) joint product-corank (X full-rank precludes it).
3. **peelCharge `(M₀−s)(M₁−s)`, NOT the raw W-codim** — the `M₂`-excess is the reduced layer, not charge.
4. **PEEL-FIRST / never the dead nested-qbox** (WALLS, `M=(2,2,1,2)`); never the unsound pointwise fold (Codex 2b).
5. **Carry `|det J|`** (the determinantal monomial Jacobian) — never drop it.

## Close
- **Firmest.** #2 = the STANDARD determinantal resolution of the FREE tail layer `A₁`'s rank-drop (a KNOWN
  object), pushed through the full-rank front (dominant-minor chart), reduced per-stratum to `hIH(redChain s M)`
  at peelCharge `(M₀−s)(M₁−s)` (min = ½minAdm, verified), the `M₂`-excess in the reduced layer. Single-factor
  NATIVE (jointpnp TEST-4 decorrelated), incl. the square. NOT the POWER-Codex source-rank Δ-model (front is
  full-rank), NOT the unsound fold, NOT a product-corank (X can't drop). Detail-at-scale, buildable, not a wall.
- **Most likely to break the BUILD.** (i) The determinantal-variety resolution kit (D2) for a general free
  matrix `A₁` — standard but detail-at-scale (the exceptional Jacobian bookkeeping across strata). (ii) The
  injective-front (b=0) transport (D3) — subtler than the surjective (a=0) (b0mirror). (iii) The `|det P|`
  disposal composing with the reduced core at the tight (binding) stratum. (iv) The dominant-minor cover being
  genuinely full-rank-preserving for the SQUARE (front P square — its only minor is P itself; `σ_min(P)` on the
  chart controlled by the minor-dominance, NOT bounded below globally — the |det P| handled by the det-variety
  resolution + the free-front qbox, not by a σ_min lower bound).
- **Next.** The formaliser builds the standard-det-resolution kit (D1–D5) for the single free `A₁`, template
  the square (2,2,3,3)@s=0, then the general wing. jointpnp cross-checking the single-factor. This is REGIME #2;
  REGIME #1 (corank rank-1 FreeBilinear) + the fixedF top + the κ-skeleton land in parallel (lane1shell).

Files (absolute): `…/threads/genm-d1design/d2-wingfront-pin.md` (this); `joint-coupled-spec.md`,
`b0-wall-adjudication.md`, `scripts/{d2_charge_reconcile,d1_wing_stratum_rank}.py`; jointpnp `genm-jointpnp/scripts/{l1_singlefactor_battery,l1_wingfront_check}.py` (TEST-4).

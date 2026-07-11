# genm-vsastruct — corank-2 rung certificate (the frontier de-risker for the deep-strata recursion)

**Seat:** pen-and-paper (witness + obstruction). **Date:** 2026-07-11. **NO Lean.** **Scope: q=2 ONLY.**
**Charge:** the formaliser-ready certificate for the corank-2 rung of the (3,3,3,4) deep-strata recursion —
the coupled front-first majorant, the tube integral, the composition → 7/2, Lean shapes + banked-piece
audit. **Exact algebra:** `/tmp/corank2_check.py` (asymmetric front form, pushforward joint density,
composition; MC-guided). **Decorrelated:** `codex/corank2-{prompt,answer}.md` (gpt-5.6, xhigh; my
conclusion withheld — it CONFIRMED every exponent + the compound-route failure, with exact Gamma
constants). Companion: `verdict.md` (the parent structural adjudication).

---

## HEADLINE (the load-bearing finding, decorrelated-confirmed)

**The corank-2 front-first majorant is ASYMMETRIC: `g̃ ≍ max(s₂,s₃)^{−3}·min(s₂,s₃)^{−(2c'−6)}`.** The
true corank-2 tube integral IS finite for `c'<7/2` (`= ½(D₂+d₂)`), via the joint two-singular-value
pushforward density `dμ ≍ s₂²·ℓ(s₂) ds₃ ds₂`. **BUT the symmetric `∧²`-compound `σ_min(∧²P)=s₂s₃`
weight — the proposed Lean route — CANNOT close it: pointwise domination forces `b ≥ c'−3/2 > 3/2`,
integrability forces `b < 1`; the ranges do not overlap.** ⟹ The corank-2 rung is BUILDABLE (7/2 sound,
derived three ways) but NOT via the clean symmetric compound tube. It needs an **asymmetry-respecting
route**: either (J) a joint-pushforward-density module (new measure infra) or, cleaner, (S) the native
(S,J) corner resolution (vslice-cert §5), whose Lean endpoint `sjJointResolution` is currently an unproven
sorry. **Recommendation: build the deep strata via Architecture I's corner resolution, NOT Architecture
II's compound tube. Architecture II (LAYER 2) is the right tool for the TOP stratum only.**

---

## 1. The corank-2 coupled front-first majorant (PROVEN exact)

**Cell.** `cell₂ = {σ₁(P) ≥ κ, σ₂(P) < κ}` — the tail `P = Ã₁·A₂` (`3×4`) near `{rank ≤ 1}`; `s₁ ≍ 1`
bounded below, `s₂ ≥ s₃` both small. `m₀ = r = 3`, `c' ∈ (3, 7/2)`.

**The integrand.** After the Gram-diagonalisation `PPᵀ = Q diag(s²) Qᵀ` and the rotation `A₀↦A₀Q`, the
front box integrand is the coupled SUM (`b_j ∈ ℝ³`):

> `g̃(P) = ∫_{box³} (κ²‖b₁‖² + s₂²‖b₂‖² + s₃²‖b₃‖²)^{−c'} db₁ db₂ db₃`   (1 stable block `b₁`, weight `κ`;
> 2 COUPLED collapsing blocks `b₂,b₃`, weights `s₂,s₃`).

**The bound (exact, iterated Beta).** Integrate `b₁` (dim 3, weight `κ²`; `∫_{ℝ³}(‖x‖²+T)^{−c'}dx =
π^{3/2}Γ(c'−3/2)/Γ(c') · T^{3/2−c'}` for `c'>3/2`), then `b₂` (weight `s₂²`, saturates since
`2(c'−3/2)>3 ⟺ c'>3`), then `b₃` (finite radial leaf `∫ρ^{5−2c'+3}dρ`, `c'<9/2`):

> **`g̃(P) ≍ s₂^{−3}·s₃^{−(2c'−6)}`   on `cell₂`   (`c' ∈ (3, 7/2)`),** i.e. `p=3` on `max(s₂,s₃)`,
> `q=2c'−6 = α'` on `min(s₂,s₃)`. Globally `g̃ ≍ max(s₂,s₃)^{−3}·min(s₂,s₃)^{−α'}`.

**Consistency (two exact checks — both pass).**
- Diagonal `s₂=s₃=σ`: `g̃ ≍ σ^{−3}·σ^{−(2c'−6)} = σ^{−(2c'−3)} = σ^{−β₂}` (the `verdict.md` codim-2 exponent).
- Sector boundary `s₂→κ` (leaving `cell₂`): `g̃ ≍ κ^{−3}·s₃^{−(2c'−6)} ≍ σ_min^{−α'}` — **continuously
  matches the codim-1 (LAYER-2) form.**

[FACT — exact iterated Beta; MC-guided (`corank2_check.py`: s₂-exp ≈2.5–3.5, s₃-exp ≈α'); Codex-confirmed
with the exact Gamma constant `π^{3/2}Γ(c'−3/2)/Γ(c')`.]

### Why the COUPLING is load-bearing (the min-vs-sum, worked)

The loss is a SUM whose two collapsing directions share the corner `{b₂=b₃=0}`. Treating them as two
INDEPENDENT divisors undershoots. In the resolved corner coordinates (vslice-cert §5; `u₀` = the `2×2`
corank-block radial, `4`-dim ⟹ Jacobian `|u₀|³`; `u₁` = the boundary-row radial, `3`-dim ⟹ `|u₁|²`):

| treatment | bookkeeping | threshold |
|---|---|---|
| independent `{u₀=0}` | `∫|u₀|^{3−2c'}du₀ < ∞ ⟺ 3−2c'>−1` | `c'<2` |
| independent `{u₁=0}` | `∫|u₁|^{2−2c'}du₁ < ∞ ⟺ 2−2c'>−1` | `c'<3/2` |
| **independent (min)** | `min(2, 3/2)` | **`3/2` (UNDERSHOOT — wrong)** |
| **coupled corner** `u₁=u₀τ` | `|u₀|³|u₀τ|²|u₀| = |u₀|⁶|τ|²`; `G=u₀²(U₀+τ²U₁)`; `∫|u₀|^{6−2c'}<∞` | **`(6+1)/2 = 7/2`** |

The Jacobian powers **ADD** (`3+2+1 = 6`) onto ONE terminal divisor while the loss stays order 2 ⟹ 7/2.
The independent-divisor product-caricature `z²(x²+y²)` RLCT-collapses to `min`; the DLN sum-form does not,
because the units `U₀,U₁ > 0` stay bounded below on the generic-`A₂` chart. **The coupled form is
load-bearing, not cosmetic:** a formaliser who builds it as independent divisors gets `3/2`, not `7/2`.
[FACT — vslice-cert §5, `vslice_corner.py`; the front-first `g̃`-tube (§2) reproduces `7/2` independently.]

## 2. The corank-2 tube integral (finite at 7/2 via the joint density)

**The pushforward joint density.** The measure on `(s₂,s₃)` is the pushforward of Lebesgue on the
`(Ã₁,A₂)` box, NOT the free law. From the banked codims (`D₁ = codim{rank≤2} = 1`,
`D₂ = codim{rank≤1} = 4`; task #116) the incremental powers are `s₃: D₁`, `s₂: D₂−D₁`:

> `μ{s₂≤t₂, s₃≤t₃} ≍ t₂^{D₂−D₁}·t₃^{D₁}·ℓ(t₂) = t₂³·t₃·ℓ(t₂)`,  `ℓ(t)=1+log(κ/t)` (the tie log, task #116),
> so **`dμ ≍ s₂²·ℓ(s₂) ds₃ ds₂`** on `{s₃≤s₂}`.

[FACT — codims determine the powers; the tie supplies the log. MC-corroborated (`corank2_check.py`: joint
CDF `~ t₃t₂³`, the `s₂`-marginal apparent exponent `~3.3 < 4` = the visible log-tie deflation).
Codex-confirmed.]

**The integral (both `s₃`- and `s₂`-conditions bind at `η<1`).** With `η = 2c'−6`:

    ∫_{cell₂} g̃ dμ ≍ ∫₀^κ ∫₀^{s₂} s₂^{−3}·s₃^{−η}·s₂²·ℓ(s₂) ds₃ ds₂
                   = (1−η)^{−1} ∫₀^κ s₂^{−η}·ℓ(s₂) ds₂     (inner needs η<1)
                   < ∞   ⟺   η < 1   ⟺   **c' < 7/2 = ½(D₂+d₂) = ½(4+3)**,  d₂ = m₀(r−2) = 3.

[FACT — exact; Codex-confirmed term-for-term.] **The tie log is HARMLESS:** `∫₀^κ s₂^{−η}ℓ(s₂)ds₂ < ∞`
for every `η<1` (the log is subdominant to the power); it only strengthens the borderline `η=1` (`c'=7/2`)
divergence, correctly excluded by strictness. (`C_ε t^{D−ε}` form: `t⁴ℓ(t) ≤ C_ε t^{4−ε}` ⟹ tube needs
`β₂ < 4−ε`, still fine for `c'<7/2`, `ε` small.) [FACT.]

## 3. Composition — `∫_{cell₂} g < ∞ for c' < 7/2`

`g ≤ g̃` on `cell₂` (drop `s₁ ≥ κ` to `κ`), so `∫_{cell₂} g ≤ ∫_{cell₂} g̃ dμ < ∞` for `c'<7/2` by §2.
The corank-2 rung is FINITE at the honest threshold, binding EXACTLY at 7/2 (equal to codim-1). Derived
THREE independent ways that agree: (i) front-first `g̃`-tube (§1–2), (ii) resolved corner blow-up
(vslice-cert §5), (iii) `verdict.md`'s single-`σ` radial `∫σ^{−β₂}σ^{D₂−1}dσ`, `β₂=2c'−3`, `D₂=4`.

## 4. The `∧²`-compound σ_min route FAILS — and the Lean audit

**Why the proposed route (`σ_min(∧²P)=s₂s₃`, integrate `(s₂s₃)^{−b}` via `det_product_gram` on `∧²`
factors) does NOT close the rung** — the asymmetry defeats the symmetric weight:

| requirement | condition on `b` |
|---|---|
| pointwise `g̃ ≤ C(s₂s₃)^{−b}` on `cell₂` (diagonal forces it) | `b ≥ (3+η)/2 = c'−3/2 > 3/2` |
| `∫_{cell₂}(s₂s₃)^{−b} dμ < ∞` (inner `s₃`-integral binds) | `b < D₁ = 1` |
| **overlap** | **NONE** (`c'−3/2 > 3/2 > 1`) |

[FACT — Codex-confirmed exactly.] The symmetric compound charges `s₂,s₃` equally; `g̃` charges `s₂` at
the full `3` and `s₃` at only `α'<1`. `det(∧²P(∧²P)ᵀ) = det(PPᵀ)² ≍ (s₂s₃)^{4}` on `cell₂` gives the
same symmetric `(s₂s₃)^{−b}`, `b<1` — no better. **The compound tube is a dead route for corank-2.**

**Lean-shape audit (what to build / consume):**

- **[BUILDABLE, new-but-analogous] The coupled corank-2 front-first majorant.** Shape analogous to the
  banked `twoBlock_radial_le` but with 1 stable + 2 collapsing blocks:
  `∫_{ball_{ℝ^{d_u}} × ball × ball} (κ²‖u‖² + s₂²‖v₂‖² + s₃²‖v₃‖²)^{−c'} ≤ C · s₂^{−3} · s₃^{−(2c'−6)}`.
  CONSUMES: the iterated Haar-dilation + Beta reduction already in `RouteMSJTwoBlockRadial` (the crux),
  the radial leaf `lintegral_norm_rpow_neg_ball_lt_top` (`RouteMSJRadialInt`), `Kbracket`. NEW: one extra
  radial layer (the second collapsing block). Low-risk — it is the crux one dimension up.
- **[THE GAP — not banked, no clean route] The corank-2 tube.** Needs `∫_{cell₂} s₂^{−3}s₃^{−α'} dμ < ∞`
  under the PUSHFORWARD measure. NOT reachable from `det_product_gram` / `σ_min` / `σ_min(∧²P)` (all
  symmetric or single-`σ`; §4). Two routes, neither banked:
  - **(J) joint-density module:** formalise `dμ ≍ s₂²ℓ(s₂)` near `{rank≤1}` for the product pushforward
    (task #116 is the numeric/Jacobian cert; a Lean measure statement is NEW infra — the coarea/Jacobian
    of the `(s₂,s₃)` map on the product tube). Moderate–hard.
  - **(S) the native (S,J) corner (RECOMMENDED):** on `cell₂` (`rank ≤ 1`, so `Ã₁` near `rank ≤ 1`), peel
    `Ã₁` (pivot chart), the `2×2` corank block blows up radially (`u₀`), couples with the boundary row
    (`u₁`) → the vslice-cert §5 corner `u₀²U₀+u₁²U₁`, `∫|u₀|^{6−2c'}` → 7/2, closed by
    `monomialIntegrand_integrable_of_lt`. This is Architecture I. CONSUMES the (S,J) spine
    (`RouteMSJResolution`) — but its endpoints `sjBoundaryPeel` / `sjJointResolution` are UNPROVEN named
    sorries. The MATH is verified (vslice-cert §5); the Lean endpoint is the residual.
- **[NOT banked, and would not help] `∧²P` as an explicit `3×6` minor matrix + `∧²(AB)=∧²A·∧²B` +
  `det(∧²A)=det(A)²`.** Mathlib has `exteriorPower` (algebra), not a compound-matrix API. Building it is
  possible but POINTLESS here — §4 shows the compound weight cannot close the rung regardless.

---

## Firmest / most-likely-to-break / next

- **Firmest.** `g̃ ≍ max(s₂,s₃)^{−3}min(s₂,s₃)^{−(2c'−6)}` (asymmetric, exact, 3 checks + Codex); the tube
  is finite for `c'<7/2 = ½(D₂+d₂)` via `dμ ≍ s₂²ℓ(s₂)`; the log is harmless. The coupling is load-bearing
  (independent → 3/2, coupled → 7/2). All decorrelated-confirmed.
- **Most likely to break the CLEAN plan (already broke it).** The `∧²`-compound `σ_min` route the tide
  hoped to reuse **does NOT close the rung** — the asymmetry (`b≥c'−3/2` vs `b<1`, no overlap) is fatal.
  The corank-2 tube is not a "LAYER 2 on `∧²P`"; it is a genuinely coupled/asymmetric integral. Do NOT
  commission a formaliser on the compound tube — it will hit `+∞` per-term.
- **Next (the redirect).** Build the deep strata via **Architecture I's corner resolution** (route S), not
  Architecture II's compound tube. The smallest concrete step: close `sjJointResolution` for the corank-2
  corner monomial `u₀²U₀+u₁²U₁` (measure `|u₀|³|u₁|²`) → `monomialIntegrand_integrable_of_lt`, reusing the
  banked charge bookkeeping (`Mval_decompose`, `sjChargeBudget_le`). This settles the corank-2 rung with
  the route whose math is already verified, and it is the same endpoint the whole (S,J) descent needs — so
  it is not throwaway. (Route J — the pushforward-density module — is the fallback if the (S,J) endpoint
  proves intractable, but it is strictly more new infra.) **`q=3` deferred until `q=2` validates** (per
  scope); by the same asymmetry it will need the 3-collapsing-block corner, `d₃=0`, `D₃=8`, threshold
  `½(8+0)=4` (slack — not binding, per `verdict.md`).

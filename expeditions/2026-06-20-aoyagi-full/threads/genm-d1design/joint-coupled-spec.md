# joint-coupled-spec — the UNIFIED concentration-point of Lane 1 (the argued-native heart), formalisation-ready

**Seat:** pen-and-paper (design), `genm-d1design`, Lane 1. **Date:** 2026-07-17. **NO Lean.** Pins the ONE
mechanism the three hard `d≤1` arms unify to (b=0 tall / a=0-POWER-interior / d1-a≥u), formalisation-ready, so
the build confirms the argued-native claim. Consumes `b0-wall-adjudication.md`, `d1-atom-spec.md §2/§1bis`,
`codex/{power,wall}-answer.md` (decorrelated), `scripts/d1_*.py` (exact-ℕ).

---

## ★ STATUS (LEAD, per LATE-102 + controller flag): ARGUED-NATIVE, NOT SETTLED until it builds

**Lane-1-fully-native is ARGUED via the joint-coupled resolution — NOT a wall, NOT a cite, but NOT SETTLED
until the build confirms it.** The load-bearing claim: *the general joint-coupled `(Δ,C,Z)` source–tail
incidence resolves at `½·minAdm(M)`, terminating, for general block rank `r,k` — generalizing the banked
FreeBilinear minimal cell.* PROVEN pieces below pin the skeleton; the general resolution is the argued heart
the build must discharge. Two routes are PROVEN-DEAD (do not attempt): plain hIH; the nested-qbox recursion.

## 1. The unified object + widths + resolution architecture

**Common structure (all three hard arms, after the dominant-minor cover fixes the pivot `P` invertible).**
Stratify by the effective source rank `s`; write `r = M₀−s`, `k = M₁−s`. On the pivot chart
`F = [[X, Y],[UX, UY+Δ]]` (`X` the `s×s` invertible pivot, `Δ` the `r×k` exceptional/corank block), the loss is
`freedSchurLoss ≍ ‖B·Z‖²  +  ‖Δ·(C·Z)‖²`, where (POWER Codex §d, PROVEN):
- `B = X·A₀ + Y·C` — the reduced leading block, `s×M₂` (→ the leading layer of `redChain s M = (s, M₂, …)`);
- `C` — a FREE `k×M₂` block (the deep rows of the next layer);
- `Z = prod(deep)` — the deeper product, `M₂×q`;
- `Δ` — the FREE `r×k` block (the source-rank drop of `F`).

**Δ-blow-up (PROVEN, `codex/power` §b/d).** Blow up `Δ = z·Θ` (`z = ‖Δ‖`, `Θ` on the sphere). Single exceptional
divisor, **`ν_z = N = r·k = (M₀−s)(M₁−s)` = peelCharge = codim`{rank F ≤ s}`** (NOT the `W`-rank codim
`(M₀−s)(M₂−s)`). Template `M=(2,3,3,·)@s=1`: `|det DΦ| = |x|^{−2}|z|`, `ν_z = 2`. Gives the charge + the shift
`c' ↦ c' − N/2`. The `Θ`-sphere keeps the pivot core `‖P·Θ‖² ≥ σ_min(P)² > 0` (the radial-peel regularizer,
so `{Δ→0}` / `{Q̃ₚ→0}` corners close KEEPING the charge).

**The residual (PROVEN) → the JOINT COUPLED leaf.** Integrating `Δ` fully leaves
`det(Q Qᵀ)^{−r/2}·‖B·Z‖^{−2(c'−N/2)}`, `Q = C·Z` (`k×q`, `C` FREE, `Z` a product). The reduced core `‖B·Z‖²`
→ `hIH(redChain s M)` at `c'−N/2`; the weight `det(QQᵀ)^{−r/2}` is disposed by the **joint coupled `(Δ,C,Z)`
incidence** (keep `C`, `Z` JOINTLY on the FINITE box; resolve the incidence; NEVER extend to full space nor
recurse via nested qbox). `min_s [ (M₀−s)(M₁−s) + minAdm(redChain s M) ] = minAdm(M)` (0/5292, PROVEN).

**Proposed Lean shape (the concentration-point atom, general-κ, reusing N1–N3 @4626bbad4):**

    theorem jointCoupledIncidence_lt_top (M : Fin (L+1+1+1)→ℕ) (s : ℕ) (…dims…)
        (hIH : ∀ M' : Fin (L+1+1)→ℕ, RouteMBoxThresholdFinite M')
        (c' : NNReal) (hc' : (c':ℝ) < minAdm M / 2) :
        ∫⁻ Δ in matBox r k 1, ∫⁻ C in matBox k M₂ 1, ∫⁻ A_deep in paramsBoxM (deep) 1,
          ofReal ((‖B·prod(deep)‖² + frobSq ((of Δ)·(of C)·prod(deep)))^(-(c':ℝ))) < ⊤

with `B` the reduced core (s×M₂), resolved by: Δ-blow-up (charge `N=(M₀−s)(M₁−s)`) → joint `(Δ,C,Z)` leaf →
`hIH(redChain s M)` at `c'−N/2`. **General-κ:** `w := ‖B·Z‖²` is the positive core (§1 wings: `κ≡0` at the top
sector; here `κ = w > 0`). N1–N3 (the `(r,s)` sector cover + CoV + monomial Jacobian) are SHARED (κ-independent);
N4 (the joint leaf reduction) is the new heart.

## 2. Coverage — the three hard arms instantiate this ONE object (confirm/extend)

- **d1-a≥u (`d=1`, corank rank ≤ 1).** `Δ = Γ` (`a×1` at `b=1`, so `k=1` — the RANK-1 leaf); `C·Z = Q_b` (the
  corank tail); core `w = frobSq(P·Q̃ₚ)`. The joint `(Δ,C,Z)` incidence IS the banked **FreeBilinear** (`γ⊗Q_b`,
  `freeBilinear_box_lt_top`). **This is the MINIMAL cell — PROVEN/banked.**
- **b=0 tall wing (`d=0`, `M₁≤M₀`).** Corank empty; the tall front `[P;C]` (M₀×M₁) is the source-rank object,
  `Δ` its `(M₀−s)×(M₁−s)` drop block, `C·Z = prod(redChain M₁ M)` residual. General `r,k` (NOT rank-1). The
  joint `(Δ,C,Z)` incidence, single-factor (front injective, NOT the d≥2 joint product-corank — `scripts/
  d1_discriminate.py` 0/5292). **ARGUED-native (general r,k).**
- **a=0-POWER-interior (`d=0`, `M₀<M₁`, `M₂≥b+2`, binding `0<s<M₀`).** `Δ` the `(M₀−s)×(M₁−s)` source-rank block
  of the wide front, `C·Z` the reduced tail. General `r,k`. Single-factor (`X` full row rank M₀, tubes
  `{rank X<M₀}` EMPTY — `scripts/d1_discriminate.py`). **ARGUED-native (general r,k).**

**Confirmed:** all three share the `‖B·Z‖² + ‖Δ·C·Z‖²` structure + the Δ-blow-up charge `(M₀−s)(M₁−s)` + the
joint `(Δ,C,Z)` leaf; d1-a≥u is the rank-1 (FreeBilinear) minimal cell, b=0/a=0-POWER are the general-`r,k`
extension. **Coverage of §1-hard (b=0 tall, a=0-POWER-interior) is by the general-`r,k` joint leaf — the
argued-native heart.**

## 3. The FreeBilinear seed / base (PROVEN, banked)

Minimal cell `r=k=1` (a=b=1, e.g. `M=(2,2,1,2)@s=1`): `Δ` scalar, `C·Z` a row, `‖B·Z‖²+‖Δ·(C·Z)‖² = ‖X‖²+
|δ|²‖q‖²` → the banked `freeBilinear_box_lt_top` (`γ⊗z`, `sumSqND_box_lt_top`), threshold `½·min(a+1,D+1)` =
the full `½minAdm` at the cell (Codex `‖X‖²+‖γ‖²‖r‖²` threshold `= (dim X)/2 + min/2`, matching `minAdm`). This
is the SEED the general resolution must reduce to (induction base). PROVEN.

## 4. The 3 KILL-conditions (bake for the formaliser)

1. **NO plain hIH for the hard arms** — they fail a0rev's free-variable-separation (the Gram `det(C·Z·…)^{−r/2}`
   is of a TAIL PRODUCT, not a free box). Plain hIH is ONLY for a=0-BOUNDED + d1-a<u-bounded-w.
2. **NO carried-Gram nested-qbox recursion** — PROVEN WALLS (per-level qbox needs Fibonacci-type `r+k≤M₂`,
   `k+M₂≤M₃`, … NOT supplied by the minAdm charge; smallest failure `M=(2,2,1,2)@s=1`, C-qbox `(1,1,1)` needs
   `1<1`). Use the joint `(Δ,C,Z)` leaf on the FINITE box, NOT an iterated free-layer qbox.
3. **NO naked global Gram-decorated IH** — FALSE (ε-counter `M=(4,3,2)`, `∫|ε|^{−2}=∞`). The Gram is resolved
   LOCALLY by the joint leaf on the finite box, never carried globally.
Plus the carry-`|det J|` guard (never drop the Δ-blow-up monomial Jacobian) and the diamond guard (raw-`Pi`).

## 5. LOG δ-fold (a=0, `M₂ = b+1`)

Free-variable separation STILL holds (`W=F·A₁` free), but the free-front-Gram qbox is MARGINAL. Close by the
**coupled log-density δ-fold**: `ρ(W) ≍ log(1/dist)`, convert via `one_add_log_inv_le_rpow` to `dist^{−δ}`,
absorb `δ` in the loss headroom `Δ = ½(minAdm(redChain M₀ M) − minAdm(M)) > 0` (binding stratum interior — holds
for LOG cells; confirm at build widths). COUPLED estimate, NOT the clean `[qbox]×[hIH]` factorization.
EXPENSIVE-TRANSCRIPTION.

## 6. d1-a<u statements (RESCOPED by lane1shell's genm-tideD recon — mostly BANKED, a WIRE-UP)

**lane1shell's recon (adopted): d1-a<u is a WIRE-UP of the banked genm-tideD edge machinery
(`RouteMSJEdge*`, all green 0-sorry), NOT a fresh 2-sub-lemma build.** The pieces:
- **R2 C-shift bound — BANKED.** `edge_C_shift_bound` (`RouteMSJEdgeCShift:128`, verified): for `v_{j₀} ≠ 0`,
  `W > 0`, `∫_{C ∈ box(a×(u+1))} (W + ‖(of C).mulVec v + β‖²)^{−c'} ≤ 2^{au}·|v_{j₀}|^{−a} · ∫_{ℝ^a}(W+‖x‖²)^{−c'}`
  — β-INVARIANT, the `|v_{j₀}|^{−a}` factor explicit, the RHS radial = `scaledRadialEuclid` (banked
  `_lt_top`, `a<2c'`). Plus `edge_leaf_gamma_bound` (`:257`, adds the γ-box factor `2^a`). Do NOT re-derive.
- **ω-disposal core — BANKED (`projection_rpow_lintegral_uniform`, NOT corner_block).** ⚠ CORRECTION to my
  earlier framing: `‖Q̃ₚω‖²` is a DEGENERATE rank-`u` form (vanishes on `ker Q̃ₚ`, codim `u`), so plain
  `corner_block_lintegral_lt_top` (bounded-below) does NOT apply to it in isolation. The right banked lemma is
  `projection_rpow_lintegral_uniform` (`RouteMSJProjRadial:130`, the SAME lemma `qbox` uses): `∫_{ball}‖P_U w‖^{−a}
  ≤ C` uniformly for `finrank U ≥ r`, `a < r`. Take `U = rowspace(Q̃ₚ)` (dim `u`), `r = u`: gives `∫ ‖P_U ω‖^{−a}
  < ⊤ ⟺ a < u`. The disposal `|v_{j₀}|^{−a} ≤ u^{a/2}‖Q̃ₚω‖^{−a}` and `‖Q̃ₚω‖ ≍ ‖P_{rowspace Q̃ₚ}ω‖` (up to
  the `Q̃ₚ`-conditioning, controlled by the dominant-minor cover). **`a<u` = `a < finrank(rowspace Q̃ₚ) = u`.**
- **The genuinely-new WIRING (the only pieces to build):**
  **(A) the ω-sweep + conditioning** — `ω = Q_b/‖Q_b‖` (a product row) swept over the sphere by the last free
  layer, connecting `edge_leaf_gamma_bound`'s per-fixed-`v` `|v_{j₀}|^{−a}` to `projection_rpow`'s `∫‖P_Uω‖^{−a}`
  (the `Q̃ₚ`-conditioning bridge; small).
  **(B) THE CONNECTION** — after the C-shift leaves `2^{au}|v_{j₀}|^{−a}·scaledRadialEuclid(W,c') = K·W^{a/2−c'}`,
  the residual `∫_{(P,B₁₂,A')} frobSq(P·Q̃ₚ)^{−(c'−a/2)} = frontCollapse(X=[P|B₁₂], m=u, n=M₁)` at exponent
  `c'−a/2`, closed by `frontCollapse_wide_bounded_lt_top` for bounded-w (`M₂ ≤ n−m = M₁−u = b`).
  **Charge bookkeeping (confirmed):** the corank charge is `ab/2 = a/2` (`b=1`); `peelCharge(u) = (M₀−u)(M₁−u)
  = a·b = a`; cut-soundness `minAdm(M) ≤ a + minAdm(redChain u M)` ⟹ `c'−a/2 < ½minAdm(M) − a/2 ≤ ½minAdm(redChain
  u M)` — transfers. frontCollapse adds NO further charge (bounded-w = a separate finite qbox × hIH).
- **The freed-triple ASSEMBLY (lane1shell's flag — check).** genm-tideD's edge lemmas targeted the OLD
  `coupledBoxIntegrand`; the `freedSchurLoss` lemmas (`freedSchurLoss_shear_corank_one_le`
  `RouteMSJEdgeWiring:153`, `corank_integrand_le`) TRANSFER, but wire them into the CURRENT freed-Γ triple via
  `gammaPeelIntegral_schurShearFree_eq` (the socket's reduction), NOT the old `coupledBox`/cell machinery.
**Buildable NOW for bounded-w** (924 cells, `scripts/d1_altu_buildable.py`); §2-independent (uses §1
frontCollapse, not the joint atlas).

## Close

- **Firmest.** The three hard `d≤1` arms unify to ONE object — the joint `(Δ,C,Z)` coupled source–tail
  incidence: Δ-blow-up (charge `(M₀−s)(M₁−s)`, PROVEN) + the joint leaf on the finite box + `hIH(redChain s M)`.
  d1-a≥u is the rank-1 FreeBilinear minimal cell (PROVEN/banked); b=0 + a=0-POWER are the general-`r,k` extension
  (single-factor native, `scripts/d1_discriminate.py` — NOT the d≥2 product-corank wall). Two routes PROVEN-DEAD
  (plain hIH, nested-qbox). min-over-strata `= ½minAdm` (0/5292). LOG = coupled δ-fold.
- **The ARGUED heart (NOT SETTLED — what the build must confirm).** That the general-`r,k` joint `(Δ,C,Z)`
  incidence resolves at `½minAdm`, terminating (reducing to FreeBilinear-type leaves via the finite-box joint
  geometry), for `r,k > 1`. The minimal cell is banked; the general is single-factor native (so NOT a wall) but
  the exact finite-box joint resolution for `r,k>1` is the concentration point — pin the build here; the build
  confirms the argument. Most likely to break: if the general `r,k>1` joint leaf secretly needs a `min≥2`
  determinantal resolution not reducible to the rank-1 seed + single-factor structure (I judge NOT — single-factor
  + the min-over-strata airtight — but this is the unsettled load-bearing claim).
- **Next.** Build: (i) d1-a<u bounded-w NOW (§6 statements, lane1shell greenlit, §2-independent); (ii) the joint
  `(Δ,C,Z)` leaf, seeding from the FreeBilinear minimal cell, extending to general `r,k` (the concentration
  point — concentrate the soundness review here); (iii) LOG δ-fold. On-call for the joint-leaf per-sector
  instantiation + the §6 statements at lane1shell's widths.

Files (absolute): `…/threads/genm-d1design/joint-coupled-spec.md` (this); `b0-wall-adjudication.md`,
`d1-atom-spec.md`, `codex/{power,wall}-{prompt,answer}.md`, `scripts/d1_{corners,power_strata,b0_reach,altu_buildable}.py`.

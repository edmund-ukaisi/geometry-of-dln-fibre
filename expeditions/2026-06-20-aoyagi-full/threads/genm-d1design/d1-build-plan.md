# d1-build-plan — the HONEST formal build recipe for the `¬hcork` (d ≤ 1) native arm of `innerCorankDescent_lt_top`

**Seat:** pen-and-paper (design, decorrelated), `genm-d1design`, Lane 1. **Date:** 2026-07-17. **NO Lean.**
Adjudicates the truth-value: *does the `d = min(M₀−t, M₁−t) ≤ 1` native arm of `(□)` close with the PLAIN
`hIH` + the banked atoms (as the dispatch-spec assumes), or does it hide genuinely-new analytic content?*
Verified three decorrelated ways that CONVERGE: my exact-ℕ census (`scripts/d1_{charge,wings,discriminate,witnesses}.py`,
transcribing Lean's `minAdmRec`), my structural CoV/charge analysis, and a decorrelated `local-codex-consult`
(xhigh, my conclusion withheld — `codex/d1-{prompt,answer}.md`). Consumes the socket
(`RouteMSJDecoratedPeelStep.lean` @ `origin/genm-integration`) + satred `D-cert`/`dispatch-spec`/`waist-pin`/
`c2-atom-supply` + decstep `decstep-cert` (rounds 1–8).

---

## ★ VERDICT — the per-sub-build open-vs-transcription call (LEAD)

**The `d ≤ 1` native arm does NOT close with the plain `hIH` + banked atoms for the majority of cuts.**
Every `d ≤ 1` cut funnels its pivot-energy term through ONE genuinely-new object — the **boxed
wide-product pushforward-density RLCT** (integrate a product `X·Y·Z_deep` of a boxed front `X`, a boxed
next layer `Y`, and the boxed deep product, reducing to `hIH` of a *width-keeping* shorter chain). Where
the front is "wide enough" (density order `A = 0`) this is transcription; where it is not (the deep cells)
the reduction leaves a **Gram-of-a-PRODUCT weight** (a decoration) that the plain `hIH` cannot discharge,
**and the prior design's pointwise density-fold shortcut is UNSOUND** (Codex 2b, PROVEN by a 2×2 counter).
The min-over-strata ARITHMETIC is airtight everywhere (0 fails, `scripts/`), so it is **NOT a wall**, and
the `d ≤ 1` incidence is **NATIVE single-factor** (P-invertibility blocks the `d ≥ 2` product-corank tubes —
so this is NOT another Aoyagi cite); but it is a genuinely-new NATIVE build, not plain-`hIH` transcription.

| sub-build | arm | VERDICT | why |
|---|---|---|---|
| **2a** generic dominant-minor cover (pivot-energy `frobSq(X·Q)` → shorter chain) | density bounded (`A=0`) | **EXPENSIVE-TRANSCRIPTION** | dominant-minor `Finset`-cover + bounded pushforward density + CoV + `hIH` |
| **2a** | density singular (`A>0`) | **OPEN-PROBLEM** | pointwise fold UNSOUND (Codex 2b); needs a SOUND rank-sector / sector atom |
| **2b** corank-one edge (`d=1`) | `a < u` | **EXPENSIVE-TRANSCRIPTION** (modulo 2a) | corner-block joint-sphere + `scaledRadialEuclid` + `hIH`; pivot term still rides 2a |
| **2b** | `a ≥ u` (the §3bis residual) | **OPEN-PROBLEM** | leaves a pivot-Gram `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` on a PRODUCT → needs a Gram-decorated IH |
| **2c** wing `a=0` wide (`M₀<M₁`) | `A ≤ 2Δ` | **OPEN-PROBLEM** | fold UNSOUND; even the "clean" arm needs a sector argument |
| **2c** `a=0` wide | `A > 2Δ` | **OPEN-PROBLEM** | per-stratum front-rank-sector blow-up (native, single-factor, buildable) |
| **2c** wing `b=0` tall (`M₁<M₀`) | `M₂ ≤ a` | **EXPENSIVE-TRANSCRIPTION** | one-shot `qbox` on the FREE front `det(PᵀP+CᵀC)^{−M₂/2}` |
| **2c** `b=0` tall / square (`a=b=0`) | `M₂ > a` (square: always) | **OPEN-PROBLEM** | one-shot `qbox` diverges; reduces to the same wide-product density |

Census (arity-4/5, widths ≤ 6; `scripts/d1_{charge,wings,discriminate}.py`): of the `d ≤ 1` cuts, the
one-shot/clean bound closes only a minority — `d=1 a≥u` one-shot `qbox` closes **1764/3276**; `b=0` one-shot
`qbox` closes **1470/5292** (the square subset **0/1512** — always recurses); `a=0` wide has **2688/5292**
with `A>2Δ`. So ≈half of `d ≤ 1` is OPEN.

**§3bis a≥u residual — CLOSED (as a call): it is a GAP, not a convergence.** The D-cert §3bis "RESOLVED —
folds into the reduced-chain recursive IH" is **incorrect for the PLAIN `hIH`**: the pivot Gram
`det(Q̃ₚQ̃ₚᵀ)^{−a/2}` is a Gram of a deeper PRODUCT (`Q̃ₚ = W'·Z_deep`), not a free box, so `qbox` cannot
dispose it at one level, and "recurse one level" preserves the Gram decoration (Codex 1b, PROVEN). It needs
a pivot-Gram-decorated reduced-chain IH (a mild NATIVE decoration).

---

## 0. The socket + the dispatch (verbatim target)

`innerCorankDescent_lt_top M t ρ κ c' hc' hIH hcited`, `by_cases hcork : 2 ≤ min (M 0 − t) (M 1 − t)`.
The `hcork` branch is `exact hcited …` (CITED — arch1build's box-level `cited_aoyagi_product_corank`; NOT
this recipe). The **`¬hcork` branch** (`d := min a b ≤ 1`, `a := M₀−t`, `b := M₁−t`, `u := t`) is the goal:

    ∫⁻ A' in paramsBoxM (tailChain M) 1, ∫⁻ x in outerDom t a b 1,
      ∫⁻ Γ in {Γ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) 1},
        ofReal ((freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (−c')) < ⊤

with `x = ((P : t×t), (B₁₂ : t×b)), (C : a×t)`, `P` INVERTIBLE on `outerDom` (`IsUnit`),
`freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b`, `Q_p/Q_b` the top-`t` /
bottom-`b` rows of the tail product `Q = (prod (tailChain M) A')` (`q := M_last` cols), and — the load-bearing
identity — `frobSq(P·Q̃ₚ) = frobSq([P|B₁₂]·Q) = frobSq(X·Q)`, `X := [P|B₁₂]` (`t×M₁`, full row rank `t`).

**`decoratedPeelStep_proof` requires EVERY cut `t ∈ [1, min(M₀,M₁)]` finite** (`sjBoundaryPeel` is a full
`Finset.Icc` sum closed by `ENNReal.sum_lt_top` — it *covers* only via `t=1` charts, but the statement demands
all terms finite). So the deepest cut (`d=0` wings) and every `d=1` cut MUST be discharged; there is no
"route each chain through its best cut" escape at this socket.

**Charge invariant (round-5 kill-condition, honoured).** Every reduction is to `redChain u' M` at exponent
`c' − peelCharge(M,u')/2`, `peelCharge(M,u') = (M₀−u')(M₁−u') = (corank-at-deepened-cut)²`. Closes below
`½·minAdm(redChain u' M)` via `minAdm_le_peelCharge_add_redChain` (0/22932, `scripts/d1_charge.py`).

## 1. The load-bearing reframing — every `d≤1` cut funnels through the wide-product density

The pivot-energy term `frobSq(P·Q̃ₚ) = frobSq(X·Q)`, `X = [P|B₁₂]` (`t×M₁`, full row rank `t`),
`Q = A₁·Z_deep` (`A₁ = M₁×M₂` the first tail layer, `Z_deep = prod(M₂,…,M_last)`). Reducing to a shorter
chain requires the pushforward of `(X, A₁) ↦ W := X·A₁` (a `t×M₂` matrix), i.e. the density `ρ(W)` of a
product of a boxed full-row-rank `t×M₁` matrix and a boxed `M₁×M₂` matrix. **This is the SAME object in all
three sub-builds** — 2a is exactly this reduction; the `a=0` wing IS this with `t=M₀`; the `b=0` wing is this
with roles swapped (`([P;C], A₁) ↦ V`, reducing to the *width-keeping* chain `(M₀, M₂,…)`, itself a legal
`hIH` chain `redChain M₀ (…)`-shaped); the `d=1` corank-one dressing sits on TOP of this reduction. So the
`d ≤ 1` arm has ONE genuinely-new heart, plus the corank-one integration.

**Two facts about `ρ(W)` (the crux):**
- **Single-factor / NATIVE (PROVEN, `scripts/d1_discriminate.py`).** `X` has full row rank `t` EVERYWHERE on
  `outerDom` (`P` invertible ⟹ `rank X = t`, regardless of how small `det P` is), so the rank-drop of `W`
  comes only from `A₁` (one factor). The `d ≥ 2` joint product-corank tubes `{rank X = s < t}` are EMPTY
  here (not just null). The achievable-strata min reaches `minAdm` with the NAIVE single-factor charge
  `(M₀−s)(M₁−s)` (0/5292 front rank-sector fails). ⟹ this is NATIVE, NOT the `d≥2` Aoyagi cite; the fix is a
  native decoration, and does NOT enlarge the cited footprint.
- **`ρ(W)` is genuinely SINGULAR at rank-drops of `W`, order `A = max_{j≥1} j(M₂−b−j)` (`b=M₁−M₀`).** It is
  bounded (`A=0`) only when the front is "wide enough"; otherwise `ρ(W) → ∞` at `{rank W < t}`.

## 2a. Generic dominant-minor cover (the pivot-energy reduction — the shared heart)

**What it is.** Reduce `∫∫ frobSq(X·Q)^{−(c'−peelCharge/2)}` (after the corank block is handled) to
`routeMLayerBoxIntegral(redChain t M)(c'−peelCharge/2) 1 < ⊤` via `hIH(redChain t M)`, over the pushforward
`(X, A₁) ↦ W`.

- **Banked atoms it composes (verified on genm-integration):** the MP front-split `routeMLayerBoxIntegral_front_split`
  / `eFront` (`RouteMSJResolution`); the `Params` box CoV `paramsEquivFlat` + `measurableSet_paramsBoxM`
  (`RouteMBoxReduction`); `hIH (redChain t M)`; `minAdm_le_peelCharge_add_redChain` for the threshold shift.
- **NEW atoms to BUILD (its own lemmas):**
  1. the **`t×t`-minor `Finset`-cover of `outerDom`** — `Nat.choose (t+b) t` charts (which `t×t` minor of the
     `t×M₁` matrix `X=[P|B₁₂]` is dominant, `|det X_σ| ≥` the others), + `ENNReal.sum_lt_top`. (P-invertibility
     gives ONE always-nonsingular minor `= P`, but the pushforward Jacobian `|det X_σ|^{M₂}` still degenerates
     as `det P → 0`; the cover moves each point to its dominant minor so the Jacobian is controlled per chart.)
  2. the **bounded pushforward-density lemma** `ρ(W) ≤ K` on a chart where the dominant minor is bounded below
     — ONLY valid where `A = 0` (density genuinely bounded).
- **Measure-level interface hyps (they FAIL pointwise → stated as measure statements):** the socket's banked
  conditional `freedSchurLoss_inner_peel_lt_top` / `_inner_bounded_lt_top` (`RouteMSJFreedPeel`) expose exactly
  `hpiv : 0 < frobSq(P·Q̃ₚ)` (pivot energy positive — FAILS on the tail-degenerate null set), `hG : (Q_bQ_bᵀ).PosDef`
  (corank tail full rank — FAILS on the bottleneck charts), `hc' : a·b/2 < c'` (FAILS on ≈94/480 charts). These
  hold **a.e.**, so the descent supplies them as `ae`-statements, not pointwise.
- **Instance-diamond hazard (`lean/CLAUDE.md`).** The matrix-space measure CoV `(X,A₁) ↦ W` and the transverse
  projector `1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b` (2b) hit the `DecidableEq`/`Inv` diamond (blocks `rw`/`linarith`);
  workaround = `generalize` the composite to a fresh atom across goal + all hyps (round-7 gotcha,
  `RouteMSJInteriorR1`), and use raw-`Pi` instances for every matrix product/reindex (diamond guard).
- **CLASSIFY:** `A=0` = **EXPENSIVE-TRANSCRIPTION** (est. 300–600 LoC: the minor cover + CoV + density bound +
  `hIH` wire; the measured record runs 2–5× short, budget accordingly). `A>0` = **OPEN-PROBLEM** — the naive
  bounded-density is FALSE; needs the sector atom (§2c).

## 2b. Corank-one edge (`d = 1`, both `a,b ≥ 1`, `min(a,b)=1`)

Take `b=1` (the `a=1` case is the transpose dressing). `Q_b` is `1×q`; `Γ = γ ∈ ℝ^a`; `γ·Q_b = γ⊗Q_b`.
Decompose the corank energy `frobSq(C·Q̃ₚ + γ⊗Q_b) = ‖C·v + σγ‖²  +  ‖C·Q̃ₚ·(I−P_{Q_b})‖²` (fragile ω-column +
transverse), `ω = Q_b/‖Q_b‖`, `v = Q̃ₚ·ωᵀ` (a `t`-vector), `σ = ‖Q_b‖`.

- **`a < u` leaf — EXPENSIVE-TRANSCRIPTION.** Drop the transverse (`≥0`); the `Γ,C` integral collapses to
  `|v_{j₀}|^{−a}·scaledRadialEuclid(w, c')`, `w = frobSq(P·Q̃ₚ)` is `C`-free (the R2 β-invariant C-shift,
  D-cert §3bis). Dispose `∫_ω ‖Q̃ₚω‖^{−a}` and reduce `w` via `hIH`.
  - **Banked atoms:** `scaledRadialEuclid_lt_top` (`(a:ℝ)<2p`, `RouteMSJEdgeScalar`); `corner_block_lintegral_lt_top`
    (`RouteMSJRadialPolar`) — applied on the **JOINT (pivot ⊕ corank) sphere** where the sum `‖P·Q̃ₚ‖²+‖Q̃ₚω‖²`
    IS bounded below (its "corner sum" case, `N = a+u`; `‖Q̃ₚω‖²` in ISOLATION is degenerate — do NOT apply
    corner-block to it alone). Then `hIH` on the pivot term (via 2a).
  - **NEW atom:** the ω-uniformisation — `ω = Q_b/‖Q_b‖` is a specific product direction; the last free layer
    `A_last` sweeps `ω` over `S^{q−1}` with a bounded density, converting `∫_{A'}` into the sphere integral.
  - **EQUALITY witness (the `a<u` boundary is tight):** `a = u` is marginal — `∫_ω ‖Q̃ₚω‖^{−a}` is the RLCT of a
    rank-`u` form, finite iff `a < u`, LOG at `a = u`. Cell **`M=(2,2,1,2)` @ `t=1`**: `a=1, b=1, u=1` (`a=u`),
    `minAdm=2`, `redChain=(1,1,2)` `minAdm=1`, `peelCharge=1`, cut-sound `2 ≤ 1+1` (marginal, EQUALITY).
  - **Caveat:** even the `a<u` leaf's pivot term rides 2a's wide-product density (for `b=1`, `X` is `u×(u+1)`,
    nearly square, `A` can be `>0`), so it is transcription only where 2a's density is bounded.
- **`a ≥ u` leaf — OPEN-PROBLEM (the §3bis residual, CLOSED as a gap).** Dropping the transverse is LOSSY
  (`∫‖v‖^{−a}` diverges for `a≥u`). Keeping it and integrating `C` via `gammaAtom_aniso_shifted_eq`
  (`R=Q̃ₚ`, `p=a`, `q'=u`) produces the **pivot Gram `det(Q̃ₚQ̃ₚᵀ)^{−a/2}`** (spending `au/2` — affordable since
  `at ≥ ab` for `t≥b=1`, cut-sound) riding on the reduced loss. But `Q̃ₚ = W'·Z_deep` is a **PRODUCT**, so:
  - `qbox_lintegral_lt_top` disposes a Gram of a **FREE box** only — it cannot take `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` for a
    product `Q̃ₚ` (Codex 1b, PROVEN). The one-shot `qbox` (any `q ∈ {M₂, M_last}`) closes only **1764/3276**
    a≥u cells (`scripts/d1_charge.py`); the rest are marginal and the "recurse one level" carries the Gram
    decoration into the recursion — which the PLAIN `hIH` cannot receive.
  - **Every banked integration order leaves a product-Gram** (Codex 1a, ARGUED, exhaustive over orderings:
    `γ`-first → `‖Q_b‖^{−a}` product-row; `[C|γ]`-together → Gram of `[Q̃ₚ;Q_b]`; drop-transverse →
    `∫‖v‖^{−a}=∞`). **No plain-`hIH` route exists.**
  - **Minimal missing lemma (name it for what it is):** *the pivot-Gram-decorated reduced-chain IH* —
    for `W'∈ℝ^{u×M₂}`, `y_b∈ℝ^{1×M₂}`, boxed `Z_deep∈ℝ^{M₂×q}`, `Q̃ₚ=W'Z_deep`, `Q_b=y_bZ_deep`, `a≥u`,
    `au/2 < c' < minAdm(M)/2`: `∫ det(Q̃ₚQ̃ₚᵀ)^{−a/2}·(‖P·Q̃ₚ‖² + ‖γ·Q_b(I−P_{Q̃ₚ})‖²)^{−(c'−au/2)} < ⊤`.
  - **CLASSIFY: OPEN-PROBLEM** (native, buildable, mild decoration; NOT transcription; NOT a cite). Est. a NEW
    IH-carrier (a `qbox`/`gammaAtom`-family Gram-weighted `RouteMBoxThresholdFinite`) + preservation, ≥ 400–800 LoC.
  - **EQUALITY witness (`a≥u` boundary tight):** `a=u` (`M=(2,2,1,2)@t=1`, above) is the marginal cell where the
    `a<u` route just fails and the pivot-Gram route just turns on.

## 2c. The wings (`d = 0`, deepest cut `t = min(M₀,M₁)`)

**`a = 0` wide (`M₀ < M₁`, `t = M₀`, `b = M₁−M₀ ≥ 1`).** `Γ` empty, `freedSchurLoss = frobSq(X·Q)`,
`X=[P|B₁₂]` (`M₀×M₁` full row rank `M₀`). This is 2a with `t=M₀`, `peelCharge = 0`; reduces to `redChain M₀ M
= (M₀,M₂,…)` at exponent `c'` (no shift), against headroom `Δ = ½(minAdm(redChain M₀ M) − minAdm(M)) ≥ 0`.
- **`A ≤ 2Δ` arm — OPEN-PROBLEM (the fold is UNSOUND).** The prior "pointwise density fold"
  `ρ(W) ≤ K·frobSq(W·Z_deep)^{−A/2}` is **FALSE** (Codex 2b, PROVEN by counter): the density singularity is
  normal to a nonzero rank-deficient `W₀`, but `‖W₀·Z₀‖ ≠ 0` for generic deep `Z₀`, so the RHS stays bounded
  while `ρ → ∞`. The fold survives only after a sector argument that makes the loss detect the normal
  coordinates. So even `A ≤ 2Δ` needs a sector/blow-up (or q2gate's dyadic-shell + Hölder, which reaches
  `½minAdm` with the plain IH + a standalone density atom, but is verified only for `u ≤ 2` — `u = M₀` here).
- **`A > 2Δ` arm — OPEN-PROBLEM (native front rank-sector).** Stratify `rank W = r`; stratum `s = M₀−r` reduces
  to `redChain s M` at charge `(M₀−s)(M₁−s)/2`; `min_s[(M₀−s)(M₁−s)+minAdm(redChain s M)] = minAdm(M)` EXACTLY
  (0/10976 satred, my 0/5292). Banked arithmetic; the ANALYTIC realization (the per-stratum determinantal
  blow-up + its `|det J|` Jacobian, CoV, per-stratum comparator, sum-over-strata) is a genuinely-new measure
  atom (Codex Q2c minimal lemma).
- **EQUALITY witness (`A=2Δ` boundary):** `M=(1,2,3,3)` and `(1,2,3,4)`: `A=1 = 2Δ=1` (fold marginal — and
  unsound even here); `M=(1,2,3,1)`, `(1,2,4,1)`: `A=1,2 > 2Δ=0` (fold fails). (M₀≥2 witnesses exist too.)
- **NEW atom (the `a=0` heart):** the boxed wide-product density RLCT — `∫∫ frobSq(X·A₁·Z_deep)^{−c'} dX dA₁`
  (`X` `M₀×M₁` full-row-rank box, `A₁` boxed) `< ⊤` for `c' < ½minAdm(M)`, via the front rank-sector reducing
  each `s`-chart to `hIH(redChain s M)`. **CLASSIFY: OPEN-PROBLEM** (native, buildable, NOT the fold). Diamond
  guard: raw-`Pi` for `X·A₁ ↦ W`. Trap: the per-`P` CoV `z₀↦P·z₀` has `|det P|^{−M₂}` non-integrable — use the
  `X·A₁` pushforward, never the per-`P` Jacobian (waist-pin §4).

**`b = 0` tall (`M₁ < M₀`, `t = M₁`) + the square (`a=b=0`, `M₀=M₁`).** `Γ` empty, `freedSchurLoss =
frobSq([P;C]·Q_p)`, `[P;C]` (`M₀×M₁`, full COLUMN rank `M₁`, a FREE matrix), `Q_p = prod(redChain M₁ M)`.
- **`M₂ ≤ a` arm — EXPENSIVE-TRANSCRIPTION.** The crude col-rank factorisation `frobSq([P;C]·Q_p) ≥
  σ_min([P;C])²·frobSq(Q_p)` gives `[∫_{[P;C] box} σ_min^{−2c'}] · [hIH(redChain M₁ M)]`; the first is a FREE-box
  Wishart = `qbox_lintegral_lt_top` with `(b_box,q_box,exp) = (M₁, M₀, M₂)`, converges iff `M₂ ≤ a =
  M₀−M₁` (`M₂ < M₀−M₁+1`). **Banked:** `qbox_lintegral_lt_top` + `hIH`. Est. 150–300 LoC.
- **`M₂ > a` arm (square: ALWAYS) — OPEN-PROBLEM.** The crude factorisation diverges. The sound route
  recombines `([P;C], A₁) ↦ V := [P;C]·A₁` (both FREE) and reduces to the width-keeping chain `(M₀,M₂,…)` via
  `hIH` — i.e. the SAME boxed wide-product density as `a=0` (roles swapped), NOT a clean transpose (the tall
  map is injective not surjective; Codex flag). **CLASSIFY: OPEN-PROBLEM.**
- **EQUALITY witness (`M₂ = a+1` boundary):** `M=(2,1,1,·)`: `a=1, M₂=1=a` → `qbox` STRICT (one-shot);
  `M=(2,1,2,·)`: `a=1, M₂=2=a+1` → `qbox` MARGINAL (`a = q−b+1`), one-shot FAILS. The square is `M₂ > 0 = a`
  always → always the OPEN arm (Codex's 2×2 `ρ(diag(½,ε)) ≍ log(1/ε)` proves the divergence directly).

## 3. The glue + the KILL-GUARD

`¬hcork` (`min a b ≤ 1`) dispatches: `by_cases a = 0` (→ `a=0` wing) / `by_cases b = 0` (→ `b=0` wing/square)
/ else `d=1` corank-one (`by_cases a < u`). Each stitches into the freed-Γ triple at the consistent charge
`peelCharge M u' = (corank-at-cut)²`, feeding `hIH`. The corank block `Γ` is empty for `d=0` (0 rows / `Q_b`
empty — `frobSq_empty_rows`, the socket's `Apiv:=0` weld), integrated (gammaAtom/corner-block) for `d=1`.

**KILL-GUARD (bake as kill-conditions):**
1. **Never route `min-corank ≥ 2` here** (that is `hcited`); the `d≤1` dispatch is entered only under `¬hcork`.
2. **Never carry a decoration into the PLAIN `hIH`** — `hIH` is the undecorated `RouteMBoxThresholdFinite`. If a
   sub-build produces `det(product-Gram)^{−a/2}` on the reduced box, it CANNOT be handed to `hIH`; it needs the
   native decorated IH (2b a≥u, 2c OPEN arms). Handing it to `hIH` is UNSOUND.
3. **Never use the pointwise density fold** `ρ ≤ K·frobSq(W·Z_deep)^{−A/2}` (UNSOUND, Codex 2b). Use the rank-
   sector / sector atom or the dyadic-shell+Hölder route.
4. **Never `qbox` a Gram of a PRODUCT** (only a free box); and never the CORANK Gram `det(Q_bQ_bᵀ)` at edge dims
   (`a<q−b+1` is `a<a`=FALSE — the "atom trap"); the pivot Gram `det(Q̃ₚQ̃ₚᵀ)` (full rank `u`) is the safe one,
   but still a product → needs the decorated IH.
5. **Carry `|det J|`** (the transverse determinantal Jacobian = the stratum codim) — never drop it (tide-D KILL).

## 4. The headline correction + decorrelation

**The prior design's "plain `hIH` closes `d ≤ 1`" (decstep round-6/7 §3, dispatch-spec §2) is TOO OPTIMISTIC
for the deep cells.** decstep round-7 Q2 flagged it as INFERENCE ("until the §3 c=1 + wings + dominant-minor
are implemented"); lane1shell found the assumed assembly lemmas do not exist; this recipe adjudicates the
inference FALSE for the majority (the `u≥3` / `a≥u` / `M₂>a` cells). The correction is **not a wall and not a
new cite** — the `d≤1` incidence is NATIVE single-factor (P-invertibility, discriminator (1)); it is a mild
NATIVE decoration (a `qbox`/`gammaAtom`-family Gram-weighted IH) OR the standalone boxed-wide-product-density
atom. Three decorrelated lines converge: my exact-ℕ census (0-fail arithmetic + one-shot-fails-for-majority),
my structural CoV/charge analysis, and Codex xhigh (Q1 & Q2 both **OPEN-PROBLEM**, the fold PROVEN unsound).

## Close

- **Firmest result.** The `d ≤ 1` native arm is NOT ~3 plain-`hIH` transcription sub-builds; it funnels to ONE
  genuinely-new NATIVE object — the **boxed wide-product / joint pushforward-density RLCT** (reducing to `hIH`
  of a width-keeping shorter chain), plus a **pivot-Gram-decorated IH** for the `d=1 a≥u` corank-one dressing.
  The min-over-strata arithmetic is airtight (0 fails), the incidence is single-factor NATIVE (not the `d≥2`
  cite), so it is buildable, not a wall — but it needs a mild native decoration / new atoms, and the prior
  pointwise-fold shortcut is UNSOUND. Transcription-clean only: `d=1 a<u` (modulo 2a), `b=0` `M₂≤a` one-shot
  `qbox`, and the `A=0` bounded-density charts.
- **Most likely to break THIS call.** (i) If a formaliser finds a `qbox`/`gammaAtom` composition that disposes a
  PRODUCT-Gram at one level (would collapse 2b-a≥u and 2c-open to transcription) — unlikely (Codex 1b PROVEN the
  product-Gram is not a free-box qbox), but it is the escape to watch. (ii) The dyadic-shell+Hölder route
  (q2gate) might extend the plain-`hIH` scope beyond `u≤2` to more `d≤1` cells — worth re-checking before
  committing to a decorated IH. (iii) My "single-factor NATIVE" rests on P-invertibility making `rank X = t`
  always; if some chart genuinely needs `rank X < t` the `d≥2` cite could leak into `d≤1` (I find it does not —
  the achievable strata reach `minAdm` with naive charge, 0/5292).
- **Next construction / consult.** Commission the **boxed wide-product-density RLCT** as a focused NATIVE atom
  (Codex Q2c's lemma: `∫∫ ‖XYZ‖^{−2c} < ∞` for `2c < min_s[(M₀−s)(M₁−s)+minAdm(s,M₂,…)]`, each `s`-chart
  dominated by `hIH`), replacing the unsound fold with a sound rank-sector/sector argument — this ONE atom is
  the heart of `a=0`, `b=0`-`M₂>a`, the square, and (via the corank-one C-transversality) `d=1`. Then decide the
  architecture: a mild `qbox`-family Gram-decorated `RouteMBoxThresholdFinite` IH, vs. standalone atoms feeding
  the plain driver. Either way, the endgame `(□)` fill is LARGER than the "d≤1 transcription" the round-6 spec
  assumed. Recommend surfacing to the controller BEFORE any formaliser tide sinks in.

Files (absolute): `…/threads/genm-d1design/d1-build-plan.md` (this); `codex/d1-{prompt,answer}.md` (decorrelated,
Q1 & Q2 OPEN-PROBLEM); `scripts/d1_{charge,wings,discriminate,witnesses}.py` (exact-ℕ census + witnesses).
Consumes: satred `D-cert`/`dispatch-spec`/`waist-pin`/`c2-atom-supply`; decstep `decstep-cert`; the socket
`RouteMSJDecoratedPeelStep.lean` @ `origin/genm-integration`.

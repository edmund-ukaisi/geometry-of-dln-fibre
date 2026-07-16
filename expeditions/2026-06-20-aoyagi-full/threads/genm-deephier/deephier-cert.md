# deephier — the hierarchical (non-comparable-scale) deep degeneration: **NO WITNESS.** The honest deep codim is the reduced-rank floor `minAdm((u,)+deep)`, and the gate reduces to the `t=u` term

**Seat:** pen-and-paper (design-space adjudication, OBSTRUCTION-primary, decorrelated), aoyagi-full Stage 2,
`genm-deephier`. **Date:** 2026-07-16. **NO Lean edits, NO build.** Exact Newton-polyhedron / monomial-RLCT
ray LP (`scipy.optimize.linprog`, exact rational vertices), exact `ℕ` `minAdm`/`CR` recursions; Monte-Carlo
tail-exponent only as a GUIDE (labelled). Decorrelated `local-codex-consult` (gpt-5.x, my conclusion WITHHELD,
prompt "reason it out, decide"): `codex/deephier-{prompt,prompt-tight,answer}.md`. **CONCURS on all three points,
decorrelated (run 3: high-effort, self-contained, NO repo access, my conclusion withheld) — independently
derived the SAME closed form `minAdm(u,m,n)`, the SAME cross-layer weighted-average bound `Σc_i d_i/Σc_i ≥
min_i d_i ≥ minAdm`, and the SAME `t=u`-term verdict `minAdm(M₀,M₁,deep) ≤ ab + minAdm(u,deep) ⟹ NO undercut`.**
(Runs 1–2 failed: run 1 exhausted budget exploring the repo breaking decorrelation; run 2 timed out; run 3
succeeded self-contained. The verdict rests on exact algebra regardless.)

**Consumed / verified (signatures, not paraphrased):** `genm-diagbfix/diagbfix-cert.md` (the (3a) winner, the
§6b hierarchical flag it left open — this thread retires it; the local model `loss ≍ |y|²+τ²|W_lost|²`, charge
`det(Q_bQ_bᵀ)^{−a/2}`, deep measure `τ^{κ_k−1}dτ`); `genm-deepgate/deepgate-cert.md` (the single-scale/comparable
gate `C_k = min(uρ, u(ρ−k)+κ_k−γ_{ρ−k}) ≥ 2T1_q`, the exact `κ_k = CR(deep,ρ−k)` and
`γ_s = max_{max(0,b−s)≤h≤b} h(a+b−s−h)` definitions, §4/§6 the model-dependence caveat); repo anchor
`lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean` (`Mval` = the geometric codim = the **Aoyagi-Watanabe
(2005) reduced-rank-regression closed form**, `rlct = ½·codim` — the cited fact my reduction rests on).
Scripts (this thread, `scripts/`): `deephier_lp.py` (the per-stratum multi-scale ray LP), `verify_minadm_identity.py`,
`confirm_floor.py`, `arity4_min_compare.py`, `gate_reduction.py`, `multilayer_check.py`, `crosslayer_ray.py`,
`validate_rlct.py`, `mlayer_numeric.py`.

---

## ★ VERDICT — **the gate `C_k ≥ 2T1_q` HOLDS for ALL hierarchical / non-comparable degenerations. NO WITNESS. Kill-condition NOT triggered.**

`min_k C_k^{hier} < 2T1_q`: **0 cases** over arities 4–7 (LP with charge, exhaustive within the rankgen scope).
The `(3a)` deep-stratum model-dependence that diagbfix §6b flagged is **RETIRED**. But the retirement comes with
a **sharp correction to the deepgate reasoning that the formaliser must wire correctly** (see ★2, ★3):

**★1. The single-scale radial `τ^{κ_k−1}dτ` is the DIAGONAL of a multi-scale measure over the lost singular
values — and hierarchical (unequal-scale) rays genuinely BEAT the diagonal.** The honest per-stratum effective
codim (RLCT-codim, computed by the min over Newton-polyhedron rays) is **strictly smaller** than deepgate's
single-scale `C_k^{single}` at the deep strata. Concretely `(4,4,4,4)@u=3`: single-scale gives `C_3=C_4=12`
(the naive `κ_k`), but the honest hierarchical resolution gives `C_3^{hier}=C_4^{hier}=10`. The hierarchical
degeneration erodes **all** of deepgate's per-stratum slack. **This is real — deepgate's "deep strata dominated
with room to spare (`κ_k ~ k²` beats charge `~ k`)" is single-scale-specific and does NOT survive.**

**★2. But the erosion bottoms out EXACTLY at the reduced-rank-regression floor `minAdm((u,)+deep)`, and NEVER
below.** For a single deep matrix the honest codim is a closed form (§2); over 1485 binding cuts × all strata,
`C_k^{hier} ≥ minAdm((u, M₂, n))` with **0 below**, and `min_k C_k^{hier} = minAdm((u,M₂,n))` **exactly**. The
floor is the Aoyagi RRR codim of the `(u-row front) × (deep chain)` product `‖F·Z_deep‖²` — validated against the
exact `minAdm(3,4,4)=10` (NOT the naive polyhedron's 12).

**★3. The gate reduces to a `∀`-PROVABLE `ℕ` inequality — the `t=u` term of the front `minAdm` recursion:**

    C_k^{hier}  ≥  minAdm((u, M₂,…,M_last))  ≥  minAdm(M) − a·b  =  2·T1_q,

the second inequality being **exactly** `minAdm(M) = min_t (M₀−t)(M₁−t)+minAdm((t,)+deep) ≤ (M₀−u)(M₁−u)+minAdm((u,)+deep) = ab + minAdm((u,)+deep)`.
This **upgrades the deep-stratum gate from the finite scan (deepgate 0/5736, diagbfix 0/5736) to a genuine
`∀`-argument** — addressing the controller's bedrock flag directly. **Equality (zero margin) holds precisely when
`u` is a `minAdm`-minimiser (`u = t★`)** — 693/1485 (arity 4), 686/1022 (arity 5), 751/940 (arity 6), 415/455
(arity 7) cuts. So the honest gate is **TIGHT**, not "dominated with room."

**★4. The charge never bites hierarchically either.** `C_k^{hier}(with charge) = C_k^{hier}(loss-only)`, never
below `minAdm((u,)+deep)` (0 cases). The corank Gram charge `det(Q_bQ_bᵀ)^{−a/2}` is inert at the binding ray
(as deepgate found single-scale at `k=1`) — its exponent `γ^{hier}(e)` is dominated at the optimum.

**★5. The multi-layer "one block ~ `t`, another ~ `t²`" degeneration gives MORE codim, not less.** Cross-layer
scale-difference rays (layer `i` ~ `τ^{c_i}`) have effective codim = a weighted average of the layer dimensions
`≥ min_i(w_{i-1}w_i) ≥ minAdm` — **0/9288** chains where it dips below `minAdm`. The binding directions are the
reduced-rank blow-ups (rank-split *within* the matrices), captured exactly by the intermediate-rank `min` in
`minAdm` — which is itself the honest multi-scale-across-layers resolution (Aoyagi).

---

## 1. The exact objects and the single-scale model (recap, deepgate §1)

Binding cut `u = t★+j` (`1≤j<r`), `a=M₀−u`, `b=M₁−u`, `ρ = deepTailMin M = min(M₂,…,M_last)`, `n=M_last`,
rankgen `a+b ≤ ρ−1`. `Z_deep` = product of deep layers `(M₂,…,M_last)`, an `M₂×n` matrix, generic rank `ρ`.
Target: `∫ frontChargeIntegrand < ⊤` for `q < T1_q := (minAdm(M)−ab)/2`.

deepgate's **comparable** (single-scale) per-stratum local model at `{rank Z_deep = ρ−k}`:

    integrand ≍ τ^{−γ_{ρ−k}} · (|y|² + τ² |W_lost|²)^{−q},   measure  dy · dW_lost · τ^{κ_k−1} dτ,
    y ∈ ℝ^{u(ρ−k)},  W_lost ∈ ℝ^{uk},  κ_k = CR(deep, ρ−k),  γ_s = max_{max(0,b−s)≤h≤b} h(a+b−s−h).

Integrating `y`, then the `W`-radial, then `τ` gives `C_k^{single} = min(uρ, u(ρ−k)+κ_k−γ_{ρ−k})`, convergence
for `2q < C_k^{single}`. **Comparable = all `k` lost singular values scale like the single `τ`.** The `τ`-radial
is the DIAGONAL of the honest `k`-dimensional singular-value degeneration.

---

## 2. The hierarchical model — the honest RLCT is the min over Newton-polyhedron rays

**Single deep matrix (`κ_k` determinantal).** Near a rank-`(ρ−k)` point, the normal slice `E` is the Schur
complement, a `p×k` matrix with `p = k + |M₂−n|` and `κ_k = p·k`. Its `k` singular values `σ₁≥…≥σ_k` are the
lost ones; the measure in singular coordinates is

    dμ(σ) = ∏_{i<j}|σᵢ²−σⱼ²| · ∏ᵢ σᵢ^{p−k} dσ.

The loss becomes multi-scale: `loss ≍ |y|² + Σ_{i=1}^k σᵢ²|W_i|²`, `W_i∈ℝ^u`. The single-scale `τ^{κ_k−1}dτ` is
`dμ` restricted to the diagonal `σᵢ=τ` (Vandermonde `→ τ^{k(k−1)}`, `∏σ^{p−k} → τ^{k(p−k)}`, `dσ → τ^{k−1}dτ`,
total `τ^{κ_k−1}dτ` ✓). The **honest RLCT** is the min over ALL rays `σᵢ=τ^{eᵢ}` (ordered `e₁≤…≤e_k`; in the
open ordered sector the Vandermonde `→ ∏σᵢ^{2(k−i)}`, an exact monomial), `y=τ^{f}`, `W_i=τ^{gᵢ}`:

    C_k^{hier} = 2 · min_ray  [ Σᵢ eᵢβ_i + u(ρ−k)·f + u·Σ gᵢ − γ^{hier}(e) ] / D,
    D = min(2f, min_i 2(eᵢ+gᵢ)),  β_i = (p−k+1)+2(k−i),  γ^{hier}(e)=max_h [a(e₁+…+e_h) − h(s−b+h)].

Normalising `D=1` gives a linear program per stratum (`scripts/deephier_lp.py`). Solving:

    C_k^{hier,loss} = u(ρ−k) + Σ_{i=1}^k min(β_i, u)   (closed form; `f=½`, `eᵢ=½` iff `β_i<u` else `gᵢ=½`).

Since `Σβ_i = κ_k` and `min(β_i,u) ≤ β_i`, **`C_k^{hier} ≤ C_k^{single}`** — the hierarchical rays beat the
diagonal by `Σ_{i:β_i>u}(β_i−u)`. This bites whenever `β_1 = p+k−1 > u`, i.e. at the deep strata.

**Why the naive Newton polyhedron of `‖F·Z_deep‖²` over-estimates.** In the raw `(F,Z_deep)` entry coordinates,
the Newton-polyhedron RLCT of `‖F Z_deep‖²` gives `M₂·min(u,n)/2` (= `6`, i.e. codim 12, for `(4,4,4,4)`) — but
`‖F Z_deep‖²` is Newton-**degenerate** (bilinear product), so the true RLCT is **strictly smaller**. The SVD/
singular-value resolution above IS the birational resolution of that degeneracy; it gives the honest RLCT.

---

## 3. Validation — the honest floor is the exact Aoyagi RRR codim `minAdm((u,)+deep)`

The honest full-collapse (`k=ρ`) codim of `loss=‖F·Z_deep‖²` (F free `u×M₂`, Z_deep free) is the reduced-rank-
regression codim of the two-layer product, `= minAdm((u, M₂, n))`. Checks:

- **`(4,4,4,4)@u=3`:** σ-LP gives `10`; exact `minAdm(3,4,4)=10`; naive polyhedron `12`. **σ-LP matches the RRR
  codim, refuting the naive polyhedron** (`scripts/validate_rlct.py`, `deephier_lp.py`).
- **Identity `C_k^{hier} ≥ minAdm((u,M₂,n))`, `min_k = minAdm((u,M₂,n))`** — arity 4, widths 1..9: `0` below over
  1485 cuts; `min_k` mismatch `0` (`scripts/confirm_floor.py`). The 315 "above" are the shallow strata.
- **Charge:** `C_k^{hier}(charge) < minAdm((u,)+deep)`: `0` cases (`verify_minadm_identity.py`).
- **MC tail-exponent (GUIDE only):** RRR `(2,2,2)` measured `λ≈1.54` vs `minAdm/2=1.5`; `(2,3,2,3)` `≈2.21` vs
  `2.0` (`scripts/mlayer_numeric.py`). Deep products under-resolve — MC decides nothing here; the LP + exact
  `minAdm` do.

---

## 4. The obstruction (rigorous, all arities) — strata-partition + the `t=u` term

1. **Honest deep-factor RLCT-codim `≥ minAdm((u, M₂,…,M_last))`.** The full deep integral
   `∫ ‖F·Z_deep‖^{-2q}·charge·(Lebesgue on deep layers, A_cor, F)` is the reduced-rank-regression / DLN
   multiplication-map integral of the `(u-row front)×(deep chain)` product; its loss-fibre-over-0 codim is
   `minAdm((u,)+deep)` (**the paper's own QIP/`minAdm` codim theorem** applied to the SUB-CHAIN `(u,)+deep` —
   a GEOMETRIC/native codim). The `minAdm` recursion `min_t (·)(·)+minAdm((t,)+…)` over intermediate ranks **IS**
   the multi-scale-across-layers resolution — so hierarchical/non-comparable degenerations are already accounted
   for; the honest RLCT-codim (min over the toric fan of chart radial exponents) bottoms out at this value (LP,
   §2–3). The charge is inert at the binding ray (★4), so it does not lower this. **For the `(□)` FINITENESS
   direction only the LOWER bound `rlct(deep) ≥ minAdm((u,)+deep)/2` is used — earned NATIVELY by a covering
   monomial resolution whose every chart radial exponent `≥ minAdm((u,)+deep)`, then elementary
   `∫r^{c−1−2q}dr < ⊤`. The `rlct = ½·codim` EQUALITY (`cited_aoyagi_dln`) is NOT needed here — it is a payoff-only
   citation (see §7 Q2).**
2. **The deep-rank strata `{rank Z_deep = ρ−k}` PARTITION this integral** ⟹ `RLCT_total = min_k RLCT_stratum`,
   i.e. `2·RLCT_total = min_k C_k^{hier} = minAdm((u,)+deep)`, hence **`C_k^{hier} ≥ minAdm((u,)+deep)` for every
   `k`** (each `≥` the min).
3. **`minAdm((u,)+deep) ≥ minAdm(M) − ab = 2T1_q`** — the `t=u` term of the front recursion (a one-line `∀`-proof,
   0 violations arities 4–7 in `scripts/gate_reduction.py`, and it is an identity, not a scan).
4. ⟹ **`C_k^{hier} ≥ 2T1_q` for all `k`, all hierarchical degenerations.** ∎ Kill-condition
   (`min_k C_k^{hier} < 2T1_q`) NOT triggered: `0` cases, arities 4–7 (`scripts/arity4_min_compare.py`,
   `multilayer_check.py`).

**The brief's explicit case (multi-layer, one block ~ `t`, another ~ `t²`).** Uniform-per-layer rays
`X_i ~ τ^{c_i}` have codim = weighted average of layer dims `Σᵢ(w_{i-1}w_i)c_i / Σc_i ≥ min_i(w_{i-1}w_i) ≥
minAdm(chain)` (single-layer collapse gives product 0 at codim `w_{i-1}w_i`), so **cross-layer scale differences
NEVER undercut** — `0/9288` (`scripts/crosslayer_ray.py`). Worked: `(2,2,2,2)`, `c=[1,1,2]` → codim `4 > minAdm=3`.

---

## 5. Scoped conditions (where each ingredient bites)

- **Rankgen scope `a+b ≤ ρ−1`** (binding strict shells): keeps the charge non-integrable wall `a+b ≥ ρ+1` safely
  outside (deepgate §4); also `d=ρ−b ≥ a+1`, `k=1` charge-inert.
- **The floor is the RRR codim of the sub-chain `(u, M₂,…,M_last)`** — NOT `minAdm(deep)` and NOT the
  determinantal `(M₂−s)(n−s)`. Using `minAdm(deep)` (deepgate §3 full-collapse form) is a *different, looser*
  reduction; the honest per-stratum floor is `minAdm((u,)+deep)`, which the `t=u` term ties to `2T1_q`.
- **Equality `C_k^{hier} = 2T1_q` iff `u=t★`** (the cut is a `minAdm`-minimiser). At strict shells `u>t★` there is
  positive margin `minAdm((u,)+deep) − 2T1_q`; the honest binding stratum is then the shallow `k` / `uρ` cap, and
  the deep strata sit AT the floor (no `κ_k` slack).

---

## 6. Levels kept apart

- **Quiver/orbit & codim `(C,θ)`:** untouched; consumed only via `minAdm`/`CR` (geometric codim). The `t=u` term
  and the RRR-codim identity are `ℕ` facts about `minAdm`.
- **RLCT cap:** this cert works at the per-stratum **finiteness / RLCT-codim** level (is the honest deep-factor
  RLCT-codim `≥ 2T1_q`?), which needs only the LOWER bound `rlct(deep) ≥ T1_q` — obtainable NATIVELY (§7 Q2), NOT
  the `rlct = ½·codim` equality (`cited_aoyagi_dln`, a payoff-only citation). `(□)` remains TRUE throughout.
- **The single-scale `C_k` is a strict OVER-estimate of the honest per-stratum RLCT-codim at deep strata** — do
  not lift a single-scale "room to spare" as if it were the honest margin.

---

## 7. Discharge guidance for the formaliser (controller Q1/Q2 — MATH content; Lean route deferred to controller)

*I hold no Mathlib-feasibility model and do not prescribe the Lean route; below is the mathematical content the
discharge rests on, and the object distinctions that must not be conflated (`scripts/discharge_check.py`).*

**Q1(a) — Is `deepGate_branch`'s `C_k^{single}` formula directly usable as a codim lower bound for finiteness?
NO.** `C_k^{single} = min(uρ, u(ρ−k)+κ_k−γ_{ρ−k})` is the radial exponent of the **single-scale (comparable)
chart**, and it is `≥` the true per-cell RLCT-codim — `C_k^{hier} ≤ C_k^{single}`, **STRICT at 1415/4386 deep
strata** (`(4,4,4,4)@u=3`: `k=3,4` give `C_single=12` but true `C_hier=10`). So `C_k^{single}` is an
OVER-estimate, not a lower bound: "true codim `≥ C_k^{single}`" is the WRONG direction, and the single-scale
chart does not cover the hierarchical corners of the cell. `deepGate_branch`'s `ℕ` inequality stays true but
bounds only the single-scale sub-chart. **The correct discharge is the RRR-floor: true per-cell codim `≥
minAdm((u,)+deep) ≥ 2T1_q`.**

**Q1(b) — the GEOMETRIC input.** The needed object is `codim{F·Z_deep = 0}` for the SUB-CHAIN
`(u, M₂,…,M_last)` `= minAdm((u,)+deep)` — the paper's OWN QIP/`minAdm` codim, instantiated at the sub-chain
obtained by prepending the front-cut width `u` to the deep widths. **⚠ This is a DIFFERENT object from
`κ_k = CR(deep, ρ−k)`** (the deep-parameter MEASURE codim, `~k²`): `4249/4386` strata have `κ_k ≠
minAdm((u,)+deep)`. So a banked product-rank-locus codim that computes `CR(deep,·) = κ_k` is the WRONG object
for the floor; the floor is `minAdm` of the sub-chain `(u,)+deep`. What must be TRUE: (i) the deep cell's
loss-fibre codim `= minAdm((u,)+deep)` [QIP on the sub-chain]; (ii) `minAdm((u,)+deep) ≥ minAdm(M) − ab` [the
`t=u` term — trivial `ℕ`]. *(Whether the right `minAdm((u,)+deep)` instance is banked or needs building is a
Lean-feasibility call for the controller.)*

**Q2 — ★ AXIOM FOOTPRINT: NATIVE, not `cited_aoyagi_dln`.** `(□)` needs only the LOWER bound `rlct(deep) ≥
T1_q`. Native route: a COMPLETE monomial atlas of the deep cell whose every chart has radial exponent `≥
minAdm((u,)+deep)` [native QIP codim] + elementary `∫₀^δ r^{c−1−2q}dr < ⊤` for `2q < c` + the `t=u` term ⟹
`rlct(deep) ≥ minAdm((u,)+deep)/2 ≥ T1_q`. **The `rlct = ½·codim` EQUALITY (`cited_aoyagi_dln`) is NOT needed
for `(□)` finiteness** — it is required only for the PAYOFF (exact `rlct = C/2`). **CAVEAT:** "native" is
contingent on the atlas being COMPLETE (covering the hierarchical corners) — that IS the real deep-atlas build
(the ~2 sorries), now with the CORRECT floor `minAdm((u,)+deep)` (NOT the single-scale `C_k`). Watanabe's
universal `rlct ≤ codim/2` is the FREE direction and does NOT suffice (wrong direction): the lower bound must
be earned by the covering resolution.

**Clean alternative to flag.** The deep-factor finiteness `= (□)` for the shorter sub-chain `(u,)+deep` (one
fewer layer — the front two widths `M₀,M₁` collapsed to the single cut-width `u`). If `(□)` is proved by
induction on chain LENGTH, this is a valid IH and is **non-circular** (strictly shorter chain) — reframing
diagbfix's "no shorter-chain IH" as "a shorter-chain IH that is legitimate under length-induction." This may be
cleaner than a standalone RRR-floor atlas; both are native. Route choice is the controller's.

---

## 8. Close

- **Firmest result.** `C_k^{hier} ≥ minAdm((u, M₂,…,M_last)) ≥ minAdm(M) − ab = 2T1_q` for every `k` and every
  hierarchical / non-comparable-scale degeneration (within-matrix unequal singular values AND cross-layer scale
  differences). **NO WITNESS**; kill-condition NOT triggered (0 over arities 4–7). The `(3a)` model-dependence is
  **RETIRED**. The gate is upgraded from a finite scan to a `∀`-argument: strata-partition + the native QIP
  codim `minAdm((u,)+deep)` (the paper's codim theorem on the sub-chain) + the `t=u` term (a one-line `ℕ`
  inequality). Decorrelated Codex (no repo access) independently derived the same closed form and `t=u` verdict.
- **The sharp correction (bedrock).** deepgate's *verdict* (min gate `≥ 2T1_q`, holds) is correct and unchanged;
  its *reasoning* ("deep strata dominated with room to spare, `κ_k ~ k²` beats the charge") is single-scale-only
  and **illusory** under honest resolution — hierarchically the deep strata drop to the floor `minAdm((u,)+deep)`
  and are TIGHT, not slack. They were never the binding stratum, so the conclusion is safe; but the formaliser
  must NOT discharge `(3a)` via a per-stratum `κ_k ~ k²` domination (false hierarchically). **The honest
  discharge is the RRR-floor reduction: `C_k ≥ minAdm((u,)+deep) ≥ 2T1_q` via the `t=u` term.**
- **Most likely to break it.** (a) The charge argument at very deep strata for MULTI-LAYER is verified single-
  matrix + argued structurally (charge depends only on `Z_deep`'s `M₂×M₂` Gram, identical to single-matrix), not
  by a from-scratch multi-layer charge LP — a residual `INFERENCE`. (b) The NATIVE lower bound `rlct(deep) ≥
  minAdm((u,)+deep)/2` (§7 Q2) is contingent on the deep atlas being COMPLETE (covering the hierarchical corners);
  if that build stalls and one falls back to citing a lower bound, that would be a NEW (weaker-than-equality)
  cited dependency — but the native build is the intended route and my LP exhibits the resolution.
- **Next construction/consult.** For the formaliser: discharge `(3a)` as the `ℕ` lemma `minAdm((u,)+deep) ≥
  minAdm(M) − ab` (the `t=u` term — trivial in Lean) composed with the per-stratum finiteness whose codim is the
  RRR floor. A from-scratch multi-layer charge LP (2 deep layers, composite `CR` measure) would retire residual
  (a); it is bounded, not a wall.

**Files (absolute):**
- `…/.claude/worktrees/agent-a9fa628dc1a919710/expeditions/2026-06-20-aoyagi-full/threads/genm-deephier/deephier-cert.md` (this cert)
- `…/genm-deephier/scripts/{deephier_lp,confirm_floor,verify_minadm_identity,arity4_min_compare,gate_reduction,multilayer_check,crosslayer_ray,validate_rlct,mlayer_numeric}.py`
- `…/genm-deephier/codex/deephier-{prompt,answer}.md` (decorrelated consult)

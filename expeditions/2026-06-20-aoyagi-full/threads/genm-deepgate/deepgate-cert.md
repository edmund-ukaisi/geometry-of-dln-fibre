# deepgate — the deep-stratum codim WITH the peeled corank det charge: **BOUNDED** (the charge never binds)

**Seat:** pen-and-paper (adjudication, obstruction-primary, decorrelated), aoyagi-full Stage 2,
`genm-deepgate`. **Date:** 2026-07-15. **NO Lean edits, NO build.** Exact composite-rank-locus codim
(recursion, validated three ways), exact charge-exponent linear algebra, monomial-RLCT assembly; MC only as a
guide. Decorrelated `local-codex-consult` (gpt-5.x, xhigh, my conclusion WITHHELD; prompt "argue whichever
way"): `codex/deepgate-{prompt,answer}.md`, `codex/deepgate-run.log`.

**Consumed / verified (signatures, not paraphrased):** `genm-stepdesign/design.md` §0/§4.1/§4.2/§4.3 (the
front-charge object, the loss-only local model, the "binds at 2T1_q" claim, the comparator route);
`genm-stepbuild/codex/ibuniform-{prompt,answer}.md` + `codex/scale_check.py` (the `r^{−ab}` ratio finding);
`genm-rankgen/rankgen-cert.md` (`a+b ≤ deepTailMin−1` at binding strict shells; `Z_deep` = product of deep
layers `(M₂,…,M_last)`, generic rank `ρ = deepTailMin`; route (c) effective dimension);
`genm-incidencepp/incidence-cert.md` §3 (`C_{ℓ,s} = (M₀−s)(M₁−s)+sM₂−ab`, `min = minAdm_feas−ab`, the JOINT
integrated resolution, the §3 index-incompleteness caveat); `genm-thresholdhunt/threshold-verdict-cert.md`
§2 (`codim{BW=0} = minAdm`, the rank stratification); `genm-couplingfin/coupling-verdict-cert.md` (`A_cor→0`
transverse; `hpiv` marginal cuts).

Scripts (this thread, `scripts/`): `deepgate_arity4.py`, `composite_rank_codim.py` (κ_k recursion +3-way
validation), `deepgate_scan.py`, `deepgate_charge_analysis.py`, `verify_charge_exponent.py`,
`verify_charge_Acor_integral.py`, `verify_assembly_onset.py`, `verify_structural_and_onset.py`,
`deepgate_scan_corrected.py`.

---

## ★ VERDICT — **BOUNDED. The det charge never determines finiteness.**

At every deep rank-drop stratum `{rank Z_deep = ρ−k}` (`k = 1,…,ρ`), the exact local codimension of the
front-charge integrand **including** the peeled corank charge `det(Q_b Q_bᵀ)^{−a/2}` is

    C_k  =  min( u·ρ ,  u·(ρ−k) + κ_k − γ_{ρ−k} )   ≥   minAdm(M) − a·b   =   2·T1_q,

for **every** binding strict-shell cut, with **zero violations** over all 4-, 5-, 6- and 7-width chains
swept (widths 1..9 / 1..7 / 1..5). Here

- `κ_k = CR((M₂,…,M_last), ρ−k)` is the exact **parameter-space** codim of `{rank Z_deep ≤ ρ−k}` (the
  deep-degeneration measure codim), given by the composite-rank recursion `CR` below (three-way validated;
  `CR(·,0) = minAdm(·)`). **It is NOT the determinantal-variety codim** `(M₂−s)(n−s)` — that over-counts for
  multi-layer / non-square deep tails.
- `γ_s = max_{max(0,b−s) ≤ h ≤ b} h·(a+b−s−h)` is the exact **corank Gram det charge exponent** at rank `s`
  (stratifying the `A_cor`-integral by `rank(A_cor|surviving) = b−h`); the naive pointwise value is only the
  `h = (b−s)₊` term `a·(k−d)₊`, `d = ρ−b`.

**The charge is a red herring for finiteness.** The binding (worst) stratum is ALWAYS a shallow drop (small
`k`, where the charge is inert) or the generic-front cap `u·ρ`, both at `2·T1_q`. The charge-carrying deep
strata (`γ_s > 0`) sit with slack `≥ 0` and are never the binding one: the deep-degeneration codim `κ_k`
(growing `~ k²`) dominates the charge (growing `~` linearly in `k`). The `r^{−ab}` ratio-blowup that
stepbuild's Codex found kills the **bare-comparator domination route**, not the integral — confirmed both by
Codex ibuniform's own note ("the scalar quotient `I/J` is finite once both are finite") and here exactly.

**This CONFIRMS stepdesign's BOUNDED verdict at the tight deep stratum, and identifies stepdesign §4.2 as
loss-only-but-sufficient** (see §5). **Decorrelated Codex INDEPENDENTLY derived the exact same corrected
`γ_s` and proved `C_k ≥ minAdm−ab` cleanly** (§4).

---

## 1. The exact objects

At a binding cut `u = t★+j` (`1 ≤ j < r`), `a = M₀−u`, `b = M₁−u`, `ρ := deepTailMin M = min(M₂,…,M_last)`,
`n := M_last`, `d := ρ−b`. rankgen (binding strict shell): `a+b ≤ ρ−1`, so `d ≥ a+1 ≥ 2`, `b ≤ ρ−2`.
`Z_deep` = product of the deep layers of widths `(M₂,…,M_last)` (an `M₂×n` matrix), generic rank `ρ`.
Target: `frontChargeIntegral < ⊤` for `q < T1_q := (minAdm(M)−ab)/2`, i.e. finiteness for `2q < minAdm(M)−ab`.

**(A) Deep-degeneration measure codim `κ_k` (composite-rank-locus codim).** For deep widths `(v₀,…,v_p) =
(M₂,…,M_last)`,

    CR((v₀,…,v_p), s) = min_{0≤r≤min(v_{p-1},v_p)} [ (v_{p-1}−r)(v_p−r) + CR((v₀,…,v_{p-2}, r), s) ],
    base CR((v₀,v₁), s) = (v₀−s)(v₁−s)₊ ,   and inner CR = 0 when the reduced width r ≤ s.

`κ_k := CR((M₂,…,M_last), ρ−k)` = the parameter-space codim of `{rank Z_deep ≤ ρ−k}`. Derivation: stratify by
`rank(last deep layer) = r`; restricting the head-composite to a generic `r`-dim input subspace replaces the
last width by `r`. **Validated three independent ways** (`composite_rank_codim.py`): (i) `CR(chain,0) =
minAdm(chain)` exactly (arity 4–6, incl. `(4,4,4,4)→11`, `(5,4,3,4,5)→10`); (ii) `CR` for two deep layers
matches the direct rank-stratification `min_r[(v₁−r)(v₂−r)+(v₀−s)₊(r−s)₊]`; (iii) `CR` matches an independent
optimization-landing + normal-projection ("L-rank") numeric codim on 3-layer chains at all tested `s`.

> **Why not the determinantal codim.** For a single deep matrix (4-width chains) `κ_k = (M₂−s)(n−s)` is exact.
> For products it is strictly smaller: e.g. deep `(4,2,4)`, `{Z=0}`: `CR=7` (single narrow-factor drop) vs
> determinantal `16`; deep `(2,2,2)`, `{Z=0}`: `CR=3` (aligned component) vs `4`. Using the determinantal
> codim would be a false-comfort over-estimate.

**(B) Corank Gram det charge exponent `γ_s`.** At a rank-`s` drop (`s = ρ−k`, the `k` lost singular values
`~ t`), `Q̂_b = A_cor·S̃ = [B_s | t·B_l]`, `B_s` is `b×s`, `B_l` is `b×k`. The `A_cor`-integral
`∫ det(Q̂_b Q̂_bᵀ)^{−a/2} dA_cor` is resolved by stratifying `rank(B_s) = b−h` (normal codim `h(s−b+h)`, charge
`t^{−ah}` there):

    γ_s = max_{ max(0,b−s) ≤ h ≤ b }  ( a·h − h(s−b+h) )  =  max_{ max(0,b−s) ≤ h ≤ b }  h·(a+b−s−h).

- Pointwise (generic `A_cor`) is only `h = (b−s)₊`, giving `a·(k−d)₊`. `γ_s` can be **strictly larger** in the
  window `s < a+b` (e.g. deep `(6,6)@(a=b=2)`, `k=4,s=2`: `γ_2 = 1 > 0 = a(k−d)₊`).
- Full collapse `s = 0`: forced `h = b`, `γ_0 = ab` (matches stepbuild's `r^{−ab}` scaling exactly).
- **Charge exponent verified exactly** (`verify_charge_exponent.py`, `verify_charge_Acor_integral.py`): log-log
  slopes of `det(Q_bQ_bᵀ)` and of `∫_{A_cor} det^{−a/2}` match `2·max(0,k−d)` and `γ_s` respectively to the
  integer (finite-`t` contamination explains the sub-integer readings at the window boundary).

**(C) Codim-with-charge (the monomial-RLCT assembly).** The local model at the `k`-drop (Codex-concurred
form): loss `≍ |y|² + t²|W_lost|²`, `y ∈ ℝ^{u(ρ−k)}`, `W_lost ∈ ℝ^{uk}`; charge `t^{−γ_{ρ−k}}`; deep measure
`t^{κ_k−1}dt`. Integrating `y`, then the `W_lost`-radial, then the `t`-radial gives two constraints
`2q < uρ` (front/`W`-collapse) and `2q < u(ρ−k)+κ_k−γ_{ρ−k}` (deep radial), i.e.

    C_k = min( u·ρ , u·(ρ−k) + κ_k − γ_{ρ−k} ).

Assembly validated (`verify_assembly_onset.py`): a synthetic charge-visible case (`G(k)=3 < uρ=4`, predicted
onset `q*=1.5`) is **finite below `1.5`** (τ→0 tail-growth `~1e−9`) and **divergent above** (`~7e2` at `1.7`,
`~1e7` at `2.0`) — the charge lowers the onset from the no-charge `2.0` to `1.5` exactly as `C_k/2`.

---

## 2. The exhaustive scan (EXACT, corrected γ) — zero violations

`deepgate_scan_corrected.py` (binding strict-shell cuts, `1≤j<r`, `a,b≥1`):

| widths | range | cuts | `C_k < minAdm−ab`? | min overall slack | min **charge-stratum** slack |
|---|---|---|---|---|---|
| 4 | 1..9 | 1485 | **0** | 0 (tight) | 0 |
| 5 | 1..7 | 1022 | **0** | 0 (tight) | 0 |
| 6 | 1..5 | 189 | **0** | 0 (tight) | 0 |

(The earlier pointwise-`γ` scan — `deepgate_arity4.py`, `deepgate_scan.py` — covered 4/5/6/7-width, 3999+ cuts,
also 0 violations; the corrected `γ` only raises the charge strata's exponent yet the verdict is unchanged.)

- **The binding stratum is NEVER charge-biting** (`deepgate_charge_analysis.py`: `worst_k > d` count = 0 across
  all arities). It is always a shallow drop (charge inert) or `uρ` — both at `minAdm−ab`.
- **Canonical `(4,4,4,4)@u=3`** (`a=b=1,ρ=4,d=3, minAdm=11, target=10, uρ=12`): binding at `k=1,2` (`C*=10`);
  full-collapse `k=4` has `κ_4=16, γ_0=1, G=15, C*=12` (Codex ibuniform's "`κ=16` at `Z=0`, both converge,
  ratio `r^{−1}`" — exactly reproduced, and `C*=12 > 10`: BOUNDED).

---

## 3. The full-collapse fact (clean structural reformulation)

At full collapse (`k=ρ`, `Z_deep → 0`): `γ_0 = ab`, `κ_ρ = CR(deep,0) = minAdm((M₂,…,M_last))`, and

    C_full  =  min( u·ρ ,  minAdm(M₂,…,M_last) − ab )   ≥   minAdm(M) − ab
    ⟺  minAdm(M₂,…,M_last) ≥ minAdm(M)   AND   u·ρ ≥ minAdm(M)−ab.

**Both hold with zero exceptions.** `minAdm(deep) ≥ minAdm(M)` (38993 chains, 0 fails — structurally forced:
`Z_deep = 0 ⟹ Z_full = 0`, so the full-product zero locus has codim ≥ the deep zero locus' contribution).
The `−ab` from the charge is EXACTLY cancelled by the `−ab` in `2T1_q`; the residual comparison is between two
`minAdm`'s, and the deep one is always the larger. This is the clean reason the maximal charge (`r^{−ab}`)
cannot win.

---

## 4. Decorrelated Codex (conclusion WITHHELD) — INDEPENDENT derivation + clean proof

`codex/deepgate-{prompt,answer}.md` (gpt-5.x, xhigh; prompt withheld my BOUNDED conclusion, gave the two
established sub-facts κ_k and pointwise charge, asked "compute the codim-with-charge and decide"). Codex,
decorrelated:

- **[FACT] CORRECTED the charge exponent to exactly `γ_s = max_h h(a+b−s−h)`** — the same `A_cor`-integral
  resolution I found numerically, giving the same generic-`A_cor` `= a(k−d)₊` special case. Fully independent
  derivation.
- **[FACT] Same codim-with-charge** `C_k = min(uρ, u(ρ−k)+κ_k−γ_{ρ−k})` and same full-collapse
  `min(uρ, minAdm(deep)−ab)`.
- **[PROOF] BOUNDED, via a clean chain** I verified numerically (all 0 failures):
  - `ab + us − γ_s = us + (a−h★)(b−h★) + h★s =: R_h★` (at the maximizing `h★`);
  - `minAdm(M₀,M₁,s) ≤ R_h★` (3-chain front QIP; case split `h≤a` / `h>a`) — **17579 checks, 0 fails**;
  - stratify by deep rank `s`: `minAdm(M) ≤ κ_k + minAdm(M₀,M₁,s)` — **verified, 0 fails**;
  - subtract `ab`: `minAdm(M)−ab ≤ κ_k + us − γ_s`, i.e. the deep branch `≥ target`. `s=ρ` gives the `uρ`
    branch. ∎
- **[FACT] ratio vs integral (Q3):** `r^{−ab}` proves only that bare-comparator domination fails; the actual
  radial integral `∫ r^{κ_ρ−1−ab−2q}dr` converges for `2q < κ_ρ − ab ≥ minAdm(M)−ab`. "The ratio blow-up
  does not imply divergence; it kills only the bare-comparator route."
- **[FACT] the wall's true location:** the first analytic wall is `a+b ≥ ρ+1` (charge non-integrable for
  generic full-rank `Z`); the strict-shell scope `a+b ≤ ρ−1` (rankgen) lies safely inside.
- **[CAVEAT, honest — Codex + I concur]:** the local model assumes the **rank-stratified normal charts**
  (comparable lost singular values). A fully rigorous proof "still needs the corresponding
  stratified-resolution or induction lemma" that these charts EXHAUST the hierarchical composite-product
  degenerations — the deep-strata analogue of incidencepp §3b's front atlas. This is the one remaining
  build-side obligation (see §6), not a gap in the codim arithmetic.

---

## 5. Reconciliation with stepdesign §4.2 — it was **loss-only, and correct for the stratum it examined**

stepdesign §4.1's local model `loss ≈ |y|² + t²‖W_lost‖²` carries **no** `det(Q_bQ_bᵀ)^{−a/2}` factor — it is
**loss-only**. §4.2 computed the codim of the **`k=1` (rank `ρ−1`) stratum only** and found it tight at `2T1_q`.

**Both are correct, and here is why the omission was harmless at `k=1`:** at `rank Z_deep = ρ−1` the charge is
**inert**. Since `b ≤ ρ−2`, `Q_b = A_cor·Z_deep` (with `A_cor` generic, `rank Z_deep = ρ−1 ≥ b`) keeps full row
rank `b`, so `det(Q_bQ_bᵀ)` is a bounded unit — `γ_{ρ−1} = max_{0≤h≤b} h(a+b−(ρ−1)−h) = 0` because
`a+b−(ρ−1) ≤ 0` (rankgen). So `C_1 = min(uρ, u(ρ−1)+κ_1) =` the loss-only codim `= 2T1_q`. **§4.2's answer for
the tight stratum stands.**

What §4.2 did NOT examine is the **deeper** charge-biting strata (`rank Z_deep < a+b`, i.e. `k > ρ−a−b`), which
are the genuinely-new content this thread resolves. There the charge does bite (`γ_s > 0`, up to `ab` at full
collapse), but the deep-degeneration codim `κ_k` dominates it, so `C_k ≥ 2T1_q` with room to spare. **So
"deep strata bind at `2T1_q`" is right, and the binding stratum is precisely the charge-inert `k=1` one.**

---

## 6. The route (only-if-BOUNDED item): **Route B** — direct deep-stratum codim gate

stepbuild proved **Route A with the BARE comparator FALSE** (`frontCharge/comparator ~ r^{−ab} → ∞`). Two
repair options:

- **Route A′ (decorate the comparator):** carry `det(Q_bQ_bᵀ)^{−a/2}` inside the comparator so `front/comp →
  O(1)`. Works, but **changes the outer-IH object** (the recursion must thread the corank charge) — invasive,
  and the decorated comparator's finiteness must be re-established.
- **Route B (direct deep-stratum RLCT gate) — RECOMMENDED.** Because the charge never binds, each deep stratum
  is finite **directly** by its own codim-with-charge, with NO comparator for the deep factor:

  > **Gate (the exact Lean-friendly statement).** For a binding cut `u=t★+j`, `1≤j<r`, at each deep rank-drop
  > `{rank Z_deep = ρ−k}`, the per-stratum radial charge integral `∫₀^δ r^{C_k−1−2q} dr < ⊤` for `2q <
  > minAdm(M)−ab`, because the Nat inequality
  >
  >     C_k = min( u·ρ , u·(ρ−k) + CR((M₂,…,M_last), ρ−k) − γ_{ρ−k} )  ≥  minAdm(M) − a·b
  >
  > holds, with `γ_s = max_{max(0,b−s)≤h≤b} h(a+b−s−h)`. The Nat inequality is DISCHARGED by the clean chain
  > (§4): `minAdm(M) ≤ κ_k + minAdm(M₀,M₁,ρ−k)` (deep-rank stratification of the QIP) and `minAdm(M₀,M₁,s) ≤
  > ab + us − γ_s` (3-chain front QIP, case split on `h≤a`), plus `minAdm(deep) ≥ minAdm(M)` at full collapse.

  **Cleaner (reuses banked front machinery, does not perturb the IH):** each `∫ r^{C_k−1−2q}dr` is the same
  shape as the banked corner/incidence gate `stratum_corner_lt_top` / `clsCodim_gate_genL`; the new content is
  (i) the deep-rank-drop charts (the `(M₂,…,M_last)` composite-rank stratification — the deep analogue of
  incidencepp §3b's front atlas), and (ii) the Nat gate lemma above. **This is the honest way to close Step 3's
  deep factor** — it replaces stepdesign §4.3's comparator/IH route (which the bare comparator cannot support).

**Load-bearing build obligation (the §4 caveat):** the per-stratum gate presumes the rank-stratified charts
exhaust the deep degeneration (comparable lost singular values). The formaliser needs the deep
stratified-resolution / induction lemma (finite atlas of composite-rank big-cells with monomial Jacobians),
exactly parallel to incidencepp §3b for the front. Not a wall (the strata are explicit determinantal
big-cells) but it is the substantive Lean labour of Route B.

---

## 7. Close

- **Firmest result.** The deep-stratum codimension **including** the corank det charge is `C_k = min(uρ,
  u(ρ−k)+κ_k−γ_{ρ−k}) ≥ minAdm(M)−ab = 2T1_q` for every `k`, at every binding strict-shell cut (0 violations,
  4–7 width; corrected `γ_s` Codex-independently-derived). **BOUNDED — no finiteness gap; no wall.** The det
  charge NEVER binds (dominated by the `~k²` deep-degeneration codim `κ_k`); the binding is the charge-inert
  shallow drop or the `uρ` front cap. stepbuild's `r^{−ab}` kills only the bare-comparator domination, not the
  integral. stepdesign's BOUNDED verdict HOLDS at the tight deep stratum.
- **The tight rank-`(ρ−1)` stratum specifically:** charge inert (`Q_b` full-rank-`b`), codim-with-charge =
  loss-only codim = `2T1_q` — stepdesign §4.2 (loss-only) was correct there; the charge-biting content is at
  deeper drops, all dominated.
- **Most likely to break it (build, not math).** A tide that (a) uses the determinantal codim `(M₂−s)(n−s)`
  instead of the composite-rank `CR` (over-estimate — masks nothing here but is wrong for products); (b) uses
  the pointwise charge `a(k−d)₊` instead of `γ_s` (under-estimate — happens to stay bounded but is not the true
  exponent); (c) tries to route the deep factor through the BARE comparator (false, `r^{−ab}`); (d) omits the
  deep stratified-resolution lemma (§6 caveat) and assumes the front atlas covers the deep drops.
- **Next construction/consult that would settle the open part.** The one remaining obligation is the **deep
  stratified-resolution lemma** (§4 caveat): a finite atlas of composite-rank big-cells for `{rank Z_deep ≤
  ρ−k}` with monomial Jacobians (deep analogue of incidencepp §3b). A pen-and-paper follow-on could construct
  those explicit charts (the `CR`-recursion's stratification by the last deep layer's rank IS the atlas index)
  and confirm hierarchical (non-comparable) singular-value degenerations do not lower `C_k` below the
  comparable-`t` model — the only place the codim arithmetic is currently model-dependent.

# seamrlct — the deep-atlas ANALYTIC gate (per-stratum `rlct = C_k/2`): **BENIGN — no wall**

**Seat:** pen-and-paper (adjudication, OBSTRUCTION-primary, decorrelated), aoyagi-full Stage 2,
`genm-seamrlct`. **Date:** 2026-07-15. **NO Lean edits, NO build.** Exact RLCT algebra (the paper's own
`rlct` calculus + local-zeta / Morse–Bott per component + PSD det-monotonicity for the charge); Monte-Carlo
/ importance-sampling only as a noise-limited guide — and it **is** noise-limited (see §7), so nothing
load-bearing rests on it. Decorrelated `local-codex-consult` (gpt-5.x, xhigh; my BENIGN conclusion WITHHELD,
prompt framed "argue whichever way / is the seam benign or higher-order?"):
`codex/seamrlct-{prompt,answer}.md`, `codex/seamrlct-run.log`.

**Consumed / verified (signatures, not paraphrased):**
`genm-deepatlas-design/design.md` §2.2 (the product-layer reduction `L·M = (HΔ, HU+FE)`, unit-Jacobian CoV),
§4.1 (the `C_k` gate), §4.2 (the `(2,2,2)` benign check + the `x²+y⁴` caution), §4.3 (the coupled charge
`R=DDᵀ`), §4.4 (the one-peel local-zeta obligation — the target); `genm-deepgate/deepgate-cert.md`
§1(A) (the CR recursion `κ_k`), §1(C) (`C_k = min(uρ, u(ρ−k)+κ_k−γ_{ρ−k})`, the comparable-`t` local model),
§5 (the binding stratum `k=1` is charge-INERT: `γ_{ρ−1}=0`, `Q_b` full row rank `b`), §6/§7 (Route B, the
stratified-resolution obligation);
**the paper `paper-sources/…/source/main.tex` §RLCT** — Prop `rlct_elem` (lines 1819–1850) and
Thm `aoyagi-rlct` (lines 1887–1937), which supply the entire proof calculus below.

---

## ★ VERDICT — **BENIGN. No stratum + seam goes higher-order below the target; the wall cannot exist.**

The kill-condition (some binding stratum + seam with `rlct < C_k/2` dropping below `(minAdm−ab)/2`, making
the layer-box integral diverge for `c′∈[rlct, minAdm/2)`) is **provably impossible**, and the per-stratum
`rlct = C_k/2` route is sound at the binding stratum. Three independent supports, kept apart by level:

1. **`(□)` is TRUE unconditionally-modulo-the-cited-equality — the wall cannot exist.** The box integrand
   `K = ‖mult(A)‖²` is **homogeneous** (scale all layers by `s` ⟹ `K ↦ s^{2p}K`). For a homogeneous `F`,
   `rlct_0(F) = rlct(F)` (lower-semicontinuity + ray-constancy — §1), so `rlct(K) = rlct_0(K) =
   minAdm(M)/2` by the **cited** global Aoyagi equality (Thm `aoyagi-rlct`). Since `rlct(K) = inf_x rlct_x(K)`
   (Prop `rlct_elem`(iii)), **every** local `rlct_x(K) ≥ minAdm/2`, so `∫_{box} K^{−c′} < ⊤` for every
   `c′ < minAdm/2`. A binding-stratum `rlct < (minAdm−ab)/2` would force some `rlct_x < minAdm/2`,
   contradicting the cited equality. **The kill is impossible without disproving Aoyagi.** (This is the
   benign PRIOR the controller named, here turned into a proof-of-no-wall.)

2. **The SINGLE-PEEL seam is benign, PROVEN natively** (only the 2-layer Aoyagi base is cited): the
   product-seam loss `‖H‖² + ‖FE‖²` has `rlct = dim(H)/2 + codim{FE=0}/2 = C_k/2` by the paper's **own**
   `rlct(F+G)=rlct(F)+rlct(G)` (disjoint vars) + `rlct(FG)=min` + `rlct(Σsquares)=e/2`. Reproduces the
   design's `(2,2,2) → 3/2` **exactly** (§2). The `x²+y⁴` caution is **refuted for this seam**: `FE` is
   degree-2-in-each-factor (biquadratic), so per component it is Morse–Bott and its rlct is `codim/2`, never
   the `¼` of a pure quartic (§2, §3).

3. **The BINDING stratum is exactly the single-peel + charge-inert case** — the cleanest one. deepgate §5:
   binding at `k=1` (`{rank Z_deep = ρ−1}`), where the charge is **inert** (`γ_{ρ−1}=0`, `Q_b` full row rank)
   and `κ_1 = 1` (one transverse Schur block `E`). So the binding transverse loss is `‖y‖² + ‖(gen)·E‖²` on a
   generic (full-rank) big cell — Morse–Bott, `rlct = C_1/2 = (minAdm−ab)/2` (§4, §6). The seam / cross-peel /
   non-comparable complications live only at **deeper** strata (`k>1`), which carry codim **slack**
   (`κ_k ~ k²` dominates), so a deficit there cannot reach the target.

**The coupled charge `R = DDᵀ` (subquestion (c)) is a bounded factor** — `λ^b det(NNᵀ) ≤ det(N DDᵀ Nᵀ) ≤
Λ^b det(NNᵀ)` by PSD det-monotonicity (§5), exponent unchanged (274 966 nondegenerate trials, 0 violations;
and it is a theorem). **Non-comparable sectors (subquestion (b))** give the *true* rlct (comparable
over-estimates) but land **at** `codim/2`, not below, for biquadratic seams (§3, Codex Q3-corrected).

**The one un-discharged item is NOT a wall:** the fully general multi-peel `rlct_x = C_k/2` at *deep
intersection points* (non-generic, non-homogeneous) is exactly the paper's **own OPEN local conjecture**
(main.tex line 1937: "we expect … `rlct_{A_*} = codim_{A_*}/2` … future work"). It is **not needed for `(□)`**
(support 1) and is benign at the binding stratum (support 3); its clean sufficient condition is in §4.

---

## 1. The proof calculus (the paper's own `rlct` theorems) + the homogeneity lemma

All of Prop `rlct_elem` / Example `ex:rclts` (main.tex 1819–1870), used verbatim. For real analytic `F ≥ 0`:

- **[T-cap]** `rlct_x(F) ∈ (0, codim_x F⁻¹(0)/2]`. *The wall direction is `rlct < codim/2`.*
- **[T-sum]** `F(x), G(y) ≥ 0` in **disjoint** variables ⟹ `rlct(F+G) = rlct(F) + rlct(G)`.
- **[T-prod]** disjoint variables ⟹ `rlct(FG) = min(rlct F, rlct G)`.
- **[T-sos]** `rlct(x₁²+…+x_e²) = e/2 = codim/2` (saturates [T-cap]).
- **[T-inf]** `rlct(F) = inf_x rlct_x(F)`, attained for `X,F` algebraic; and `x ↦ rlct_x(F)` is
  lower-semicontinuous.
- **[T-inv]** rlct is invariant under (i) analytic coordinate change with non-vanishing Jacobian, and (ii)
  bounded-factor equivalence `c₁ f ≤ g ≤ c₂ f` (`c₁,c₂ > 0`) — since `|f|^{−s}` and `|g|^{−s}` share
  integrability. *(Standard; used throughout.)*
- **[T-aoyagi] (CITED)** `rlct(K^{DLN}_B) = codim mult⁻¹(B)/2` (global). For `B=0`, `= minAdm/2`. The 2-layer
  case `rlct(‖FE‖²) = minAdm(m,q,n)/2` is the base used below.

**[FACT] (homogeneity lemma).** If `F` is homogeneous (`F(sx)=s^N F(x)`, `N>0`), then `rlct_0(F) = rlct(F)`.
*Proof.* For `x≠0` in `F⁻¹(0)`, `rlct_{sx}(F)=rlct_x(F)` (rescaling is a Jacobian-nonzero coordinate change,
[T-inv]); by lower-semicontinuity [T-inf], `rlct_0(F) ≤ liminf_{s→0} rlct_{sx}(F) = rlct_x(F)`. Hence
`rlct_0 ≤ rlct_x` for all `x`, so `rlct_0 = inf_x rlct_x = rlct(F)`. ∎ **The DLN loss `‖mult(A)‖²` is
homogeneous of degree `2p` (`p =` #layers)** ⟹ its worst point is the origin, and support 1 follows.

---

## 2. Single-peel: `rlct(‖H‖² + ‖FE‖²) = C_k/2` (exact — subquestion (a))

**Object (design §2.2).** After the block-Schur reduction on the last layer `M` (pivot `Δ` invertible,
generic) and the unit-Jacobian column CoV on the free layer `L`, the deep product with **trivial head** is
`L·M = (HΔ, HU + FE)`, `H ∈ ℝ^{m×r}` free, `F ∈ ℝ^{m×(n−r)}` (spectator) free, `E ∈ ℝ^{(n−r)×(d−r)}` the
transverse Schur block; `Δ,U` generic on the big cell.

**[FACT] Bounded equivalence to the clean seam.** `loss = ‖ΔH‖² + ‖UH + FE‖² ≍ ‖H‖² + ‖FE‖²` on the
compact big cell (`σ_min(Δ) > 0`). *Upper:* triangle ineq. *Lower:* `‖ΔH‖² ≥ σ_min(Δ)²‖H‖²` gives `‖H‖²`;
and `‖FE‖ ≤ ‖UH+FE‖ + ‖U‖‖H‖` gives `‖FE‖² ≤ 2‖UH+FE‖² + 2‖U‖²‖H‖² ≤ C·loss`. So `c₁(‖H‖²+‖FE‖²) ≤ loss ≤
c₂(‖H‖²+‖FE‖²)`; [T-inv] ⟹ same rlct. *(This is the map `(H,W)↦(ΔH, UH+W)` being a bounded linear iso, with
`W = FE`.)*

**[FACT] rlct.** `H` is disjoint from `(F,E)`, so [T-sum]+[T-sos]+[T-aoyagi base]:
```
rlct(‖H‖² + ‖FE‖²) = dim(H)/2 + rlct(‖FE‖²) = dim(H)/2 + codim{FE=0}/2 = C_path/2,
```
and the min over rank-paths of `C_path` is `CR = κ_k` (design §2.3). **This is `C_k/2` (charge-inert stratum).**

**[FACT] `(2,2,2)` reproduced exactly.** `H∈ℝ²` (rlct 1), `‖FE‖²=‖F‖²E²` with `F∈ℝ²,E∈ℝ`:
`rlct(‖F‖²E²) = min(rlct‖F‖²=1, rlct E²=½) = ½` [T-prod]. Total `1 + ½ = 3/2 = CR((2,2,2),0)/2`. ✓ (matches
design §4.2 by hand + numeric).

**[FACT] the `x²+y⁴` caution does NOT apply.** `x²+y⁴` has `rlct = ¾ < 1 = codim/2` because `y⁴` is a **pure
quartic in one variable** (`rlct(y⁴)=¼`). The seam factor `FE` is **degree 2 in `F` and degree 2 in `E`**
(biquadratic); by [T-prod] its per-component rlct is `min` of the two smooth transverse contributions, i.e.
`codim/2`, never `¼`. A bilinear product cannot manufacture a pure high-power direction. Codex Q1 gives the
same conclusion via Schur-elimination (Morse–Bott at every point of a 2-factor zero fiber; local rlct = local
codim/2, "never a deficit below codim/2").

**Codex-independent (Q1, decorrelated).** `rlct(‖H‖²+‖FE‖²) = (mr + C(m,q,e))/2` with `C(m,q,e) =
min_s[(m−s)(q−s)+se]` — exactly the CR/2 above, derived independently.

---

## 3. Non-comparable sectors do NOT drop below `codim/2` (subquestion (b))

**[FACT, corrected by Codex Q3].** The comparable scaling (all `E_j ~ t^{α}` equal) is **not** always the
minimizer; the true rlct is found at a non-comparable sector — but for a biquadratic seam it lands **exactly**
at `codim/2`. Prototype: `K = h² + f²e²`. Comparable weights `(1,1,1)` give the candidate `3/2`; the weights
`(w_h,w_f,w_e) = (1,½,½)` give `(1+½+½)/(2·min(1,1)) = 1`, and [T-sum]+[T-prod] give the **exact** `rlct = 1 =
codim/2` (components `{h=0,e=0}`, `{h=0,f=0}`, each codim 2). So the non-comparable sector *finds* the
correct `codim/2`; comparable *over*-estimates. A sector falls **below** `codim/2` only under genuine
higher-order tangency (a pure `y⁴`), which the biquadratic seam never produces (§2). **Pivot-collapse seams**
are the chart boundaries `{det M_{I,J}→0}`, covered by lower-rank charts as **null overlaps** (design
§3.2/3.3) — inside each chart's compact interior the pivots are bounded away from singular.

---

## 4. Cross-peel coupling — the open item, NOT a wall (multi-peel)

**Object.** With a nontrivial head `P` (product of the earlier, also-degenerating layers), the loss is
`‖P·[H | FE]‖² = ‖PH‖² + ‖P·FE‖²`. `P` is **shared** between the two terms, so [T-sum] does not apply
directly (they are not in disjoint variables).

**[FACT] the shared head does not create a codim deficit — you minimize over components, not add peels**
(Codex Q2). Scalar prototype `K = p²(h² + f²e²)`: naively "additive" `rlct(h²+f²e²)=1`, but
`rlct(p²·(…)) = min(rlct(p²)=½, 1) = ½` [T-prod] — and this **is** `codim/2` (`K⁻¹(0)` has the component
`{p=0}` of codim 1). Verified numerically `rlct = 0.503` (`confirm.py`(B)). So the correct rule is
`rlct = min_{rank-path} (component codim)/2`; the coupling adds the head's own degeneration as its **own**
component, it does not lower any component's exponent.

**[FACT] where the clean decoupling holds** (Codex Q2): `‖PX‖ ≍ ‖X‖` needs `P` full **column** rank
(`PᵀP≻0`). For `(2,2,2,2)` the head is a generic invertible `2×2` ⟹ [T-inv] reduces to §2 (benign). For
`(2,3,3,3)` the natural head `P∈ℝ^{2×3}` has only full **row** rank (1-dim kernel) ⟹ decoupling fails; this
is the genuinely-coupled probe.

**[FACT] the deepest point of every chart is benign** (homogeneity, §1): each rank-stratum sub-model is
conic, so `rlct_0 = global = codim/2` by [T-aoyagi]. Origin values (Codex Q2, `codim{ABC=0}=min_s(D_s+se)`):
`(2,2,2,2) → codim 3, rlct₀ 3/2`; `(2,3,3,3) → codim 5, rlct₀ 5/2`. Generic component points are Morse–Bott
(also `codim/2`).

**[INFERENCE, Codex-concurred] the residual = the paper's own open conjecture.** Proving `rlct_x = C_k/2` at
*every* deep intersection (non-generic, non-homogeneous, several rank strata meeting with the head kernel
aligned to both `H` and `FE` while a spectator `F` loses rank — Codex Q5's "most likely deficit locus")
"would essentially prove the stated open local conjecture" (Codex). **Clean sufficient condition** (Codex Q5):
if `rank D_xμ = codim_x μ⁻¹(0) = C` (`μ = mult`), then `C` independent components of `μ` are analytic
coordinates and `‖μ‖² ≍ z₁²+…+z_C²`, so [T-inv]+[T-sos] give `rlct_x = C/2`. This holds on the atlas's
Morse–Bott big cells; the deep intersections are the null overlaps between charts. **This item does not gate
`(□)`** — support 1 closes `(□)` regardless — and does not touch the **binding** stratum (§6).

---

## 5. The coupled corank charge `R = DDᵀ` is a bounded factor (subquestion (c))

On the big cell `D = [Δ | U]` has full row rank `ρ_eff`, `G := DDᵀ ≻ 0`; on a compact subchart
`λI ⪯ G ⪯ ΛI` (`λ>0`). With `Q_b = A_cor·Z_deep`, on `{E=0}` `Z_deep = Z_red·D`, `N := A_cor Z_red` (`b`
rows), so `Q_b Q_bᵀ = N G Nᵀ`.

**[FACT] PSD det-monotonicity squeeze.** `G ⪰ λI ⟹ NGNᵀ ⪰ λ NNᵀ ⪰ 0 ⟹ det(NGNᵀ) ≥ λ^b det(NNᵀ)` (det is
monotone on the PSD order); symmetrically `≤ Λ^b det(NNᵀ)`. Hence
```
Λ^{−ab/2} det(NNᵀ)^{−a/2}  ≤  det(Q_b Q_bᵀ)^{−a/2}  ≤  λ^{−ab/2} det(NNᵀ)^{−a/2},
```
a bounded-factor equivalence ⟹ **same leading corank exponent, rlct unchanged** [T-inv]. Verified 274 966
nondegenerate random big-cell trials, **0 violations** (`confirm2.py`(A′)). Codex Q4 independently: [BENIGN],
"same leading corank exponent … fails only when `σ_min(D)` is no longer uniformly positive" — i.e. the chart
boundary, a null overlap. **At the binding stratum `k=1` the charge is inert anyway** (`γ_{ρ−1}=0`, deepgate
§5), so no charge subtlety enters where finiteness binds.

---

## 6. Why the BINDING stratum is clean — the native Route B is sound

deepgate §5: the binding (worst-`C_k`) stratum is `k=1` (`{rank Z_deep = ρ−1}`) or the `uρ` front cap, where
`κ_1 = 1` (a single transverse Schur block `E`) and the charge is **inert** (`γ_{ρ−1}=0`). So the binding
local model is `‖y‖² + ‖(generic)·E‖²` on a full-rank big cell — a single quadratic-nondegenerate transverse
block plus the front `y`-block, **Morse–Bott**. By §2 (single-peel, trivial coupling at `κ_1=1`) and §5
(charge inert):
```
rlct(binding stratum, with charge) = C_1/2 = (minAdm(M) − ab)/2,   the target.   [FACT]
```
The seam / cross-peel / non-comparable subtleties (§3, §4) live only at **deeper** strata `k>1`, which carry
codim **slack** (`C_k − (minAdm−ab) > 0`, deepgate scan, `κ_k ~ k²` dominates the linear charge). A deficit
there would have to consume the entire slack to reach the target — and cannot even do that, since
`rlct ≥ minAdm/2 > (minAdm−ab)/2` by support 1. **So Route B's per-stratum gate `∫₀^δ r^{C_k−1−2q}dr < ⊤`
for `2q < minAdm−ab` holds:** the binding stratum realizes `C_1/2` (proven), the rest have slack and the
global floor `minAdm/2`. deepgate's Nat gate `C_k ≥ minAdm−ab` supplies the arithmetic; §2/§5 supply the
`rlct = C_k/2` realization at the stratum that binds.

---

## 7. Method note — the numerics are noise-limited (nothing load-bearing rests on them)

The importance-sampled tube-volume estimator (`rlct_is.py`) is **exact on sum-of-squares** (validated `e/2`
for `e=1..6`, `confirm.log`/`is_validate.log`) — the backbone [T-sum]/[T-sos] reduces every benign case to.
But on **matrix products** and high-codim degenerations it is **biased and eventually collapses** (the IS
weights blow up: `dd_resolve.py` shows consecutive-slope estimates `1.0, 2.3, 5.6, 1.7, 3.0, 0.03, 5.3, 6.0`
at shrinking `t` — pure noise). So: the low readings on `(2,2,2,2)`, `(3,2,3)`, the `(D'')` proxy, etc. are
**MC artifacts, not walls** (the brief's warning: "a float rank at a tolerance is not the exact rank"). The
verdict rests on the **exact** algebra of §1–§6 + the cited equality, with MC only confirming the
sum-of-squares backbone and the low-codim cases. Where MC is reliable it agrees (`(2,2,2)→3/2`; charge
squeeze 0 violations; scalar cross-peel `→0.5`).

---

## 8. Levels kept apart (required check)

- **Quiver/geometry level** — the rank-stratum codims `κ_k = CR(deep, ρ−k)` and the component structure
  (design §2–3, deepgate §1A). Untouched here; consumed.
- **Codim-with-charge (`C_k, θ`) level** — the `ℕ` gate `C_k = min(uρ, u(ρ−k)+κ_k−γ_{ρ−k}) ≥ minAdm−ab`
  (deepgate, proven). This cert does **not** re-prove it; it establishes the **analytic realization** that the
  per-stratum radial integral actually has exponent `C_k` (i.e. `rlct = C_k/2`) at the binding stratum.
- **RLCT cap level** — `rlct = ½·codim` is the **cited** Aoyagi equality globally (Thm `aoyagi-rlct`); its
  **local** per-point form is the paper's open conjecture (line 1937). `(□)` needs only the **global** value
  `minAdm/2` (support 1), which is cited. This cert does **not** upgrade the cited equality to a native local
  theorem — it shows the seam does not obstruct the native lower-bound route at the binding stratum, and
  isolates the residual as the paper's own open conjecture.

---

## Close

- **Firmest result (obstruction).** The wall the kill-condition describes **cannot exist**: it would force a
  local `rlct_x(‖mult‖²) < minAdm/2`, contradicting the cited global equality `rlct = minAdm/2 = inf_x rlct_x`
  (via homogeneity, §1). Independently, the **binding** stratum (`k=1`, charge-inert, `κ_1=1`) is Morse–Bott
  and realizes `rlct = C_1/2 = (minAdm−ab)/2` **natively** (§2, §5, §6). The single-peel `FE` seam is benign
  and PROVEN via the paper's own `rlct` calculus (`rlct = CR/2`, reproducing `(2,2,2)=3/2`); the `x²+y⁴`
  worry is refuted (biquadratic ≠ pure quartic); the coupled `DDᵀ` charge is a bounded factor (PSD
  det-monotonicity, 0/274 966 violations); non-comparable sectors land **at** `codim/2`, not below.
- **Most likely to break it (and why it doesn't).** A genuine higher-order seam would have to sit at a **deep
  intersection** (head kernel aligned with both `H` and `FE`, spectator `F` losing rank — Codex Q5). This is
  (i) **not** the binding stratum (which is shallow + charge-inert, §6), (ii) has codim **slack** if `k>1`,
  and (iii) is floored by `rlct ≥ minAdm/2` (support 1). No such deficit is constructible in scope (Codex Q5:
  "I cannot construct the requested DLN counterexample; producing one would disprove the … local conjecture").
- **Next construction/consult that would settle the open part.** The only genuinely-open item is the paper's
  **local** conjecture `rlct_{A_*} = codim_{A_*}/2` at deep-intersection points (main.tex line 1937), whose
  clean sufficient condition is `rank D_xμ = C` (submersive/clean charts ⟹ `‖μ‖² ≍ Σz_i²`, §4). A pen-and-
  paper follow-on could prove the two-peel `(2,3,3,3)` non-injective-head case at an explicit intermediate
  point by a symbolic (Gröbner / Newton-polyhedron) resolution of `‖P[H|FE]‖²` — the smallest case where the
  decoupling `PᵀP≻0` fails. **This does not gate `(□)` or the deep-atlas tide D binding stratum** — both are
  closed by §1 and §6 respectively. **Recommendation:** deep-atlas **tide D may build the per-stratum gate**
  `rlct = C_k/2` for the binding stratum on the Morse–Bott big cells (§6), citing the global Aoyagi equality
  for the `(□)` floor and the sufficient condition (§4) for the big-cell realization; do **not** attempt a
  native proof of the deep-intersection local conjecture inside this expedition.

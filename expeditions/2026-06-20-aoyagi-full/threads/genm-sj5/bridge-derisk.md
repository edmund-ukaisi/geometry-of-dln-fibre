# BRIDGE de-risk — the full reduction freed-Γ → corank-Gram (GAP-A) → detGram (GAP-B)

**Seat:** pen-and-paper (obstruction, then corrected). **Date:** 2026-07-11. **NO Lean.** **Charge
(team-lead):** certify the FULL analytic reduction the fill (genm-sj5-schur) builds: **GAP-A** (box-bounded
inner-Γ integration → corank-Gram weight, incl. the PosDef-fail bottleneck) + **GAP-B**
(`corankGram_shrink_lt_top`: corank-Gram box → banked single-matrix `detGram`, via the shrinking-image CoV).
Two-regime split (`b≤min tail` vs `b>min tail`); does `b>min tail` arise at the binding cut; the pivot role.

**Exact algebra (mine):** `/tmp/prodD/{bridge,wzero,bridge2,bridge3}.py`, `/tmp/seam/*` (SVD reduction
identity; box-vs-full-space; pivot load-bearing; the binding-cut `b`-vs-`min(tail)` scan; the joint
per-chart abscissa). **Decorrelated:** `codex/bridge-{prompt,answer}.md` (xhigh, conclusion withheld). Its
finding — "the STANDALONE det-Gram/det⁺ WEIGHT reduction does not prove finiteness; a JOINT
rank-stratified bounded-box resolution is required" — is the same conclusion, pinning the discipline below.

> **CORRECTION (this version supersedes my first pass).** My first pass headlined "NO — do not peel Γ
> first," over-weighting the pointwise `{w=0}` divergence. That was a mis-emphasis: the `{w=0}` inner-Γ
> `+∞` is the **standard pivot charge** on a NULL set, integrable over the pivot variables — a *handled*
> coupled charge, not a wall. The route **closes** provided the pivot residual is **kept coupled** (the
> failure mode is *dropping* the pivot to a `w`-independent weight). This matches Codex exactly (its
> "weight reduction invalid, joint resolution required" = keep the pivot coupled).

---

## VERDICT (headline): YES — the reduction closes, with the pivot residual KEPT coupled. `b≤min tail` at every binding cut, so the full-rank det-Gram suffices — NO det⁺ variant needed.

1. **`b = M₁−t ≤ min(M₂,…,M_L)` at EVERY nontrivial binding cut** (`p = M₀−t ≥ 1`): **0 / 57332** binding
   charts violate it (widths 1..6, `L=2..6`; `bridge3.py`). So the corank rows `Q_b` (bottom `M₁−t` rows of
   the tail product) are **generically full rank `b`**, the bottleneck `{rank Q_b < b}` is **NULL**, and the
   literal det-Gram `∫det(Q_bQ_bᵀ)^{−a/2}` is well-posed. **GAP-B's `b ≤ m` (full-rank) hypothesis holds;
   the det⁺ variant is NOT needed** for the (□) peel. (The `b>min tail` charts — 3390 — ALL have
   `p = M₀−t = 0`: Γ empty `0×b`, GAP-A vacuous; degenerate, no corank-Gram.)

2. **The target is finite up to `½·minAdm`.** The freed-Γ triple = the per-chart integral `∫_{A'} g(Q)`,
   `g(Q) = ∫_{A₀-chart}frobSq(A₀Q)^{−c'}` — abscissa **exactly `7/2`** for `(3,3,3,4)` (`bridge2.py`: stable
   below, blows up above). The joint `(x,Γ)=A₀` integral closes at `½·minAdm`.

3. **The pivot `w` is load-bearing and must be KEPT coupled.** The inner-Γ integral is `+∞` pointwise on the
   NULL `{w=0}` locus, but that is the standard pivot charge, integrable over the pivot variables. Dropping
   `w` (reducing to a `w`-independent det-Gram/det⁺ WEIGHT, then integrating the deeper params) gives `+∞`;
   keeping the coupled residual closes it.

---

## 1. The exact inner-Γ CoV (GAP-A), both regimes — VERIFIED

`J(w,S,Q_b) = ∫_{Γ∈box}(w + ‖S + Γ Q_b‖²)^{−c'}dΓ`, `Γ:p×b`, `Q_b:b×n`, `S = C·Q̃ₚ`, `w = ‖P·Q̃ₚ‖²`. Via the
SVD `Q_b = UΣVᵀ` (verified `bridge.py` PART A, `J_direct = J_svd`):

**Full row rank `Q_b` (`rank = b`, the a.e. case at every binding cut):**
> `J = det(Q_bQ_bᵀ)^{−p/2} · R`, `R = ∫_Ω (w + ‖S_⊥‖² + ‖T‖²)^{−c'} dT`, `Ω = S_b + (box·U)Σ` the
> shifted-scaled IMAGE box.

This is the banked `corankBlock_morsePeel` atom (full-rank scope). **The residual `R` KEEPS the pivot `w`**
(the Morse regularizer); it is finite a.e. (`+∞` only on the null `{w=0, S_⊥=0}`). Do NOT extend `Ω` to
`ℝ^{pb}` (the over-count); keep the box.

**Rank-deficient `Q_b` (`rank = r < b`; NULL at binding cuts):**
> `J = det⁺(Q_bQ_bᵀ)^{−p/2} · ∫_{ℝ^{p×r}} m_B((T−S_r)D⁻¹)·(w+‖S_⊥‖²+‖T‖²)^{−c'}dT`,

`det⁺ = ∏_{i≤r}σ_i²`, `m_B(Z)` the bounded kernel-slice volume (nonconstant, e.g. tent `2(√2−|z|)`). `J`
over the box is finite (box caps the `p(b−r)`-dim kernel; `bridge.py` PART B: `J` grows as `B→∞`, so the
box is essential, full-space diverges). **Because this stratum is NULL at every binding cut (fact 1) it
contributes measure-zero; the det⁺ form is recorded for robustness but is not on the (□) path.**

---

## 2. THE CRUX — box-boundedness + null bottleneck: the reduction is a MEASURE statement

The pointwise hyps of `corankBlock_morsePeel` (`Q_bQ_bᵀ` PosDef, pivot `>0`, `c'>ab/2`) fail on two NULL
loci; supplied as a measure statement (integrate `x`, `A'`), both are harmless:

- `{rank Q_b < b}` NULL at binding cuts (fact 1) → the a.e. full-rank atom gives
  `J = det(Q_bQ_bᵀ)^{−p/2}·R` a.e.; box-boundedness makes `J` finite on the null stratum too (genuinely
  measure-zero, no hidden mass) → contributes `0`.
- `{w=0}` NULL (`Q̃ₚ=0`, positive-codim in `(x,A')`); `J=+∞` there pointwise, but `R(w)` is integrable over
  the pivot variables `x` (the pivot charge). Inner-Γ at `{w=0}` is `∫_{Γ box}‖ΓQ_b‖^{−2c'}dΓ`, finite iff
  `c'<p·b/2` (`=2` for `(3,3,3,4)`), `+∞` above (`wzero.py`, MC `1.6·10⁴→3.4·10⁷`); yet the JOINT
  `∫_x∫_Γ = g(Q)` is finite (`~30`) throughout `[2,7/2)` — the pivot variables supply the missing
  transverse dimensions.

**So the reduction is valid as a MEASURE (a.e.) statement, NOT pointwise.** The formaliser supplies
`corankBlock_morsePeel`'s hyps a.e. (both null loci), integrates the pivot residual over `x` (the pivot
charge), and the null loci contribute `0` / an integrable coupled singularity. = Codex's "joint
rank-stratified bounded-box resolution"; covdesign's §CONCESSION front-first `g(Q) ≍ σ_q^{−α}`
(`α=max{0,2c'−M₀(q−1)}`) is the clean packaging of the joint `(x,Γ)` integral.

---

## 3. The pivot is LOAD-BEARING — keep it coupled (the one discipline)

`(w+E)^{−c'} ≤ E^{−c'}` and `≤ w^{−c'}` are both valid pointwise majorants but **either can be
non-integrable** (`bridge.py` PART C: at `c'=1.2`, `J(w=0)/J(w>0)=119`; Codex's `p=1,b=2,Q=(1,0)ᵀ`: at
`c'=3/4`, drop `w` → `∫|γ₁|^{−3/2}=∞`, drop `E` → `∫|x|^{−3/2}=∞`). The correct majorant is the SECTOR
bound `min{w^{−c'},E^{−c'}}` (`= (w+E)^{−c'}` up to `2^{c'}`), kept over `(x,Γ)` jointly. In the chart `P`
invertible ⟹ `w=0 ⟺ Q̃ₚ=0 ⟹ S=0`, so on `{w=0}` the inner-Γ is the pure pivot charge `∫‖ΓQ_b‖^{−2c'}`,
rescued only by integrating the pivot jointly. **The failure mode is DROPPING the pivot** to a
`w`-independent weight (then `∫` of the weight is `+∞` on `{w=0}`).

---

## 4. THE DOWNSTREAM CoV (GAP-B) — `corankGram_shrink_lt_top`, the recipe

Reduce `∫∫_{Y∈matBox(b,m),A∈matBox(m,q)}det((YA)(YA)ᵀ)^{−a/2}` (`b≤m≤q` — holds at binding, fact 1) to the
banked single-matrix `detGram_lintegral_lt_top`, via the **shrinking-image CoV** (= my cover-seam
`cover-derisk.md` mechanism as a Lean-friendly estimate):

1. **`m`-column Cauchy–Binet lower bound** (banked #112): `det((YA)(YA)ᵀ) ≥ det((YA_S)(YA_S)ᵀ)`, `|S|=m` —
   integrand `≤ det((YA_S)(YA_S)ᵀ)^{−a/2}`, reducing to the **square-middle `(b,m,m)` base**, matched
   threshold `m−b+1 = a_c`. (A single `b×b` minor is lossy, threshold only `a<1`; the `m`-column block is
   sharp — cover-derisk + Codex.)
2. **Shrinking-image CoV (the exact estimate).** On `{A_S` invertible`}`, `Y↦Q_S = Y·A_S`,
   `dY = |det A_S|^{−b}dQ_S`, reduced core over the image parallelepiped `A_S·(Y-box)`. The `|det A_S|^{−b}`
   Jacobian is **exactly cancelled** by the image volume `vol(A_S·[-1,1]^{b×m}) = 2^{bm}|det A_S|^{b}`.
   **Do NOT extend the shrinking image to a fixed box** — that reintroduces `∫|det A_S|^{r−b}=∞` (`r<b`), the
   over-count trap (= the fill's Codex's "fixed-box → `∫|det|^{r−b}=∞`").
3. **Endpoint = banked `detGram_lintegral_lt_top`** on the square base (`m=q`, no twist), threshold `m−b+1`.
   Finiteness up to `½·minAdm` via the tube-codim linchpin (`prodD-general` #127, banked ℕ).

**The one genuinely-new quantitative lemma:** the parallelepiped-volume identity
`vol(A_S·[-1,1]^{b×m}) = 2^{bm}|det A_S|^{b}`, cancelling `|det A_S|^{−b}` exactly (retaining the shrinking
image). This is `corankGram_shrink_lt_top`'s content; the rest (#112, `detGram`, tube #127) is banked.

---

## 5. The full reduction, assembled (the recipe genm-sj5-schur builds)

```
freedSchurLoss triple  ∫_{A'} ∫_x ∫_Γ (‖P Q̃ₚ‖² + ‖C Q̃ₚ + Γ Q_b‖²)^{−c'}
  │  GAP-A: inner-Γ, a.e. (Q_b full rank b — bottleneck NULL at binding, fact 1)
  │         corankBlock_morsePeel  →  det(Q_bQ_bᵀ)^{−p/2} · R(w)   [KEEP the pivot residual R(w)]
  ▼
  ∫_{A'} det(Q_bQ_bᵀ)^{−p/2} · [∫_x R(w) = pivot charge]        [{w=0} handled: coupled, integrable]
  │  GAP-B: corankGram_shrink_lt_top
  │         det((YA)(YA)ᵀ)^{−a/2}  →(m-col Cauchy–Binet #112)→  square (b,m,m) base
  │         →(shrinking-image CoV, |det A_S|^{−b}×|det A_S|^b cancel)→  detGram_lintegral_lt_top (banked)
  ▼
  finite up to c' < ½·minAdm   [tube D = minAdm(reduced) + linchpin, prodD-general #127; charges add, front-peel]
```

**Do NOT:** (i) reduce the inner-Γ to a `w`-independent det-Gram weight (drops the pivot → `+∞` on `{w=0}`);
(ii) extend the shrinking image to a fixed box in GAP-B (`∫|det A_S|^{r−b}=∞`); (iii) build a det⁺ variant
(unneeded — `b≤min tail` at binding, fact 1).

---

## 6. Answers to the asks + Codex

- **ASK 1 — does `b>min(tail)` arise at the binding cut?** NO for nontrivial charts: `b ≤ min(M₂,…,M_L)` at
  every binding cut with `p=M₀−t ≥ 1` (**0/57332**); the `b>min tail` cases are exactly the `p=0`
  (empty-Γ, degenerate) charts. **GAP-B's `b≤m` full-rank det-Gram suffices; no det⁺ brick needed.**
- **ASK 2 — the det⁺ regime's CoV (recorded, not on the (□) path):** §1 rank-deficient form,
  `J = det⁺(Q_bQ_bᵀ)^{−p/2}·[m_B kernel density · pivot-regularized residual]`, box-finite. Its generic
  rank `min(tail)` IS the reduced-chain rank (so det⁺ = the reduced chain's Gram one arity down — the #127
  connection). Recorded should a future non-binding-cut variant need it.
- **Codex (decorrelated, withheld):** "the uniform reduction to the standalone det-Gram/det⁺ WEIGHT is
  invalid; finiteness below `minAdm/2` requires a joint rank-stratified bounded-box resolution; the pivot
  `w` is load-bearing." Same discipline as §2–3 (keep the pivot coupled; do not reduce to a standalone
  weight). Adopted; it pins WHY the pivot cannot be dropped and WHY the shrinking image must be retained.

---

## 7. Close

- **Firmest.** The freed-Γ → corank-Gram (GAP-A) → detGram (GAP-B) reduction **closes**
  `innerCorankDescent_lt_top` up to `½·minAdm`, as a MEASURE statement: (i) `b≤min tail` at every nontrivial
  binding cut (0/57332) ⟹ full-rank `Q_b`, bottleneck NULL, full-rank det-Gram suffices (no det⁺); (ii)
  GAP-A = `corankBlock_morsePeel` a.e., KEEPING the pivot Morse residual; (iii) `{w=0}` is a handled coupled
  pivot charge, NOT a wall; (iv) GAP-B = the shrinking-image CoV (m-col Cauchy–Binet → square base,
  `|det A_S|` cancellation), consuming banked `detGram_lintegral_lt_top` + `#112` + tube `#127`. Per-chart
  target finite (abscissa `7/2` for `(3,3,3,4)`).
- **The one discipline (load-bearing).** Keep the pivot residual **coupled** (do not drop `w`); keep the
  **shrinking image** in GAP-B (do not extend to a fixed box). Both failures give `+∞` bounds while the
  truth is finite — the recurring over-count trap.
- **Most likely to break / watch.** GAP-B's shrinking-image `|det A_S|` estimate (the parallelepiped-volume
  cancellation) is the one genuinely-new quantitative lemma — bounded, banked-adjacent (`#112` + the volume
  identity), not yet a Lean lemma. The pivot-charge coupling (§2–3) must be a joint bound (covdesign
  §CONCESSION `g≍σ_q^{−α}`); a factorized pivot charge hits the covdesign over-count wall.
- **Next.** Relay to genm-sj5-schur: build GAP-B (`corankGram_shrink_lt_top`) per §4; use the full-rank
  det-Gram (no det⁺); keep the pivot residual coupled in GAP-A. Consumes tube (#127) + `#112` + banked
  `detGram`; the shrinking-image `|det A_S|` cancellation is the new brick.

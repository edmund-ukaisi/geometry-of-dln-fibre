# BRIDGE de-risk — the freed-Γ triple → I(a): does the majorant route close `innerCorankDescent_lt_top`?

**Seat:** pen-and-paper (obstruction — adjudicate one truth-value: does integrating the freed Schur block
Γ first reduce the exact hole to `I(a) = ∫det(Q_bQ_bᵀ)^{−a/2}` and thereby close it?). **Date:** 2026-07-11.
**NO Lean.** **Charge (team-lead):** the fill's ONE hole is the FREED-Γ TRIPLE integral (PRE-Γ-integration),
not the POST-Γ det-Gram `I(a)`. Certify whether the majorant route reduces the exact
`innerCorankDescent_lt_top` down to `I(a)` — (1) inner Γ → det-Gram where PosDef; (2) CRUX: on the
bottleneck (rank Q_b < b) does box-boundedness keep it finite AND majorable uniformly (measure statement);
(3) is the Γ-free pivot droppable or load-bearing?

**Exact algebra (mine):** `/tmp/prodD/{bridge,wzero}.py` (exact SVD reduction identity; box-vs-full-space;
pivot load-bearing test; the `{w=0}` divergence threshold). **Decorrelated:** own `local-codex-consult`
(xhigh, my conclusion WITHHELD — I told it to hunt where the reduction breaks): `codex/bridge-{prompt,answer}.md`.
Codex reached the same verdict and sharpened three points, all adopted.

---

## VERDICT (headline): NO — the Γ-first → `I(a)` det-Gram reduction does NOT close the hole. It is a LOSSY bound that is +∞ on the pivot-degenerate locus. The fix: integrate the pivot JOINTLY with Γ (the front-first bound), not Γ first.

The freed-Γ triple's finiteness (c' < ½·minAdm) is TRUE (it is `gammaPeelIntegral`, Aoyagi), but the
route "integrate Γ first, get a det-Gram weight on the deeper params, then invoke `I(a)`" does **not
prove it** — and would give a **+∞** bound on a real locus. Three exact facts:

1. **The reduction to the FULL det-Gram `I(a)` is ill-posed on contracting chains.** Where the corank rows
   `Q_b` are generically rank-deficient (`b = M₁−t > min(internal tail widths)`), `det(Q_bQ_bᵀ) ≡ 0` a.e.,
   so `I(p) = ∫det(Q_bQ_bᵀ)^{−p/2} = +∞` a.e. The correct fixed-rank Jacobian is the **pseudo-determinant**
   `det⁺(Q_bQ_bᵀ)^{−p/2}` (product of the `r` nonzero squared singular values) — but it **cannot be
   separated from the residual**: the shrinking image box and `det⁺` cancel exactly
   (`∫ m_B((T−S_r)D⁻¹)dT = det⁺(QQᵀ)^{p/2}·|box|`), so a standalone `det⁺`-weighted integral is too crude
   and can diverge while the true `J` is bounded.

2. **THE BINDING FACT — the pivot-degenerate locus `{w=0}` breaks the sequential reduction, even for
   `(3,3,3,4)`.** In the pivot chart the pivot block `P` is invertible, so
   `w = ‖P·Q̃ₚ‖² = 0 ⟺ Q̃ₚ = 0 ⟹ S = C·Q̃ₚ = 0` — no shift remains. On this locus the inner Γ-integral is
   `∫_{Γ box}‖Γ Q_b‖^{−2c'}dΓ`, which (full-rank `Q_b`) is finite iff `c' < p·b/2`. For `(3,3,3,4)`, `t=1`:
   `p·b/2 = 2·2/2 = 2`, while `½·minAdm = 7/2`. **So for `c' ∈ [2, 7/2)` the inner Γ-integral is `+∞` on
   `{w=0}`** (MC: `1.6·10⁴ → 1.1·10⁶ → 3.4·10⁷` as `c' = 2.5, 3.0, 3.4`; exact threshold `p·b/2`). Any bound
   that integrates Γ first and then the deeper params inherits this `+∞`. The TRUE joint integral is finite
   because the **pivot variables `x` supply the missing transverse dimensions** — but only if `x` and `Γ`
   are integrated JOINTLY.

3. **The pivot energy `w` is LOAD-BEARING; it cannot be dropped.** `(w+E)^{−c'} ≤ E^{−c'}` (drop `w`) and
   `≤ w^{−c'}` (drop `E`) are both valid pointwise majorants but **either can be non-integrable**. The
   correct coupled majorant is the SECTOR bound `min{w^{−c'}, E^{−c'}}` (`= (w+E)^{−c'}` up to `2^{c'}`):
   `w > 0` rescues zeros of the corank energy on the active `p·r` transverse directions; `E` rescues the
   `{w=0}` locus; the bounded box rescues the `p(b−r)` kernel directions. All three must be kept.

---

## 1. The exact inner Γ-integral (both regimes) — SVD reduction, VERIFIED

`J(w,S,Q_b) = ∫_{Γ∈box}(w + ‖S + Γ Q_b‖²)^{−c'}dΓ`, `Γ:p×b`, `Q_b:b×n`, `S:p×n`, `w≥0`. Via the SVD
`Q_b = UΣVᵀ`, `Z = ΓU`, `T = S_b + ZΣ` (verified `bridge.py` PART A, `J_direct = J_svd` to MC error):

**Full row rank (`rank Q_b = b`, needs `b ≤ n`):**
> `J = det(Q_bQ_bᵀ)^{−p/2} · ∫_Ω (a + ‖T‖²)^{−c'} dT`, `a = w + ‖S_⊥‖²`, `Ω = S_b + (box·U)Σ`.

The residual `R` is over the **rotated-scaled-shifted IMAGE box `Ω`** (extent `∝ σ_j`), NOT `ℝ^{p×b}`.
Replacing `Ω` by `ℝ^{p×b}` is the whole-space Morse value `π^{pb/2}Γ(c'−pb/2)/Γ(c')·a^{pb/2−c'}` — the
**over-count trap** (needs `c'>pb/2`, destroys the box finiteness).

**Rank-deficient (`rank Q_b = r < b`):**
> `J = det⁺(Q_bQ_bᵀ)^{−p/2} · ∫_{ℝ^{p×r}} m_B((T−S_r)D⁻¹)·(w + ‖S_⊥‖² + ‖T‖²)^{−c'} dT`,

where `det⁺ = ∏_{i≤r}σ_i²`, and `m_B(Z)` is the **kernel-slice volume** — a bounded, compactly-supported
NONconstant density (e.g. a rotated `[−1,1]²` gives the tent `m(z)=2(√2−|z|)`), not a single constant.
Verified `bridge.py` PART A (`J_direct = J_svd`, ratio ≈1.01 rank-deficient) and PART B.

---

## 2. CRUX — the bottleneck: box-finite pointwise, but the weight-reduction is not uniformly majorable

**(a) `J` over the box IS pointwise finite when `rank Q_b = r < b`** — the box caps the `p(b−r)`-dim kernel.
Verified `bridge.py` PART B: `J` GROWS without bound as the box half-width `B → ∞`
(`B=1 → 8.7`, `3 → 261`, `10 → 8710`, `30 → 197813`), so the **full-space Γ-integral is `+∞`** and the box
is essential. (This is "box caps the collapsing direction; full space doesn't" — my cover-seam de-risk
mechanism, PRE-integration.) Also: if `w + ‖S_⊥‖² > 0`, trivially `J ≤ |box|·(w+‖S_⊥‖²)^{−c'} < ∞`; and in
all cases `c' < p·r/2 ⟹ J < ∞`.

**(b) The reduction to a STANDALONE det-Gram / det⁺ weight is NOT valid uniformly.** For the full det-Gram:
`det(Q_bQ_bᵀ) ≡ 0` on `{r<b}`, `+∞` inverse — and if narrow widths force `r<b` generically, `I(p)=+∞`
a.e. For det⁺: it is the correct fixed-rank Jacobian but **cancels against the shrinking image** and cannot
be pulled out as a standalone weight (the standalone det⁺-integral can diverge while `J` is bounded — the
`Q_b = Y A₂`, `Y:2×1`, `A₂:1×4` witness: `J = 4σ⁻²∫_{s+σ[−1,1]²}(w+ρ²+‖T‖²)^{−c'}dT → 16w^{−c'}` as
`σ→0`, the `σ⁻²` cancelled by the `O(σ²)` image area).

**(c) MEASURE statement — the sequential reduction does NOT prove finiteness.** For fixed `x`:
`w(x) > 0 ⟹ ∫_{A'}J ≤ |box|·w(x)^{−c'}·|A'-box| < ∞` uniformly through every rank bottleneck; but
`w(x) = 0 ⟹ ∫_{A'}J may be +∞` (fact 2). The full joint `(x,A')`-integral IS finite (pivot supplies the
transverse dimensions), **but this requires a JOINT rank-stratified bounded-box resolution — it is not
proved by the det-Gram or det⁺ weight** (Codex Q2(c), verbatim: "finiteness below minAdm/2 is not implied
from the displayed setup alone... it is not proved by either the determinant or pseudo-determinant weight").

---

## 3. The pivot is LOAD-BEARING — the correct coupled majorant

Verified `bridge.py` PART C (aligned deep stratum, `S = −Γ₀Q_b` so `E` can vanish): as `c'` crosses
`p·r/2`, `J(w=0)/J(w>0)` explodes — `c'=0.4: 1.27`, `c'=0.8: 2.9`, `c'=1.2: 119` (`w=0` blows up when
`2c' ≥ p·r`; the corank Morse dimension is exhausted and only `w > 0` supplies the shift). Codex's exact
`p=1,b=2,Q=(1,0)ᵀ,S=0,w=x²` model: `∫_{[−1,1]³}(x²+γ₁²)^{−c'} < ∞ ⟺ c'<1`; at `c'=3/4`, dropping `w`
gives `∫|γ₁|^{−3/2}=∞`, dropping `E` gives `∫|x|^{−3/2}=∞` — **both needed**.

The correct majorant is the SECTOR bound
> `(w+E)^{−c'} ≤ min{w^{−c'}, E^{−c'}} = 𝟙_{E≤w}w^{−c'} + 𝟙_{w<E}E^{−c'}` (equivalent to `(w+E)^{−c'}` up to `2^{c'}`),

and it must be integrated JOINTLY over `(x, Γ)`, never with `Γ` peeled first.

---

## 4. THE FIX (the recipe the formaliser should build) — recombine, don't peel Γ first

The freed triple `∫_{A'}∫_x∫_Γ (freedSchurLoss)^{−c'}` **equals** `∫_{A'}∫_{A₀-chart} frobSq(A₀·Q)^{−c'}`
(the `D↦Γ` shear is measure-preserving and reversible — banked `chartInner_schurShearFree_eq` /
`measurePreserving_shearSub`; Tonelli, all nonneg). So:

1. **Recombine `(x, Γ) → A₀`.** Integrate the pivot rows and the freed Schur block **together** as the
   front A₀-chart integral `g(Q) = ∫_{A₀-chart} frobSq(A₀·Q)^{−c'} dA₀` (do NOT integrate Γ first).
2. **Front-first box-exponent bound (the load-bearing NEW brick).** `g(Q) ≍ σ_q(Q)^{−α}`,
   `α = max{0, 2c' − M₀(q−1)}` (covdesign §CONCESSION; the box keeps the collapsing direction `O(1)`, no
   `σ⁻¹`). Verified here: `g(Q)` for full-rank `Q` is finite for `c'` throughout `[2, 7/2)` (`bridge.py`
   `wzero.py`: `g ≈ 30` stable), where the Γ-first inner bound is `+∞`. **This brick is NOT yet Lean-banked**
   — it is the box-exponent lemma (box-morse-cert ingredient (i)), the genuine new analytic content.
3. **Integrate `A'` against the product-rank tube codim `D`.** `∫_{A'} σ_q(Q)^{−α} < ∞ ⟺ α < D`, closed by
   the linchpin `minAdm(M) ≤ D + M₀(q−1)` with `D = minAdm(reduced by q−1)` — **banked ℕ**
   (`minAdm_eq_frontPeel`), and the `∀M` product-tube leading-power `= D` is settled (`prodD-general.md`,
   task #127). So `c' < ½·minAdm ⟹ α < D` strictly ⟹ finite.

**Alternatively** (if the fill keeps Γ freed): stratify `{w>0}` (where the det-Gram/`corankBlock_morsePeel`
reduction is valid and `∫_{A'}J ≤ |box|w^{−c'}·|A'-box|`) and `{w=0}` (a lower-arity sub-problem: `Q̃ₚ=0`
drops the pivot rows, recurse) — but this IS the joint resolution, and the clean statement is the
recombined front-first bound of steps 1–3.

**What the fill must NOT do:** peel Γ to `det(Q_bQ_bᵀ)^{−p/2}·(residual)` and then bound `∫_{A'}` by `I(p)`
— that bound is `+∞` on `{w=0}` for `c' ∈ [p·b/2, ½·minAdm)`. The banked `corankBlock_morsePeel` /
`freedSchurLoss_inner_peel` (which need PosDef + pivot > 0 + `c' > ab/2` POINTWISE) hold only on `{w>0}` and
on the full-rank stratum; they do NOT discharge the hole alone.

---

## 5. Decorrelated Codex (my conclusion withheld) — CONCUR + three sharpenings adopted

`codex/bridge-answer.md`, asked "does the reduction break?": *"the uniform reduction to `I(p)` is invalid.
It fails generically at a narrow bottleneck... the pivot `w` is load-bearing, cannot be dropped uniformly...
finiteness below minAdm/2 is not proved by either the determinant or pseudo-determinant weight; it requires
a joint rank-stratified/bounded-box resolution."* Q1–Q3 match my exact algebra term-for-term. **Three
sharpenings adopted:** (i) the residual `R` is over the shifted-scaled IMAGE box `Ω`, not full space (the
det-Gram value needs the over-count); (ii) the kernel factor is a NONconstant slice-density `m_B(Z)` (e.g.
the tent `2(√2−|z|)`), and `∫m_B = det⁺^{p/2}|box|` cancels det⁺ exactly; (iii) at the pivot chart `P`
invertible ⟹ `w=0 ⟹ S=0`, so no shift rescues `{w=0}` — the joint pivot integration is the only rescue
(its concrete witness: narrow chain `(3,3,1,4)`, `minAdm=3`, `t=1`, `p=b=2,r=1`: for `1≤c'<3/2` the
`w=0,S=0` inner Γ-integral diverges, every `w>0` finite).

---

## 6. Close

- **Firmest.** The Γ-first → `I(a)` det-Gram reduction does **NOT** close `innerCorankDescent_lt_top`: it is
  a lossy bound that is `+∞` on the pivot-degenerate `{w=0}` locus for `c' ∈ [p·b/2, ½·minAdm)` — exactly
  `[2, 7/2)` for `(3,3,3,4)` (verified: exact threshold `p·b/2` + MC explosion + the joint `g(Q)` finite
  there). The full det-Gram is ill-posed on contracting chains; det⁺ is too crude (cancels with the
  shrinking image); the pivot `w` is load-bearing. Two decorrelated lines (my exact SVD reduction +
  box-vs-full-space + pivot test; Codex's independent derivation).
- **The fix (bounded, not a wall):** recombine `(x, Γ) → A₀` and use the front-first joint bound
  `g(Q) ≍ σ_q(Q)^{−α}` (covdesign §CONCESSION — the box-exponent lemma, the load-bearing NEW brick, NOT yet
  Lean-banked) + `∫_{A'}` against the tube codim `D = minAdm(reduced)` via the banked linchpin (`prodD-general`
  #127). Do NOT peel Γ first.
- **Most likely to break / watch.** The box-exponent lemma `g(Q) ≍ σ_q^{−α}` is the one un-banked analytic
  brick the fill genuinely needs (it is the front-first bound; the tube side is banked Core + banked ℕ). If
  the fill's `innerCorankDescent_lt_top` is shaped around the det-Gram descent, it must be **re-shaped**
  around the recombined front-first bound (or the `{w>0}` / `{w=0}` stratification, which is the same joint
  resolution). The truth is guaranteed (Aoyagi / the joint integral is finite); the sequential Γ-first
  route is the trap.
- **Next.** Relay to the fill (genm-sj5-schur): the freed-Γ hole closes via the JOINT front-first bound,
  not the Γ-first det-Gram descent. Commission the box-exponent lemma `g(Q) ≍ σ_q^{−α}` as the one new
  analytic brick; the tube integration consumes `prodD-general` (#127) + banked Core.

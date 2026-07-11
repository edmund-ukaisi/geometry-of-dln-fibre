# DecoratedStepHyp intersection coupled-estimate — design cert (T4 no-collapse; the deepest StepHyp soundness)

**Seat:** pen-and-paper (forward-scope design cert — genm-sj5-cover, focus-2). **Date:** 2026-07-11. **NO
Lean.** **Charge (team-lead):** establish that on the intersection/deficient-rank rays of the corner blow-up,
the RLCT exponent is `≥ ½·minAdm` via the QUANTITATIVE COUPLED estimate — NOT "higher codim ⟹ slack" (my own
`x²(x²+y^{2N})` correction rules that out). Land the math BEFORE #5 formalises.

**Exact algebra (mine):** `/tmp/prodD/{stephyp,collapse,deeperbranch,db2}.py` (the sum-vs-product RLCT contrast;
the joint-density intersection integral; the exact deeper-branch model). **Decorrelated:** own xhigh
adversarial `local-codex-consult`, conclusion WITHHELD, told to HUNT a hidden collapse:
`codex/stephyp-{prompt,answer}.md`. **Codex earned it** — it confirmed Q1/Q2 and supplied the EXACT
deeper-branch RLCT formula (Q3), which I re-derived and verified. **Consumed:** `corank2-cert §2` (the joint
two-scale density), `transversality-recursion.md §5–§10` (C1, the `{v=0}` refinement), my `x²(x²+y^{2N})`
caveat.

---

## ★ HEADLINE VERDICT

**No collapse is intrinsic to the uniformly-coercive coupled sum** (Q1). The coupled corner `u₀²(U₀+τ²U₁)`
with `U₀,U₁` bounded below has RLCT `½Σ(n_i)=½minAdm` (charges ADD), NOT the product-collapse `min` of the
`z²(x²+y²)` caricature. **BUT the estimate is sound only GIVEN two load-bearing obligations the
`DecoratedStepHyp` MUST establish (not codim-freebies):** **(T4)** a QUANTITATIVE units sector
`σ_min(A₂) ≥ ε` securing `U₀,U₁ ≥ c > 0` UNIFORMLY (pointwise full-rank is NOT enough — the full-rank locus
accumulates on the rank-drop), and **(T-tube)** on the rank-drop NEIGHBOURHOOD (split off, not deleted), a
JOINT tube estimate whose threshold `≥ ½minAdm` — which requires, per branch, the exact criterion
`D/m ≥ n₀` (tube dimension `D` vs vanishing order `m`), NOT codim. **The anchor `(3,3,3,4)` is SECURED** (the
joint density `∫s₂⁻³s₃⁻η dμ<∞ ⟺ η<1 ⟺ c'<7/2` IS the `D/m≥4` case). **General width:** each rank-drop branch
must be CHECKED against `D/m≥n₀` — "full rank generically, so recurse" alone is a GAP.

---

## Q1 — no intrinsic collapse: the coupled SUM-form vs the product caricature — **SOUND**

The resolved corner on the sector `|u₁|≤|u₀|` (`u₁=u₀τ`, `du₀du₁=|u₀|du₀dτ`): integrand
`|u₀|^{p₀+p₁+1−2c}|τ|^{p₁}(U₀+τ²U₁)^{−c}`. If `0<a≤U₀+τ²U₁≤b<∞` (the bracket a UNIT), then for `p_i>−1`
`∫u₀^{p₀+p₁+1−2c}du₀ < ∞ ⟺ c < ½((p₀+1)+(p₁+1))`, i.e.

> **`λ(u₀²(U₀+τ²U₁)) = ½Σ(n_i) = ½minAdm`** (`n_i=p_i+1`; charges ADD; log-divergent at equality; the
> reciprocal chart `u₀=u₁σ` covers the other sector). [V, `/tmp/prodD/collapse.py`, verified 7/2 at the anchor.]

**Contrast the product caricature** `F=z²(x²+y²)`: `∫F^{−c} = (∫|z|^{−2c})(∫r^{1−2c})` finite `⟺ c<½ ∧ c<1`, so
`λ=min(½,1)=½` — the COLLAPSE. **The collapse comes from a genuine PRE-EXISTING divisor** `{z=0}` (on which
`x,y` stay independent; `(zx,zy)=z·(x,y)` has a common factor). The coupled sum's zero set is `{u₀=u₁=0}` — a
POINT, not a union of independent divisors. **So the sum-form is immune iff its residual bracket `U₀+τ²U₁` is
a unit** (bounded below); since `(U₀+τ²U₁)|_{τ=0}=U₀`, this requires `U₀` uniformly bounded below (→ Q2). [V:
SUM `u₀²+u₁²` RLCT=1 (ADD) vs PRODUCT `z²(x²+y²)` RLCT=½ (MIN) — different singularities.]

## Q2 — T4, the load-bearing gate: is `U₀ > 0` bounded below secured? — **NEEDS A QUANTITATIVE SECTOR**

Pointwise full rank is NOT a uniform unit estimate. **Codex counterexample (verified):** `A₂(t)=diag(1,…,1,t)`
is full rank ∀`t>0`, yet `σ_min(A₂)=t→0` and `det(A₂A₂ᵀ)=t²→0`. So the open full-rank locus ACCUMULATES on
the rank-drop, and `U₀>0` pointwise `⇏ inf U₀>0`. **Securing `U₀,U₁ ≥ c > 0` requires a QUANTITATIVE SECTOR
`σ_min(A₂) ≥ ε`** (plus the specific pivot-minor sector if `U₀` is a particular minor, not the full Gram det).
**The rank-drop NEIGHBOURHOOD — where `U₀` is small and the corner constants blow up — CANNOT be deleted as
measure-zero; it must be assigned to another (recursive) branch.** This is exactly my `{v=0}` / C1 refinement,
now with the precise trigger: the split is by `σ_min(A₂)` (a quantitative sector), not by the exact rank-drop
locus. **T4 = "on the sector `σ_min(A₂)≥ε`, `U₀,U₁≥c(ε)>0`"; the `DecoratedStepHyp` must carry this sector,
not merely generic full rank.**

## Q3 — the deeper (rank-drop) branch: threshold `≥ ½minAdm`? — the EXACT criterion `D/m ≥ n₀` (not codim)

A deeper branch CAN genuinely undershoot. Exact local model (Codex, re-derived + verified,
`/tmp/prodD/db2.py`): near the rank-drop, `z∈ℝ^D`, `U₀≍|z|^{2m}`, `U₁≍1`, `F=u₀²|z|^{2m}+u₁²`:

> **`λ(F) = n₁/2 + ½·min(n₀, D/m)`** — the full coupled value `½(n₀+n₁)` is recovered **iff `D/m ≥ n₀`**
> (`D` the tube dimension, `m` the vanishing order of `U₀`). If both units share the factor
> (`U₀,U₁≍|z|^{2m}`): `λ=min(D/(2m), ½(n₀+n₁))` — the product-collapse. `x²(x²+y^{2N})`: `λ=(N+1)/(4N)<½`.

**Codimension alone is NOT enough — the vanishing order `m` matters.** [Confirms my earlier retraction of
"higher codim ⟹ slack".]

- **Anchor `(3,3,3,4)`: SECURED.** The required deeper-branch estimate IS the banked joint density
  (`corank2-cert §2`): `∫ s₂⁻³ s₃⁻η dμ < ∞ ⟺ η=2c'−6 < 1 ⟺ c' < 7/2 = ½minAdm`. In the exact model this is the
  `D/m ≥ n₀=4` case (`n₀=4`=Γ-block `ab`, `n₁=3`=deeper). The rank-drop tube does NOT undershoot. The JOINT
  estimate — not genericity, null-deletion, or marginals (`min(t₂⁴,t₃)`→`η<1/4`) — is what secures it.
- **General width: a GAP for a bare "recurse".** Each rank-drop branch must be CHECKED: `D/m ≥ n₀`, or the
  branch's own joint tube estimate `≥ ½minAdm`. This is the deepest per-branch obligation of the descent.

## The `DecoratedStepHyp` obligations (what #5 must establish — the split conditions)

1. **Uniform coercivity + bounded chart Jacobians on the quantitative full-rank sector** `σ_min(A₂)≥ε` (T4,
   Q2) — `U₀,U₁≥c(ε)>0`, so the coupled corner has RLCT `½minAdm` (Q1), no collapse.
2. **A JOINT tube estimate on the whole small-singular-value neighbourhood** (the rank-drop split-off, Q3) —
   threshold `≥ ½minAdm`, established per branch via `D/m ≥ n₀` (or the joint two-scale density), NOT codim.
3. **Every recursive branch threshold `≥ ½minAdm`**, accounting for BOTH tube density AND vanishing orders.
4. **Uniform seam control + termination** of the `σ_min(A₂)`-rank-stratification.

---

## Firmest / most-likely-to-break / next

- **Firmest.** No collapse intrinsic to the uniformly-coercive coupled sum: `λ=½minAdm` (ADD) given `U₀,U₁`
  bounded below (Q1, exact). The anchor `(3,3,3,4)` deeper branch is SECURED by the banked joint density
  (`D/m≥4`). Decorrelated-confirmed + re-derived.
- **Most likely to break (the two load-bearing gates).** (i) T4: `U₀` bounded below is NOT free from generic
  full rank — needs the quantitative sector `σ_min(A₂)≥ε` (Codex's `diag(1,…,t)` accumulation). (ii) The
  deeper branch is NOT free from codim — the exact `λ=n₁/2+½min(n₀,D/m)` shows the full value needs `D/m≥n₀`;
  a width where a rank-drop branch has `D/m<n₀` would be a genuine collapse (RLCT `<½minAdm`). The anchor is
  safe; the general width MUST check it.
- **Cheapest collapse check (Codex, adopt for the general-width audit).** On the first rank-drop normal chart,
  compute the tube dimension `D` and the leading order `U₀≍ρ^{2m}`; if `n₁/2+½min(n₀,D/m) < ½(n₀+n₁)`, a
  hidden collapse is exposed. A 1-D path `U₀→0` WITHOUT its tube measure is NOT decisive (the tube dimension
  `D` is what rescues it).
- **Next.** When #5 (`DecoratedStepHyp`) is built, audit it against obligations 1–4 — especially that the
  rank-drop split uses the quantitative `σ_min(A₂)≥ε` sector (not generic full rank) and the deeper-branch
  threshold is the joint tube estimate / `D/m≥n₀` (not codim-slack). For the general-width descent, the
  per-branch `D/m≥n₀` check is the concrete verification; if any width fails it, that is the genuine obstruction.

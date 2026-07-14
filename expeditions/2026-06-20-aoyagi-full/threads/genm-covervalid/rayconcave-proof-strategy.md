# Proof strategy — `minAdm` is concave along the leading-width ray (`x ↦ minAdm(redChain x M)`)

**Seat:** pen-and-paper, aoyagi-full Stage 2, `genm-covervalid`. **Date:** 2026-07-14. **NO Lean edits.**
Exact ℕ arithmetic over the real `minAdm`/`minAdmRec` def (`RouteMLayerSplit:58`). Scripts
`scripts/rayconcave_{structure,proof,tworegime,final_proof}.py`; decorrelated Codex `codex/concave-{prompt,answer}.md`.

## Target

`D_M(x) := minAdm(redChain x M) = minAdm((x, M₂, …, M_last))` is **concave** in the leading width `x ≥ 0`
(discretely: `D(x+1) − D(x)` non-increasing), with `D_M(0) = 0`. This gives the **ray form**
`u·minAdm(redChain t M) ≥ t·minAdm(redChain u M)` for `0 < t < u` (the hcvg off-sector prerequisite —
`D(x)/x` non-increasing, from concavity + `D(0)=0`). Verified exact: **0 concavity failures / 17028**
(tails length 1–4, widths 1–6, `x ≤ 12`); ray form 0 failures / 11172 (earlier `/tmp/concav_check.py`).

## Why the naive route fails (holed's obstruction, confirmed)

From `minAdmRec`, `D(x) = min_{s ≤ min(x,M₂)} [(x−s)(M₂−s) + E(s)]` with `E(s) := minAdm((s,M₃,…,M_last))`
x-independent — a min of **x-affine** cells (`g(x,s) = (M₂−s)x + [E(s) − s(M₂−s)]`, slope `M₂−s`) but over
an **x-dependent domain** `s ≤ min(x,M₂)`. The domain GROWS with `x`, adding smaller-slope lines, so "min
of affine ⟹ concave" does not apply off the shelf. Reusing the `u`-minimizer's cut for the `t`-bound needs
`E(s_u) ≥ s_u(M₂−s_u)`, which is FALSE (holed). The x-domain constraint is genuinely binding (verified:
2117 cases where the unconstrained envelope beats `D`) — it cannot be dropped.

## The proof (induction on tail length = chain arity) — COMPLETE, verified 0/17028

**Base** (`|T| = 1`, i.e. `M` arity 3, chain `(x, M₂)` 2-width): `D(x) = x·M₂`, linear ⟹ concave, `D(0)=0`.

**Step** (`|T| ≥ 2`): IH — `E := D_{M'}` (`M' = (M₂,…,M_last)`, one arity shorter) is concave, `E(0)=0`,
**and nonnegative**. Let `smin(x)` = smallest minimizer of `g(x,·)`.

- **F0 (nonneg + concave ⟹ nondecreasing).** A nonnegative concave ℕ-sequence is nondecreasing (a negative
  increment `ΔE(k)<0` propagates `ΔE(n)≤ΔE(k)<0 ∀n≥k` by concavity, forcing `E<0` eventually). Needed for
  F1 — concavity + `E(0)=0` ALONE do NOT give monotone (`E(s)=−s` is concave, `E(0)=0`, decreasing); the
  definitional `minAdm ≥ 0` supplies it. So the induction invariant is **{concave, `D(0)=0`, `D ≥ 0`}**;
  `D ≥ 0` is a separate immediate invariant of `minAdm`.
- **F1 (`D ≤ E`, trivial given F0).** `D(x) ≤ E(x)` for all `x`: take `s = min(x,M₂)` — if `x ≤ M₂`,
  `g(x,x)=E(x)`; if `x > M₂`, `g(x,M₂)=E(M₂) ≤ E(x)` (`E` nondecreasing by F0). [0/17028]

*(A monotone-minimizer fact — `smin(x)` non-decreasing, from `g(x+1,s)−g(x,s)=M₂−s ↓` in `s` /
submodularity — holds (0/17028) but is **NOT needed** for the concavity proof; Codex-flagged, dropped.)*

**Concavity `Δ(x) := D(x+1)−D(x) ≤ Δ(x−1)`, each `x ≥ 1`, two exhaustive cases by pure integrality**
(`smin(x) ∈ {0,…,min(x,M₂)} ⊆ {0,…,x}` is either `≤ x−1` or `= x`; if `x > M₂` only Case A occurs):

- **Case A — `smin(x) ≤ x−1` (interior; covers 13619/17028).** The anchor `s₀ := smin(x)` is feasible at
  `x−1, x, x+1` (`s₀ ≤ x−1 ≤ min(x−1,M₂)`), and `g(·,s₀)` is **affine in `x`**, so
  `g(x−1,s₀) + g(x+1,s₀) = 2·g(x,s₀) = 2·D(x)`. Since `D(x±1) ≤ g(x±1,s₀)`,
  `D(x−1) + D(x+1) ≤ 2·D(x)`. [0 fails]
- **Case B — `smin(x) = x` (boundary/full-pivot, so `D(x) = g(x,x) = E(x)`; covers 3409/17028).**
  A four-link sandwich using only F1 + IH:

      Δ(x)  = D(x+1) − E(x)
            ≤ E(x+1) − E(x)      [F1:  D(x+1) ≤ E(x+1)]
            ≤ E(x)   − E(x−1)    [E concave, IH]
            ≤ E(x)   − D(x−1)    [F1:  D(x−1) ≤ E(x−1)]
            = D(x)   − D(x−1)  = Δ(x−1).

  [each link + conclusion 0 fails]

The two cases exhaust every `x` (verified: coverage 17028/17028). ∎ (strategy)

## Structural facts that make it clean (all verified exact, 0 fails)

- The **boundary regime** `B = {x : D(x) = E(x)} = {x : smin(x) = x}` is an **initial interval** `[0, x₀]`
  (`x₀ ≤ M₂`); on `B`, `D = E` (concave by IH). Interior `x > x₀`: `smin(x) ≤ x−1`. (This is the geometric
  content behind the case split; Case B's sandwich actually needs neither the initial-interval fact nor
  `D(x−1)=E(x−1)` — only F1 + IH — so the formalization can skip it.)
- Full concavity (not just the ray form) holds — so state and prove **concavity**; the ray form is the
  `D(0)=0` corollary (`D(x)/x` non-increasing).

## Verdict: LABOUR, not a wall. Formalization shape

Clean, self-contained, `Core`-level `minAdm` structural result (network-free; belongs near `RouteMLayerSplit`).
Formalization pieces, in order (Codex-audited — VERDICT: proof CORRECT; F2 dropped as unused):
1. `nonneg_concave_mono` (F0): a nonnegative concave ℕ-sequence is nondecreasing. Tiny, generic.
2. `minAdm_le_dropLead` (F1): `minAdm((x,)+T) ≤ minAdm((x,)+T')` — `D ≤ E`. (From the `s=min(x,M₂)` cell +
   F0 applied to `E`.)
3. `minAdm_redChain_concave` (the headline): arity induction with invariant **{concave, `=0` at 0, `≥ 0`}**;
   Case A (affine anchor midpoint) + Case B (F1 + IH-concavity sandwich); `≥0` is the trivial `minAdm` invariant.
4. `minAdm_redChain_ray` (corollary): `u·D(t) ≥ t·D(u)` for `t ≤ u`, from concavity + `D(0)=0`.

**Every step is affine algebra or a two-line order argument** — no submodular monotone-minimizer needed
(F2 was a red herring). The case split is pure integrality. LABOUR, not a wall.

## Note on current need (endgame-lanes, 2026-07-14)

cruxfin's simplified crux (row-Gram floor + `hpiv`, `2c' < minAdm' + ab ≤ uρ + ab`) may DROP hcvg from the
(a) chain, mooting the *specific* hcvg use of this ray-concavity. Per the controller it is banked regardless
as a clean `minAdm` structural fact (concavity along the leading-width ray) — reusable, and the exact
certificate + proof are here.

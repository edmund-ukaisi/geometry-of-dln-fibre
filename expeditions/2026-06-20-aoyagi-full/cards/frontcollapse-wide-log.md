# Statement card — the LOG cell of the front-collapse atom (BOTH wings, critical density)

**Status:** sorry-free, **clean-three** (`[propext, Classical.choice, Quot.sound]`, forced
`#print axioms` on all six results), WIDE arm fidelity-reviewed **FAITHFUL** (`log-reviewer` + Codex xhigh);
tall + both-wings fidelity review PENDING. Built on branch `genm-log`; merged `origin/genm-b0bdd`
(`fixedF_tall_cov_bound`) clean. Module `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontCollapseLog.lean`
(+ the merged `RouteMSJFrontCollapseTallBounded.lean` from `genm-b0bdd`). No Aoyagi cite, no
`native_decide`, no new `sorry`.

This is the **LOG cell** of `frontCollapseRankSector_lt_top` (the Lane-1 native heart, atom §1) — the
critical density `M₂ = |M₀ − M₁| + 1` (slack `s = |M₀ − M₁|`, so `M₂ = s + 1`), the boundary one above
the LANDED bounded cells (`frontCollapse_wide_bounded_lt_top` / `frontCollapse_tall_bounded_lt_top`,
density `M₂ ≤ s`) where the naive Gram density factor diverges. BOTH wings.

---

## THE LOG cell (parametric, both wings)

```
theorem frontCollapse_log_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hlog : M 2 = max (M 0) (M 1) - min (M 0) (M 1) + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤
```

- **Lean:** `DLNFibre.DLN.RLCT.frontCollapse_log_lt_top`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontCollapseLog.lean`, branch `genm-log`).
- **Gloss.** For a `≥ 3`-width chain `M` at the critical/LOG density `M₂ = max(M₀,M₁) − min(M₀,M₁) + 1`,
  GIVEN the plain one-shorter strong IH `hIH`, below the geometric threshold `c' < ½·minAdm M`, the
  front-factor box integral over `F ∈ wingFrontBox M` and `A' ∈ paramsBoxM(tailChain M) 1` is finite.
  Conclusion + `hIH` + `c'` + `hc'` are **identical** to the atom `frontCollapseRankSector_lt_top`;
  `hlog` selects the LOG density (nat `max−min+1`, wing-agnostic).
- **Proved.** The full finiteness at the FULL threshold `c' < ½·minAdm M`, BOTH wings, by dispatch on
  `le_total (M 0) (M 1)` to the two wing arms below.
- **Assumed.** `hlog` (LOG/critical density); `hIH`, `hc'` (the atom's own hypotheses). No extra analytic
  gate beyond the atom's.
- **Cited.** none (no Aoyagi cite). Banked in-repo bricks only + Mathlib Hölder + `CFC.sqrt` (tall root,
  classical).
- **Deferred.** Wiring this cell into `frontCollapseRankSector_lt_top`'s dispatch `sorry`
  (`RouteMSJFrontCollapse.lean:59`) and into the aggregator `DLNFibre.lean` (controller's single-writer
  job). No mathematical gap remains for the LOG density.

## Wing arms

```
theorem frontCollapse_wide_log_lt_top (M) (hwide : M 0 ≤ M 1)
    (hlog : (M 2 : ℝ) = (M 1 : ℝ) - M 0 + 1) (hIH) (c') (hc') : … < ⊤
theorem frontCollapse_tall_log_lt_top (M) (htall : M 1 ≤ M 0)
    (hlog : (M 2 : ℝ) = (M 0 : ℝ) - M 1 + 1) (hIH) (c') (hc') : … < ⊤
```

- **WIDE (`a=0`)** rides `fixedF_wide_cov_bound` (`RouteMSJFrontCoV`) + row-Gram density `det(F·Fᵀ)` +
  `front_gram_qbox_real_lt_top`. Reviewed FAITHFUL.
- **TALL (`b=0`)** rides the banked square-root CoV `fixedF_tall_cov_bound`
  (`RouteMSJFrontCollapseTallBounded`, thread `genm-b0bdd`: `P = CFC.sqrt(FᵀF)`, `det(FᵀF)^{−M₂/2}`) +
  column-Gram density `det(Fᵀ·F)` + `front_gram_qbox_tall_real_lt_top`. Same Hölder trade.

## Route (Hölder exponent-trade, NOT a δ-fold)

At `M₂ = s + 1` the free-`F` Gram `∫ det(Gram)^{−M₂/2}` sits EXACTLY at its convergence boundary, so the
naive route (and the δ-fold) diverges. Fix `F`, pick a Hölder exponent `q > 1` with
`q·c' < ½·minAdm(redChain (min M₀ M₁) M)` (room from `saturated_threshold`; `q = (1 + T/c')/2`,
`T = ½·minAdm(redChain)`; the `c'=0` branch is the trivial `≡1` integrand):

1. Hölder on the finite box `Ω` with `g ≡ 1`: `J_{c'}(F) ≤ (J_{q·c'}(F))^{1/q} · vol(Ω)^{1/q'}`.
2. exponent-agnostic absorption CoV at `q·c'` (`wide_fixedF_absorb` / `tall_fixedF_absorb`):
   `J_{q·c'}(F) ≤ det(Gram)^{−M₂/2} · Ke`, `Ke < ⊤` by `hIH` at `q·c'`.
3. take `(·)^{1/q}`: `J_{c'}(F) ≤ det(Gram)^{−M₂/(2q)} · const`.
4. integrate over `F`: converges by the REAL-exponent qbox at `a = M₂/q < M₂ = s + 1` (strict since
   `q > 1`) — `front_gram_qbox_real_lt_top` (wide) / `front_gram_qbox_tall_real_lt_top` (tall).

Verified independently on `M = (1,2,2)` (wide, LOG): naive `∫ det(FFᵀ)⁻¹` diverges as `∫ dr/r`; the traded
`∫ det^{−1/q}` converges as `∫ r^{1−2/q} dr` for `q>1`; K-side needs `q·c' < 1`, room since
`c' < 1 = ½·minAdm`.

## Supporting lemmas (same module, all clean-three)

- `wide_fixedF_absorb` / `tall_fixedF_absorb` — fixed-`F` absorption at a **general real exponent** `e`
  (`0 ≤ e < ½·minAdm(redChain (min M₀ M₁) M)`): `∃ Ke < ⊤, ∀ F, J_e(F) ≤ det(Gram)^{−M₂/2}·Ke`. The
  exponent-agnostic core the trade rides on (density exponent `M₂/2` geometric; only `Ke`, closed by
  `hIH` at `e`, carries `e`). Each duplicates the fixed-`F` half of the corresponding landed bounded arm
  at a general exponent — a controller-side extract could DRY it (landed files left untouched).
- `front_gram_qbox_real_lt_top` / `front_gram_qbox_tall_real_lt_top` — the `M₂:ℕ` front-Gram qbox
  (row-Gram / column-Gram) restated at a REAL density `a`; trivial (`bRowGram_colBall_lt_top` is already
  `{a:ℝ}`; the tall one is the transpose reduction, mirror of `front_gram_qbox_tall_lt_top`).

## Inherited caveat (NOT a LOG-cell defect; out of scope)

`Real.rpow` gives `0^{−c'} = 0` for `c' > 0`, so where `frobSq = 0` the integrand is `0` (finite), not
`+∞`. This is inherited TEXTUALLY from the atom's integrand and the whole RLCT box-integral encoding — not
introduced by this cell — and for a finiteness claim it can only help. It belongs to the atom/RLCT-encoding
fidelity question, not this cell (flagged by `log-reviewer` + Codex; no action here).

# Statement card — the `a=0` WIDE LOG cell of the front-collapse atom (critical density)

**Status:** sorry-free, **clean-three** (`[propext, Classical.choice, Quot.sound]`, forced
`#print axioms`), fidelity review PENDING. Built on branch `genm-log` off `genm-lane1-shell @bc3b74cd6`.
New module `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontCollapseLog.lean`. No Aoyagi cite, no
`native_decide`, no new `sorry`.

This is the **LOG cell** of `frontCollapseRankSector_lt_top` (the Lane-1 native heart, atom §1) — the
critical density `M₂ = M₁ − M₀ + 1` of the wide wing. It is the wing-mirror sibling of the LANDED
bounded cell `frontCollapse_wide_bounded_lt_top` (`RouteMSJFrontCollapseWide`, density `M₂ ≤ M₁ − M₀`),
restricted to the boundary density where the naive Gram–Schmidt density factor DIVERGES.

---

## The LOG cell

```
theorem frontCollapse_wide_log_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hwide : M 0 ≤ M 1) (hlog : (M 2 : ℝ) = (M 1 : ℝ) - M 0 + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M, ∫⁻ A' in paramsBoxM (tailChain M) 1,
        ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤
```

- **Lean:** `DLNFibre.DLN.RLCT.frontCollapse_wide_log_lt_top`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontCollapseLog.lean` @ `c1d30197`, branch `genm-log`).
- **Gloss.** For a `≥ 3`-width chain `M`, a WIDE front (`M₀ ≤ M₁`) at the LOG (critical) density
  `M₂ = M₁ − M₀ + 1`, GIVEN the plain one-shorter strong IH `hIH` (`RouteMBoxThresholdFinite` for every
  chain of one fewer layer), below the geometric threshold `c' < ½·minAdm M`: the front-factor box
  integral `∫∫ frobSq(F · prod(tailChain M) A')^{−c'}` over `F ∈ wingFrontBox M` (front matrix, entries
  in `[−1,1]`, leading `min(M₀,M₁)×min(M₀,M₁)` block invertible) and `A' ∈ paramsBoxM(tailChain M) 1`
  (the deep-tail parameter box) is finite. The conclusion, `hIH`, `c'`, and `hc'` are **identical** to
  the atom `frontCollapseRankSector_lt_top`; the two added hypotheses `hwide`+`hlog` select exactly the
  WIDE-LOG dispatch cell.
- **Proved.** The full finiteness, at the FULL threshold `c' < ½·minAdm M` (not a shaved sub-threshold),
  reaching the critical density.
- **Assumed.** `hwide : M₀ ≤ M₁` (wide wing); `hlog : (M₂ : ℝ) = M₁ − M₀ + 1` (the LOG/critical density
  — the exact boundary the bounded cell excludes); `hIH` (the one-shorter box-finiteness recursion, the
  atom's own hypothesis); `hc'` (sub-threshold, the atom's own hypothesis). No extra analytic gate
  beyond the atom's.
- **Cited.** none (no Aoyagi cite). Consumes only banked in-repo bricks — `fixedF_wide_cov_bound`
  (`RouteMSJFrontCoV`), `qbox_lintegral_lt_top` via `CorankSlabD.bRowGram_colBall_lt_top`,
  `frontFactor_split` (`RouteMSJFrontCollapseWide`), `saturated_threshold` — plus Mathlib's Hölder
  (`ENNReal.lintegral_mul_le_Lp_mul_Lq`).
- **Deferred.** The **TALL (`b=0`) LOG cell** is NOT built here (WIDE only). It is the transpose mirror
  but needs a *tall* absorption CoV (`fixedF_tall_cov_bound`, the `P = C·√(FᵀF)` square-replacement
  route) which is not yet banked; `front_gram_qbox_tall_lt_top` (the tall density factor) IS banked, so
  the tall-LOG lands once that absorption is built (see mirror note below / the file docstring). Also
  deferred: wiring this cell into `frontCollapseRankSector_lt_top`'s dispatch `sorry` (`RouteMSJFrontCollapse.lean:59`)
  and into the aggregator `DLNFibre.lean` (controller's single-writer job).

## Route (Hölder exponent-trade, NOT a δ-fold)

At `M₂ = M₁ − M₀ + 1` the free-`F` front-Gram `∫ det(F·Fᵀ)^{−M₂/2}` sits EXACTLY at its convergence
boundary (`M₂ = M₁ − M₀ + 1`, not `<`), so the naive route (and the δ-fold) diverges. Fix `F`, pick a
Hölder exponent `s > 1` with `s·c' < ½·minAdm(redChain M₀ M)` (room from `saturated_threshold`, which
gives `c' < ½·minAdm(redChain M₀ M)`; concretely `s = (1 + (½minAdm(redChain))/c')/2`; the `c'=0` branch
is the trivial `≡1` integrand):

1. Hölder on the finite box `Ω` with `g ≡ 1`: `J_{c'}(F) ≤ (J_{sc'}(F))^{1/s} · vol(Ω)^{1/s'}`.
2. the exponent-agnostic absorption CoV at `sc'` (`wide_fixedF_absorb`, packaging
   `fixedF_wide_cov_bound`): `J_{sc'}(F) ≤ det(F·Fᵀ)^{−M₂/2} · Ke`, `Ke < ⊤` by `hIH` at `sc'`.
3. take `(·)^{1/s}`: `J_{c'}(F) ≤ det(F·Fᵀ)^{−M₂/(2s)} · const`.
4. integrate over `F`: converges by the REAL-exponent qbox at `a = M₂/s < M₂ = M₁ − M₀ + 1` (strict
   since `s > 1`) — `front_gram_qbox_real_lt_top`.

Verified independently on `M = (1,2,2)` (wide, slack `1`, LOG `M₂=2`, `minAdm = 2`): the naive
`∫ det(FFᵀ)⁻¹` diverges as `∫ dr/r`; the traded `∫ det^{−1/s}` converges as `∫ r^{1−2/s} dr` for `s>1`;
the K-side `∫ ‖A‖^{−2sc'}` converges as `sc' < 1`, with room since `c' < 1 = ½·minAdm`.

## Supporting lemmas (same module, both clean-three)

- `wide_fixedF_absorb` — the fixed-`F` wide absorption at a **general real exponent** `e`
  (`0 ≤ e < ½·minAdm(redChain M₀ M)`): `∃ Ke < ⊤, ∀ F ∈ wingFrontBox M,
  J_e(F) ≤ det(F·Fᵀ)^{−M₂/2}·Ke`. The exponent-agnostic core the trade rides on (density exponent
  `M₂/2` is purely geometric; only `Ke`, closed by `hIH` at `e`, carries `e`). This duplicates the
  fixed-`F` half of `frontCollapse_wide_bounded_lt_top` at a general exponent — a controller-side
  refactor could extract one shared copy from the WIDE file (left untouched here to avoid touching
  landed code).
- `front_gram_qbox_real_lt_top` — the `M₂:ℕ` front-Gram qbox restated at a REAL density `a`; trivial,
  the backing `CorankSlabD.bRowGram_colBall_lt_top` is already `{a:ℝ}`.

## Mirror note (tall `b=0` LOG)

The tall wing is NOT a clean transpose of the whole integral (unlike the single-Gram-det brick
`front_gram_qbox_tall_lt_top`), because the front-collapse integrand carries the full chain product
`prod(tailChain M)` and the `wingFrontBox`, which do not transpose layer-wise. The tall-LOG needs the
tall absorption CoV first (the `P = C·√(FᵀF)` square-SPD replacement → plain square left-mult CoV →
`det(FᵀF)^{−M₂/2}`), the `b=0`-bounded builder's piece. Once `fixedF_tall_cov_bound` lands, the
tall-LOG is `wide_fixedF_absorb`'s mirror + `front_gram_qbox_tall_lt_top` (already banked) with the same
Hölder trade.

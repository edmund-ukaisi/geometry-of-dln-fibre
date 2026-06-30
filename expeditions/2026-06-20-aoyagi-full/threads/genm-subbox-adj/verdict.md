# genm-subbox-adj — VERDICT: sub-box-divergence tolerates the LIVE poly det

**Seat:** pen-and-paper, obstruction (third fully-decorrelated read).
**Question:** does the R1-LOWER box-divergence tolerate a Jacobian det of the form
`monomial(u_p) × (a.e.-positive polynomial in independent K-coords)` — the LIVE chart
`phiFlatLiveR1`'s det `|u_p|^(minAdm−1)·|det K|^(r+c)` — or is pure-monomial load-bearing?

## VERDICT: CONFIRMED-WITH-SCOPE (the mathematics is sound; the *engine reuse* claim is over-read)

The **mathematical** claim is TRUE: the box-divergence holds with the LIVE poly det. My exact-algebra
anchor + a fully-decorrelated Codex (hypothesis-withheld) both confirm `I(c*) = ⊤`.

But two precise corrections to the chart owner's framing (UPDATE-519), both load-bearing for the
formaliser:

1. **The existing `NodeAchieverChart.cov` / `nodeLeaf_box_div` chain is NOT reusable as-is.** The `cov`
   field hardcodes the c-o-v weight as `ofReal(∏_j |u_j|^{leafH_j})` — a *pure monomial*. The LIVE
   chart's genuine Jacobian is `|u_p|^{m−1}·|det K|^{r+c}`, so the truthful c-o-v weight carries the
   extra `|det K|^{r+c}` factor. You **cannot** instantiate the frozen `cov` field truthfully for the
   LIVE chart. The chart owner already says "add a sub-box-divergence *variant*" — so this is a NEW atom
   (`routeMCore_box_diverges` consuming a poly-det cov), NOT a reuse of `nodeLeaf_box_div`. Stated
   correctly, the claim "the LIVE route works DIRECTLY with the existing engine" is FALSE; the correct
   claim is "a new, small poly-det variant atom suffices — no kLDU monomialization."

2. **The det-free fields ARE genuinely reusable.** `leaf_integrand` is RATE-based and det-free
   (`leaf_integrand_of_rate`, `RouteMGenLeafIntegrand.lean:43` — a pure algebraic identity in the rate
   `F = u_p²·V`, `V ≥ 0`; `leafH` is a free parameter appearing identically on both sides). So the
   chart bundle minus `cov` transfers. The only thing that must change is the c-o-v + the box-div atom.

## The certificate (exact, M222 r=1 anchor)

Confirmed against the real Lean objects:

- **Rate (banked):** `routeMCore_phiFlatLive` (`RouteMFlatLive.lean:149`) gives
  `routeMCore M (phiFlatLive … x) = (x p)² · UvalLive x`, `UvalLive ≥ 0` (`UvalLive_nonneg:160`).
- **LIVE det (validated, UNCONDITIONAL clean-three):** `interiorDet_headline_222`
  (`RouteMBData222.lean:1274`):
  `|det Dφ(phiFlatLiveR1At … pRad) u| = |u_pRad|^{minAdm−1} · ∏_s engine_s`, with `engine222 = |aRead|²`
  (`RouteMBData222.lean:1244`) and `minAdm M222 = 3` (`active222_card:566`). I.e.
  `|det Dφ| = |u_pRad|^{2}·|aRead|^{2}` = `|u_p|^{m−1}·|det K|^{r+c}` with `m−1 = 2`, `r+c = 1+1 = 2`.
  `aRead_eq` (`:651`): `aRead x = x readerSlotK` — a *single source coordinate* at r=1.

**The pulled-back box integrand** (genuine-Jacobian c-o-v, source box `[0,δ]^N`):

      |u_p|^{m−1} · |det K|^{r+c} · |F∘φ|^{−c}
    = |u_p|^{m−1} · |det K|^{r+c} · (u_p² · U)^{−c}
    = |u_p|^{(m−1) − 2c} · |det K|^{r+c} · U^{−c}.

**Net pivot exponent at threshold `c* = m/2`:** `(m−1) − 2·(m/2) = m−1−m = −1` (exact). `∫₀^δ u_p^{−1} du_p
= ⊤` — the boundary log-divergence. (M222: `(3−1) − 2·(3/2) = 2 − 3 = −1`.)

**The lemma chain (variant atom), each step verified sound:**

1. *Restrict to the source sub-box* `S = [0,δ]^N ∩ {|det K(u_K)| ≥ δ₀}` (`δ₀ > 0`). For r=1, `det K` is a
   single coordinate axis `a`, so `S` is itself a product box `(∏_{j≠q}[0,δ]) × [δ₀,δ]_a` — the Tonelli
   split survives intact.
2. *Lower-bound the integrand on S* using `U ≤ B` (the `Ubound` field; `U^{−c} ≥ B^{−c} > 0`, since
   `−c < 0`) **and** `|det K|^{r+c} ≥ δ₀^{r+c} > 0`:

       integrand ≥ (δ₀^{r+c}·B^{−c}) · |u_p|^{(m−1)−2c}   =:  C · |u_p|^{−1}  at c=c*,  C > 0.

   This lower bound **factors** as (function of u_p) × (positive const) — the key that the coupled `U`
   does not break: rescue via the *upper* bound `U ≤ B`, NOT a lower bound on U (Codex independently
   flagged the same rescue).
3. *The factored lower bound diverges* by exactly the existing engine's mechanism
   (`monomialIntegrand_lintegral_box_eq_top`, `Case222Cover.lean:283`): the `MeasurableEquiv` reindex +
   `setLIntegral_prod` (Tonelli) split the binding axis `p` (`|u_p|^{−1}` → ⊤ via
   `abs_rpow_lintegral_Ioo_eq_top`) from the rest (positive-finite via `prod_rpow_lintegral_Ioo_box_pos`
   for r=1, where the rest is still a pure `∏|u_j|^{e_j}`).
4. *Lift to the full box* via `lintegral_mono_set` (Mathlib `Lebesgue/Basic.lean:98`): orientation
   confirmed `s ⊆ t → ∫_s ≤ ∫_t` for `f : α → ℝ≥0∞` (no measurability hyp). So `∫_S = ⊤ ⟹ ∫_{[0,δ]^N} =
   ⊤ ⟹ ∫_{φ-image} = ⊤ ⟹ ∫_{cubeBox ε} = ⊤`.

## Checks against the brief (all four)

1. **Coordinate separability (highest risk):** CONFIRMED SOUND, with a sharpened caveat. The pivot `u_p`
   (= `pRad`) and the K-block coords are genuinely DISJOINT source coordinates; the achiever exponent on
   `u_p` is `(m−1)−2c`, *independent of `u_K`*; restricting `|det K| ≥ δ₀` does not constrain `u_p`. The
   one subtlety the sketch glossed: the integrand does NOT literally factor (the unit `U` couples all
   coords), so the clean Tonelli split is on the **lower bound** `C·|u_p|^{−1}`, obtained via `U ≤ B`.
   This is a genuine extra step, not in the sketch's four-line argument, but it is exactly the existing
   `nodeLeaf_box_div` pattern (which already lower-bounds `U^{−c} ≥ B^{−c}`).
2. **Achiever exponent on S:** CONFIRMED. Net `u_p` power `= −1` at `c*=3/2` for M222 (exact algebra
   above); `≤ −1` is divergent; the `|det K|≥δ₀` restriction leaves `u_p ∈ (0,δ)` full.
3. **Sub-box positivity:** CONFIRMED for r=1 (`det K = aRead = ` coordinate axis `a`, so `{|a|≥δ₀}` is a
   half-line, trivially positive measure, `det K ≢ 0`). For **r ≥ 2** this becomes a NEW obligation (see
   scope below).
4. **`lintegral_mono_set` lift:** CONFIRMED — exists in Mathlib, orientation correct (superset ≥ subset
   for nonneg integrand).

## SCOPE / where each sufficient condition bites (the obstruction catalogue)

The variant atom is BOUNDED (no research wall). Sufficient conditions, and where each is load-bearing:

- **r = 1 (the M222 anchor, and any leaf with a 1×1 K-core):** FULLY CLEAN. `det K` is a single source
  coordinate, `S` is a product box, the existing pure-`∏|u_j|^{e_j}` engine applies to the lower bound
  verbatim after carving the `a`-axis to `[δ₀,δ]`. No new positivity lemma.
- **r ≥ 2 (genuine `t×t` K-core, `t ≥ 2`):** `det K_s` is a genuine multivariate polynomial (degree
  `t_s`). Two new obligations bite, BOTH bounded-as-math:
  - (a) `vol([0,δ]^N ∩ {|det K_s| ≥ δ₀}) > 0` — a nonzero-polynomial superlevel-set positive-measure
    statement. Standard (the zero set of a nonzero poly is null), but it is a NEW lemma not in the
    monomial engine (which never needed it — its "rest" axes were pure boxes).
  - (b) On that non-box region the binding-axis Tonelli split is still valid (p disjoint from the K-block),
    but `setLIntegral_prod`'s inner "rest" integral is over `{|det K|≥δ₀}∩box` (not a product box) and must
    be shown positive — fed by (a) + the integrand floor.
- **The `Ubound` a.e.-positivity (`interiorLDU_Ubound`-analog for LIVE = `UvalLive` positivity):** still
  required (the `U ≤ B` upper bound + `U > 0` a.e. is what makes the lower bound `C·|u_p|^{−1}`
  legitimate where `U > 0`). For the LIVE chart this is the interior-drop pivot-survival witness
  (`achieverUfun_wInt_ne_zero`-analog); it does NOT need the kLDU lens.

## The kLDU question (the headline payoff)

CONFIRMED: the kLDU monomialization is **not a divergence necessity** — it was a `NodeAchieverChart.cov`
*convenience* (the frozen pure-monomial weight). Dropping it is sound **provided** the formaliser builds
the poly-det variant atom above (a new `cov` with weight `|u_p|^{m−1}·|det K|^{r+c}` + the sub-box
divergence). The LIVE det is already banked unconditionally at M222 (`interiorDet_headline_222`); the
∀M-L2 LIVE det is the in-flight genm-detfderiv deliverable. So the LIVE route dissolves the kLDU
subsystem **at the cost of one new variant atom** (much smaller than the LDU multi-tide), NOT at zero
cost / pure reuse.

## Most likely thing to break it

The r ≥ 2 positivity lemma (a) is the one place where "the LIVE poly det is just like a monomial" stops
being literally true: the existing engine's "rest = pure ∏|u_j|^{e_j} box" is replaced by a polynomial
superlevel region. It is bounded-as-math but it is genuinely new measure-theory the monomial engine
never carried. If the formaliser tries to literally reuse `prod_rpow_lintegral_Ioo_box_pos` it will fail
for r ≥ 2. A clean route: lower-bound `|det K|^{r+c} ≥ δ₀^{r+c}` on S and treat the *whole* K-block as a
single positive-finite factor via the new superlevel-positivity lemma, leaving only the p-axis monomial
to drive ⊤.

## Next construction to settle the open part

Build the variant atom signature now (it is the contract): a `PolyDetAchieverChart M` differing from
`NodeAchieverChart` in ONE field — `cov` weight `|u_p|^{m−1}·polyP(u_K)` + a `polyP ≥ δ₀ on S, positive
measure` field — and a `routeMCore_box_diverges_polyDet` mirroring
`routeMCore_box_diverges_of_nodeChart` with the sub-box `S` carved before the final `lintegral_mono_set`.
The r=1 instance closes immediately (M222 anchor); the r≥2 superlevel lemma is the one genuinely-new
brick.

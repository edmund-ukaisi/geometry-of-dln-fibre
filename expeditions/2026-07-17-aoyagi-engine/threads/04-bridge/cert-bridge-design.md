# Cert — the chart↔monomial-integrand CoV bridge design (t04-bridge)

**Seat:** pen-and-paper (design-first, decorrelated from the skeleton). **Date:** 2026-07-17.
**Target:** the CoV bridge r2 finding 2 showed is absent — the reason `region_glue`
(`Engine/EngineObligations.lean:166`) is a placeholder. **Method:** read the r2 carrier/obligations;
survey the banked CoV primitives; EXACT symbolic verification (sympy) of the pullback + Jacobian on
real resolution charts; one decorrelated Codex consult (`codex/bridge-design-{prompt,answer}.md`). NO
Lean built; NO `rlct = c*`.

---

## VERDICT: the bug is real and localized; the fix is a per-leaf CoV bridge (chart map + pullback +
## Jacobian + IMAGE cover). The leaf integrand is monomial × RESIDUAL (bounded-unit OR Morse) — the
## current pure-monomial `monomialChartIntegral` OMITS the residual. CanonicalResolution MUST gain the
## bridge (a bundle change — flagged loudly). All identities verified EXACT on (2,2,2) + a (3,3,4) chart.

## 1. The bug, precisely (r2 finding 2), and an exact counterexample

`region_glue` consumes `ChartsCover M t` (`EngineObligations.lean:47`), which constrains the leaves'
`chartDom : Set (Params M)` only as an ABSTRACT set (`locus ⊆ U ⊆ ⋃ chartDom`, opens). Nothing ties
`chartDom` to a chart MAP or to the loss. So `chartDom = Set.univ` (exactly `witLeaf`,
`EngineObligations.lean:192`) satisfies `ChartsCover` vacuously, for ANY `divExp`. Hence
`ChartsCover ∧ hrat ⊬ (box integral < ⊤)`. **Exact counterexample** (`battery-drafts/g-chartscover-vacuity.py`,
exit 0): for `M=(2,2,2)` (true `½ minAdm = 3/2`), a fake all-`univ` atlas with `divExp={4}` satisfies
`ChartsCover` and `hrat` at `c'=8/5 ∈ [3/2, 2)`, yet `routeMLayerBoxIntegral(2,2,2, 8/5) = ⊤` (the
banked achiever divergence for `c' > 3/2`). The current signature admits a counterexample → the bridge
is required.

## 2. The corrected structure (verified EXACT on real charts)

The leaf-level fact (sympy, `battery-drafts/g-chart-bridge-pullback.py`, exit 0): for a chart map `φ_l`,

    (P) F ∘ φ_l  =  ( ∏_k (u_k)^{2} ) · R_l          [loss pullback]
    (J) |det Dφ_l|  =  ( ∏_k (u_k)^{divExp_k − 1} ) · J_l    [Jacobian ledger, J_l a positive constant here]

where the product runs over the leaf's exceptional divisors `u_k`, `R_l` is the RESIDUAL — EITHER a
**bounded unit** (`0 < lo ≤ R_l ≤ hi`) OR a **nondegenerate (Morse) residual core of rank ρ_l**
(`R_l ≍ ‖(regular coords)‖²`, resolved by the banked radial read). Verified:

| chart | pullback | Jacobian | residual | threshold |
|---|---|---|---|---|
| (2,2,2) δ-chart | `α²δ²·R` | `α³δ²` | Morse rank 5 | `min(2, 3/2, 5/2)=3/2` = ½minAdm |
| (2,2,2) u-chart | `α²u²·R` | `α³u²` | bounded unit | `min(2, 3/2, ∞)=3/2` = ½minAdm |
| (3,3,4) corank-2 | `δ²·R`, **δ shared over all 8 gens** | `δ³` | Morse rank 8 | `min(2, 4)=2` = ½minAdm(2,2,4) |

The threshold reads `min_k (divExp_k)/2` AND `ρ_l/2` (residual) — matching `½ minAdm`. Two findings:
**(F1)** the leaf integrand is monomial × residual, NOT a pure monomial — the current
`monomialChartIntegral` (`EngineObligations.lean:49`, pure `∏ u_k^{(divExp_k−1)−2c'}`) OMITS `R_l`;
**(F2)** at corank ≥ 2 a SINGLE divisor `δ` divides EVERY generator (the sharing) — the pullback must
carry this (the typed `support` field is what encodes it; cf. compass fork-3).

## 3. THE SIGNATURE DIFF (Lean-shaped; the architect pins the exact form)

**(a) LeafData gains the chart map + residual (`ResolutionTree.lean`):**

    -- NEW fields on `structure LeafData`:
    numChartVar : ℕ                                   -- = flatDim M (φ is a CoV of the ambient box)
    chartMap    : (Fin numChartVar → ℝ) → Params M    -- the substitution (blow-up∘shear composite)
    srcBox      : Set (Fin numChartVar → ℝ)           -- the chart's source cube
    resRank     : ℕ                                    -- rank of the residual Morse core (0 = bounded unit)
    -- `divExp`, `bExp/bChain`, `divProfile` STAY; `chartDom` becomes DERIVED = chartMap '' srcBox.

**(b) the loss-pullback predicate (NEW, replaces the abstract `chartDom` tie):**

    def LeafPullback (l : LeafData M) : Prop :=
      ∃ lo hi : ℝ, 0 < lo ∧
        ∀ u ∈ l.srcBox,
          frobSq (prod M (l.chartMap u))
            = (∏ k, (u (divCoord k)) ^ (2 : ℕ)) * residualCore l u        -- (P)
          ∧ lo * baseForm l u ≤ residualCore l u ≤ hi * baseForm l u
    -- baseForm l u = ‖regular coords‖²  (Morse, rank resRank)  OR  = 1  (bounded unit, resRank = 0).

**(c) the Jacobian ledger predicate (NEW):**

    def LeafJacobian (l : LeafData M) : Prop :=
      ∃ Jhi : ℝ, 0 < Jhi ∧
        ∀ u ∈ l.srcBox, HasFDerivWithinAt l.chartMap (Dφ u) l.srcBox u ∧
          |(Dφ u).det| = (∏ k, (u (divCoord k)) ^ (l.divExp k - 1)) * jacUnit u
          ∧ 0 < jacUnit u ∧ jacUnit u ≤ Jhi                                -- (J)

**(d) the corrected `ChartsCover` → `ChartBridge` (IMAGE cover + the two identities + injectivity):**

    def ChartBridge (M) (t : ResolutionTree M) : Prop :=
      (∃ U, IsOpen U ∧ {A | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
         U ⊆ ⋃ l ∈ leaves t, l.chartMap '' l.srcBox)          -- IMAGE cover (was: abstract chartDom)
      ∧ (∀ l ∈ leaves t, Set.InjOn l.chartMap l.srcBox ∧ LeafPullback l ∧ LeafJacobian l)

**(e) the corrected `region_glue` SIGNATURE:**

    theorem region_glue (M) (hbridge : ChartBridge M (resolutionOf M)) (c' : ℝ)
        (hrat : ∀ e ∈ terminalExponents (resolutionOf M), c' < (e : ℝ)/2)
        (hres : ∀ l ∈ leaves (resolutionOf M), c' < (l.resRank : ℝ)/2) :   -- NEW: residual ratio
        routeMLayerBoxIntegral M c' 1 < ⊤

The separated `divExp/2` ratio form STAYS (cert-d3 A1 stands — `hrat`); `hres` is the residual
guard. `monomialChartIntegral` gains the residual factor `· residualCore l u` (or the leaf integral is
`(monomial part) × (radial read of the rank-`resRank` core)`).

## 4. BUNDLE CHANGE — flagged LOUDLY (re-opens the gated CanonicalResolution shape)

`CanonicalResolution` (`EngineObligations.lean:85`) currently conjoins `… ∧ ChartsCover M t ∧ …`. It
MUST become `… ∧ ChartBridge M t ∧ …` (ChartsCover strengthened to the image-cover + pullback +
Jacobian). Consequences the controller/architect must weigh:
- `coverage_theorem` (`:144`) now returns `ChartBridge` (its conclusion type changes) — coverage-design
  owns proving the IMAGE cover + injectivity, still WITHOUT `rlct=c*` (unchanged circularity guard).
- `monomialization_terminates` (`:102`, the construction hole) now must ALSO produce the chart maps +
  prove `LeafPullback`/`LeafJacobian` per leaf — MORE content in the tide, but it is the honest content
  the placeholder hid (the CoV IS the resolution). `witLeaf` (`chartDom=univ`) no longer type-checks as
  a canonical leaf (it has no chart map / fails LeafPullback) — the vacuity is closed at type strength.
- `witTree`/`witNode` non-vacuity witnesses need a real `chartMap` (the `(2,2,2)` δ-chart is the
  smallest genuine one — supplied by this cert's sympy).

## 5. Banked lemma per bridge step / the P8 composer interface I am pinning

| step | banked lemma (or GAP) |
|---|---|
| shear sub-steps of `chartMap` (unit Jac) | `CoreShearMP.measurePreserving_coreShear` |
| **elementary blow-up sub-step (monomial Jac)** | **GAP — P8 composer** (no banked box-level blow-up CoV) |
| per-chart box CoV `∫_{φ(src)} = ∫_src (F∘φ)^{-c'}|det Dφ|` | Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (needs `InjOn`+`HasFDerivWithinAt` — from `LeafJacobian`); **the P8 composer assembles this** |
| image cover → subadditivity | `lintegral_mono_set` / `measure_biUnion_le` (Mathlib) |
| strip bounded-unit residual | `S1NonMPTransport.rlctAtOn_boundedUnit_localHomeomorph` / `weightedThreshold_weight_unit_invariant` |
| Morse residual read (rank ρ) | `RouteMSJRadialInt.lintegral_norm_rpow_neg_ball_lt_top` (`< ⊤ iff c' < ρ/2`) |
| single monomial axis | `RouteMSJRadialPolar.lintegral_Ioc_rpow_lt_top` (`c' < divExp/2`) |
| RLCT-level transport (alt route) | `S1NonMPTransport.weightedThreshold_transport` |

**The P8 composer interface I am pinning:** given a leaf `chartMap` = a composite of shears [banked MP]
and elementary blow-ups [the gap], produce (i) each elementary blow-up's box-level Jacobian CoV, and
(ii) the composition `∫_{φ(src)} F^{-c'} = ∫_src (F∘φ)^{-c'}|det Dφ|` via Mathlib's
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` fed by `LeafPullback`/`LeafJacobian`. That is the P8
lane's contract.

## 6. Kill-condition + truth witness (standing rule 2)

**Kill-condition for this design:** a `chartMap` whose pullback is NOT `monomial × (bounded-unit OR
Morse)` — e.g. a residual that is a genuine SUM of incomparable monomials (`⟨d₁x,d₂y⟩`) rather than a
single dominant monomial × residual — is not a real leaf (cert-d3 A1: the separated read undershoots
there). **Truth witness (all EXACT, exit 0):** every obligation this design pins is satisfiable —
`g-chart-bridge-pullback.py` exhibits three real charts satisfying (P)+(J) with threshold `= ½ minAdm`
(the pullback/Jacobian identities are non-vacuous), and `g-chartscover-vacuity.py` witnesses that the
OLD signature is unsound (so the strengthening is necessary, not decorative). No obligation is named
without a smallest-instance satisfiability check.

## 7. Firmest / most likely to break / next

- **Firmest:** the bug is real (exact counterexample) and the fix is exactly a per-leaf CoV bridge; the
  two identities + the threshold are verified EXACT on `(2,2,2)` (both chart types) and a `(3,3,4)`
  corank-2 chart (shared divisor). The Jacobian is a pure monomial (clean); the residual is Morse or
  bounded-unit.
- **Most likely to break it:** the **residual factor** (F1). If the tide keeps `monomialChartIntegral`
  pure-monomial, it silently drops the Morse residual `R_l` and the finiteness proof is incomplete
  (the residual ratio `ρ_l/2` must enter the min, and `LeafPullback` must expose `R_l`). Smallest
  exposure: the `(2,2,2)` δ-chart (Morse rank 5 residual) — a pure-monomial leaf integrand there is
  missing a factor. Second risk: the elementary blow-up box-CoV (the P8 gap) — no banked lemma.
- **Next construction (P8 lane + tide):** (i) the elementary blow-up box-level Jacobian CoV
  (P8 composer); (ii) `LeafPullback`/`LeafJacobian` for the `(2,2,2)` δ-chart in Lean (this cert's
  sympy is the spec); (iii) wire `region_glue` to the assembled CoV + the banked radial reads. The
  bundle change (§4) is the controller's call — it re-opens the CanonicalResolution shape.

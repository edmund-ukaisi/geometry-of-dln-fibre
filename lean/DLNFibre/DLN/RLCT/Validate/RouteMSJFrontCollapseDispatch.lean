import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseWide

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapseDispatch` — the front-collapse cell dispatch

**Thread `genm-checkpoint` (LATE-158).** The relocated front-collapse rank-sector atom
`frontCollapseRankSector_lt_top`: the `by_cases`-on-wing then `M₂`-vs-`s` (`s = |M₀−M₁|`) six-cell
dispatch that funnels the front-factor box integral to one of the density cells. It sits DOWNSTREAM of
`RouteMSJFrontCollapseWide` (it consumes the LANDED `frontCollapse_wide_bounded_lt_top`, which lives
there), so it cannot sit in `RouteMSJFrontCollapse` (upstream of Wide).

## The six cells (2 wings × 3 densities; `s = max(M₀,M₁) − min(M₀,M₁)`)

- **BOUNDED** (`M₂ ≤ s`): a=0 WIDE — `frontCollapse_wide_bounded_lt_top` (LANDED, `RouteMSJFrontCollapseWide`,
  Gram–Schmidt route); b=0 TALL — `frontCollapse_tall_bounded_lt_top` (LANDED on `genm-b0bdd`,
  `RouteMSJFrontCollapseTallBounded`; INTERIM placeholder here, swap at integration).
- **LOG** (`M₂ = s + 1`): a=0 WIDE — `frontCollapse_wide_log_lt_top` (LANDED on `genm-log`,
  `RouteMSJFrontCollapseLog`; INTERIM placeholder here); b=0 TALL — `frontCollapse_tall_log_lt_top`
  (BLOCKED — needs the unbanked tall absorption CoV `fixedF_tall_cov_bound`; the one genuinely-open cell).
- **POWER** (`M₂ ≥ s + 2`): both wings — the NEUTRAL WALL `PowerCellFinite` (a plain `Prop` hypothesis).

## Checkpoint status

This atom is BANKED STANDALONE — it is NOT on the path of the checkpoint theorem
`routeMBoxThresholdFinite_of_walls` (whose two hypotheses are `DeepCorankFinite` + `D1DispatchFinite`).
It records what the `d ≤ 1` arm's eventual native fill will consume: BOUNDED both wings native (landed),
WIDE LOG native (landed), TALL LOG open (`fixedF_tall_cov_bound`), POWER a wall. The reduction that wires
this wing-level integral to the freed-`Γ` socket of `innerCorankDescent_lt_top` (the outer `(S,J)`
descent, for the corank-0 wings) is not yet built — that is the `D1DispatchFinite` wall.

Three INTERIM placeholders carry `sorryAx`: `frontCollapse_tall_bounded_lt_top` (swap for `genm-b0bdd`),
`frontCollapse_wide_log_lt_top` (swap for `genm-log`), `frontCollapse_tall_log_lt_top` (open). After the
two swaps only TALL LOG remains a `sorry`. All are OFF the checkpoint theorem's path.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators Matrix

variable {L : ℕ}

/-- **NEUTRAL WALL — `PowerCellFinite`: the front-collapse POWER-cell box-finiteness (both wings).** A
plain mathematical hypothesis (NOT attributed): in the POWER density regime
(`M₂ ≥ s + 2`, `s = max(M₀,M₁) − min(M₀,M₁)`), below `½·minAdm M`, the front-factor box integral over
`wingFrontBox M × paramsBoxM(tailChain M)` is finite. Carried as a `Prop` HYPOTHESIS — VISIBLE in the
type of `frontCollapseRankSector_lt_top`. Banked STANDALONE toward the eventual native fill of the
`d ≤ 1` arm; covers both the wide (a=0) and tall (b=0) POWER cells via the `max`/`min` form. -/
def PowerCellFinite : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ)
    (_hpow : max (M 0) (M 1) - min (M 0) (M 1) + 2 ≤ M 2)
    (_hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (_hc' : (c' : ℝ) < (minAdm M : ℝ) / 2),
    (∫⁻ F in wingFrontBox M,
        ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤

/-- **INTERIM PLACEHOLDER (thread `genm-b0bdd`) — the b=0 TALL BOUNDED cell.** For a tall front
(`M₁ ≤ M₀`) in the bounded density regime (`M₂ < M₀ − M₁ + 1`, i.e. `M₂ ≤ M₀ − M₁`), below `½·minAdm M`,
the front-factor box integral is finite. Wing-mirror of the LANDED `frontCollapse_wide_bounded_lt_top`
(the b=0 tall front-Gram brick, `det(FᵀF)` via transpose). This is the exact signature `genm-b0bdd`'s
real proof will occupy; the `sorry` swaps out when that lands. -/
theorem frontCollapse_tall_bounded_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (htall : M 1 ≤ M 0) (hbnd : (M 2 : ℝ) < (M 0 : ℝ) - M 1 + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M,
        ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  sorry

/-- **LANDED elsewhere (thread `genm-log`, `RouteMSJFrontCollapseLog`) — the a=0 WIDE LOG cell.** At the
critical wide density `M₂ = M₁ − M₀ + 1` (`hlog` in real-cast form), below `½·minAdm M`, the front-factor
box integral is finite (the δ-fold route on `fixedF_wide_cov_bound`). This is an INTERIM placeholder at
`genm-log`'s EXACT delivered signature (clean-three, sorry-free on its own branch); the controller swaps
this `sorry` for the real `RouteMSJFrontCollapseLog.frontCollapse_wide_log_lt_top` at integration. -/
theorem frontCollapse_wide_log_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hwide : M 0 ≤ M 1) (hlog : (M 2 : ℝ) = (M 1 : ℝ) - M 0 + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M,
        ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  sorry

/-- **INTERIM PLACEHOLDER (BLOCKED) — the b=0 TALL LOG cell.** At the critical tall density
`M₂ = M₀ − M₁ + 1` (`hlog` real-cast), below `½·minAdm M`, the front-factor box integral is finite. The
`genm-log` route is WIDE-ONLY (rides `fixedF_wide_cov_bound`, needs `m ≤ n`); the tall mirror needs the
tall absorption CoV `fixedF_tall_cov_bound` (the `P = C·√(FᵀF)` square-SPD replacement), which is NOT yet
banked (only the density factor `front_gram_qbox_tall_lt_top` exists). So this cell stays a `sorry` until
that lands (the heart2 / b=0-bounded builder's piece). Signature mirrors the wide-LOG cell. -/
theorem frontCollapse_tall_log_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (htall : M 1 ≤ M 0) (hlog : (M 2 : ℝ) = (M 0 : ℝ) - M 1 + 1)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M,
        ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  sorry

/-- **THE ATOM (§1) — the front-collapse rank-sector finiteness (the six-cell dispatch).** For a
`≥ 3`-width chain `M`, GIVEN the plain one-shorter strong IH `hIH`, below the geometric threshold
(`c' < ½·minAdm M`) and the POWER-cell wall `PowerCellFinite`, the front-factor box integral over
`wingFrontBox M × paramsBoxM(tailChain M)` is finite. Dispatches on wing (`le_total M₀ M₁`) then on
`M₂` vs `s = |M₀−M₁|` (bounded/LOG/POWER): BOUNDED wide = `frontCollapse_wide_bounded_lt_top` (LANDED),
BOUNDED tall = `frontCollapse_tall_bounded_lt_top`, LOG = `frontCollapse_log_lt_top`, POWER = the wall
`PowerCellFinite`. Banked STANDALONE (off the checkpoint theorem's path). -/
theorem frontCollapseRankSector_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hPower : PowerCellFinite) :
    (∫⁻ F in wingFrontBox M,
        ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  rcases le_total (M 0) (M 1) with hwide | htall
  · -- WIDE wing (a=0): M₀ ≤ M₁, s = M₁ − M₀
    rcases lt_trichotomy (M 2) (M 1 - M 0 + 1) with hb | hlog | hpow
    · -- BOUNDED: M₂ < M₁ − M₀ + 1
      have hbnd : (M 2 : ℝ) < (M 1 : ℝ) - M 0 + 1 := by
        have hc : ((M 1 - M 0 : ℕ) : ℝ) = (M 1 : ℝ) - M 0 := Nat.cast_sub hwide
        have h2 : (M 2 : ℝ) < ((M 1 - M 0 : ℕ) : ℝ) + 1 := by exact_mod_cast hb
        rw [hc] at h2; exact h2
      exact frontCollapse_wide_bounded_lt_top M hwide hbnd hIH c' hc'
    · -- LOG: M₂ = M₁ − M₀ + 1 → the a=0 WIDE LOG cell (real-cast bridge)
      have hlog' : (M 2 : ℝ) = (M 1 : ℝ) - M 0 + 1 := by
        rw [hlog]; push_cast [Nat.cast_sub hwide]; ring
      exact frontCollapse_wide_log_lt_top M hwide hlog' hIH c' hc'
    · -- POWER: M₁ − M₀ + 1 < M₂ (so s + 2 ≤ M₂)
      have hpow' : max (M 0) (M 1) - min (M 0) (M 1) + 2 ≤ M 2 := by
        rw [max_eq_right hwide, min_eq_left hwide]; omega
      exact hPower M hpow' hIH c' hc'
  · -- TALL wing (b=0): M₁ ≤ M₀, s = M₀ − M₁
    rcases lt_trichotomy (M 2) (M 0 - M 1 + 1) with hb | hlog | hpow
    · -- BOUNDED: M₂ < M₀ − M₁ + 1
      have hbnd : (M 2 : ℝ) < (M 0 : ℝ) - M 1 + 1 := by
        have hc : ((M 0 - M 1 : ℕ) : ℝ) = (M 0 : ℝ) - M 1 := Nat.cast_sub htall
        have h2 : (M 2 : ℝ) < ((M 0 - M 1 : ℕ) : ℝ) + 1 := by exact_mod_cast hb
        rw [hc] at h2; exact h2
      exact frontCollapse_tall_bounded_lt_top M htall hbnd hIH c' hc'
    · -- LOG: M₂ = M₀ − M₁ + 1 → the b=0 TALL LOG cell (real-cast bridge; BLOCKED cell)
      have hlog' : (M 2 : ℝ) = (M 0 : ℝ) - M 1 + 1 := by
        rw [hlog]; push_cast [Nat.cast_sub htall]; ring
      exact frontCollapse_tall_log_lt_top M htall hlog' hIH c' hc'
    · -- POWER: M₀ − M₁ + 1 < M₂ (so s + 2 ≤ M₂)
      have hpow' : max (M 0) (M 1) - min (M 0) (M 1) + 2 ≤ M 2 := by
        rw [max_eq_left htall, min_eq_right htall]; omega
      exact hPower M hpow' hIH c' hc'

end DLNFibre.DLN.RLCT

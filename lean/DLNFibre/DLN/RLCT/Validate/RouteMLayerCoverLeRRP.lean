import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverHfin
import DLNFibre.DLN.RLCT.Validate.RouteMBoxThresholdRRP

/-!
# `RouteMLayerCoverLeRRP` — the `cover_le` UPPER leg, CLOSED for the depth-2 `(r,r,p)` family

The bounded-and-now-CLOSED slice of the `cover_le` UPPER leg: for the depth-2 three-width chain
`M = (![r, r, p])` (`r, p ≥ 1`), the `IsRouteMCover.cover_le` field holds SORRY-FREE — by composing the
two banked atoms:

- `routeMLayerCover_hfin` (`RouteMLayerCoverHfin.lean`) — the `hfin` finiteness, MODULO `hbox :
  RouteMBoxThresholdFinite M` and `hpos : 1 ≤ minAdm M`; and
- `routeMBoxThresholdFinite_rrp r p` (`RouteMBoxThresholdRRP.lean`) — the box-finiteness `hbox`,
  banked clean-three (`[propext, Classical.choice, Quot.sound]`) for ALL `r, p` via the
  WellFounded-on-corank Schur recursion (`core_schurGen_lt_top` ∘ the sorry-free `schurRecStep_p`).

So the open analytic input `hbox` that `routeMLayerCover_hfin` carries IS discharged for this family.
The `cover_le` field then assembles via the abstract `routeM_coverLe_of_finiteness` + the banked RHS
positivity `layerCover_rhs_ne_zero`. NO `sorry`, NO new axiom (the `monomial_rlct`/S2 cite is the same
one `routeMLayerCover_hfin` already rides; the `(r,r,p)` `hbox` is S2-free).

## Scope (the depth-2 `(r,r,p)` family is a genuine SUBFAMILY, NOT all of L=2)

`(![r, r, p])` has `M0 = M1 = r` (a SQUARE first matrix factor `A0 : r×r`). General `L=2` chains
`(M0, M1, M2)` with `M0 ≠ M1` have a RECTANGULAR `A0 : M0×M1` and a DIFFERENT binding geometry: the
threshold `½·minAdm(M0,M1,M2) = ½·min_{0≤t≤min(M0,M1)}[(M0−t)(M1−t) + t·M2]` is genuinely larger than the
square `½·minAdm(r,r,M2)` (e.g. `minAdm(2,3,4) = 6 ≠ 4 = minAdm(2,2,4)`, verified `#eval`). The banked
`SchurCore p r` recursion is hardcoded to a SQUARE `Δ : matBox r r`, so it does NOT cover `M0 ≠ M1`.
General `(M0,M1,M2)` box-finiteness at the correct threshold is **additional bounded work** (the
asymmetric `(M0−t)(M1−t)` Schur recursion — no new wall, but a rectangular generalisation of the same
machinery), NOT subsumed by this wiring. This file closes the SQUARE-`A0` subfamily; that is the honest
scope of what the banked `routeMBoxThresholdFinite_rrp` delivers.

## What this banks (the full `IsRouteMCover` for `(![r,r,p])` still needs the LOWER leg `cover_ge_div`)

- `minAdm_rrp_pos` — `1 ≤ minAdm(![r,r,p])` for `r, p ≥ 1` (the `hpos` non-degeneracy), via the `inf'`
  lower bound (`minAdm_rrp_eq_inf`).
- `routeMLayerCover_coverLe_rrp` — the `cover_le` field for `(![r,r,p])`, sorry-free. This is the UPPER
  leg of the `(r,r,p)` cover; the full `IsRouteMCover` is gated on the SEPARATE `cover_ge_div` LOWER leg
  (the box-divergence atom, the `RouteMLayerCoverGE` lane — not this file).
-/

open MeasureTheory
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- **`1 ≤ minAdm(![r,r,p])` for `r, p ≥ 1`** (the `hpos` non-degeneracy `routeMLayerCover_hfin` needs).
Via `minAdm_rrp_eq_inf`: every stratum `(r−t)(r−t) + t·p` (`0 ≤ t ≤ r`) is `≥ 1` — for `t < r` the block
`(r−t)² ≥ 1`, for `t = r` the column term `r·p ≥ 1` (`r, p ≥ 1`). So the `inf'` is `≥ 1`. -/
theorem minAdm_rrp_pos (r p : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p) :
    1 ≤ minAdm (![r, r, p] : Fin 3 → ℕ) := by
  rw [minAdm_rrp_eq_inf]
  apply Finset.le_inf'
  intro t ht
  rw [Finset.mem_range] at ht
  rcases Nat.lt_or_ge t r with htlt | htge
  · -- t < r: the block (r−t)² ≥ 1.
    have h1 : 1 ≤ r - t := by omega
    have : 1 ≤ (r - t) * (r - t) := by
      calc 1 = 1 * 1 := by ring
        _ ≤ (r - t) * (r - t) := Nat.mul_le_mul h1 h1
    omega
  · -- t = r: the column term r·p ≥ 1.
    have htr : t = r := by omega
    subst htr
    have : 1 ≤ t * p := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega

/-- **The `cover_le` UPPER leg, CLOSED for `(![r,r,p])` (`r, p ≥ 1`), sorry-free.** The
`IsRouteMCover.cover_le` field for the flat core `routeMCore (![r,r,p])` over the box
`routeMBaseNbhd (![r,r,p])` with the layer atlas's chart family: for every `c'` there is a finite
prefactor `C` with `∫⁻_U |routeMCore|^{−c'} ≤ C · (leaf-sum)`. Assembled from the abstract
`routeM_coverLe_of_finiteness` with the two banked atoms: the RHS positivity `layerCover_rhs_ne_zero` and
the finiteness `routeMLayerCover_hfin`, whose open `hbox` is discharged here by the banked
`routeMBoxThresholdFinite_rrp r p` (clean-three ∀r∀p) and whose `hpos` by `minAdm_rrp_pos`. This is the
bounded UPPER win for the SQUARE-`A0` depth-2 subfamily; the full `(r,r,p)` `IsRouteMCover` is gated on
the SEPARATE `cover_ge_div` LOWER leg. -/
theorem routeMLayerCover_coverLe_rrp (r p : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p) :
    ∀ c' : NNReal, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∫⁻ x in routeMBaseNbhd (![r, r, p] : Fin 3 → ℕ),
          ENNReal.ofReal (|routeMCore (![r, r, p] : Fin 3 → ℕ) x| ^ (-(c' : ℝ)))
        ≤ C * ∑ i : (routeLayerAtlas (![r, r, p] : Fin 3 → ℕ)).ι,
            ∫⁻ y in unitBox (layerD (![r, r, p] : Fin 3 → ℕ) i),
              ENNReal.ofReal (monomialIntegrand (layerD (![r, r, p] : Fin 3 → ℕ) i)
                (layerK (![r, r, p] : Fin 3 → ℕ) i)
                (layerH (![r, r, p] : Fin 3 → ℕ) i) (c' : ℝ) y) :=
  routeM_coverLe_of_finiteness (routeMCore (![r, r, p] : Fin 3 → ℕ))
    (routeMBaseNbhd (![r, r, p] : Fin 3 → ℕ))
    (layerD (![r, r, p] : Fin 3 → ℕ)) (layerK (![r, r, p] : Fin 3 → ℕ))
    (layerH (![r, r, p] : Fin 3 → ℕ))
    (layerCover_rhs_ne_zero (![r, r, p] : Fin 3 → ℕ))
    (routeMLayerCover_hfin (![r, r, p] : Fin 3 → ℕ) (minAdm_rrp_pos r p hr hp)
      (routeMBoxThresholdFinite_rrp r p))

/-- **Non-vacuity (the worked `(3,3,4)` anchor).** The `(r,r,p)` `cover_le` lane fires on `r = 3, p = 4`
— the smallest binding corank-2 case (`minAdm(3,3,4) = 8`, threshold `4`). Confirms the wiring is
non-vacuous and reproduces the anchor family. -/
theorem routeMLayerCover_coverLe_M334 :
    ∀ c' : NNReal, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∫⁻ x in routeMBaseNbhd (![3, 3, 4] : Fin 3 → ℕ),
          ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ)))
        ≤ C * ∑ i : (routeLayerAtlas (![3, 3, 4] : Fin 3 → ℕ)).ι,
            ∫⁻ y in unitBox (layerD (![3, 3, 4] : Fin 3 → ℕ) i),
              ENNReal.ofReal (monomialIntegrand (layerD (![3, 3, 4] : Fin 3 → ℕ) i)
                (layerK (![3, 3, 4] : Fin 3 → ℕ) i)
                (layerH (![3, 3, 4] : Fin 3 → ℕ) i) (c' : ℝ) y) :=
  routeMLayerCover_coverLe_rrp 3 4 (by norm_num) (by norm_num)

end DLNFibre.DLN.RLCT

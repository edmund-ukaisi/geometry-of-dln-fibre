import DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurThresholdP` — the ∀p Schur threshold witness

The output-width-`p` generalisation of `schurLambda` (`RouteMSchurGeneral`, the `p = 4` threshold) and its
`SchurThreshold 4` witness. This is the BASE-INDEPENDENT arithmetic piece of the `schurRecStep_p` bundle
(task #146): it depends only on `minAdm` / `minAdmRec` (`RouteMLayerSplit`, via `RouteMSchurGeneral`'s
import closure) and the abstract `SchurThreshold` contract — NOT on the carve, the radial chart, or the
`(r,r,4)` box infra. So it composes onto any integration base that has the carve + the box reshape.

## The witness (Option B — reuse `minAdm`)

`schurLambdaP p r := (minAdm (![r, r, p]) : ℝ) / 2` — the depth-2 `(r,r,p)` geometric threshold, the
`p`-general analog of `schurLambda r` (which is `schurLambdaP 4 r`, the content of genm-n4's
`minAdm_rr4_eq`). Reusing `minAdm` keeps the Schur threshold aligned with the global Aoyagi/`minAdm`
library and makes the downstream threshold-match `½·minAdm(![r,r,p]) = schurLambdaP p r` a definitional
unfolding rather than a separate bridge.

## The three `SchurThreshold p` contract fields

* `lambda0` — `schurLambdaP p 0 = 0` (the corank-0 leaf, `minAdmRec` of a `Fin 1` chain is `0`).
* `radial_le` — `schurLambdaP p r ≤ r²/2`, i.e. `minAdm(![r,r,p]) ≤ r²`, via the `t = 0` stratum
  `(r−0)² + p·0 = r²` in the `inf'` (cap B, the `r²` radial-divisor a-axis).
* `peel_le` — `schurLambdaP p r ≤ jp/2 + schurLambdaP p (r−j)` for `1 ≤ j ≤ r`, i.e. the codim
  sub-additivity `minAdm(![r,r,p]) ≤ jp + minAdm(![r−j,r−j,p])`. The one genuinely-new arithmetic: proved
  by the **stratum-lift** — a binding stratum `t'` for the residual `(r−j)` lifts to the stratum `t'+j`
  for `r`, with `(r−(t'+j))² + p(t'+j) = ((r−j)−t')² + p·t' + p·j` (the exact algebraic identity, validated
  numerically p=1..11, r=1..11).

`schurLambdaP_satisfies_threshold : SchurThreshold p (schurLambdaP p)` packages all three — the abstract
contract is inhabited in-Lean at every `p`, so `core_schurGen_lt_top (p) (schurLambdaP p) …` is non-vacuous
∀p (the wrapper consumes the contract, the carve/engine supply the deferred `SchurRecStep p`).
-/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

/-! ## The witness `schurLambdaP` -/

/-- **The ∀p Schur threshold** `schurLambdaP p r := ½·minAdm(![r,r,p])` — the depth-2 `(r,r,p)` geometric
threshold. The `p`-general analog of `schurLambda` (`= schurLambdaP 4`, genm-n4's `minAdm_rr4_eq`). -/
noncomputable def schurLambdaP (p r : ℕ) : ℝ := (minAdm (![r, r, p] : Fin 3 → ℕ) : ℝ) / 2

/-! ## The per-stratum value of `minAdm(![r,r,p])` (the `inf'` over rank-drops `t`) -/

/-- `minAdm(![r,r,p]) = inf'_{t ≤ r} [(r−t)² + p·t]` — the layer-peel `minAdmRec` at the `Fin 3` chain,
with the `Fin 1` residual leaf `minAdmRec (redChain t (![r,r,p])) = redChain t … 0 = t`... no: the residual
is a `Fin 2` leaf `(t, p)` with value `t·p`. So each stratum is `(r−t)(r−t) + t·p`. -/
theorem minAdm_rrp_eq_inf (r p : ℕ) :
    minAdm (![r, r, p] : Fin 3 → ℕ)
      = (Finset.range (r + 1)).inf' (by simp)
          (fun t => (r - t) * (r - t) + t * p) := by
  rw [← minAdmRec_eq_minAdm, minAdmRec_succ_succ]
  -- `(![r,r,p]) 0 = r = (![r,r,p]) 1` (defeq), so `min … + 1 = r + 1` (defeq, same index set); the
  -- residual `minAdmRec (redChain t …) = t * p`, so the body is `(r−t)(r−t) + t·p` per-`t`. The two
  -- `inf'`s have a defeq index set and pointwise-equal bodies — prove the body equality per `t`, then
  -- the `inf'`s coincide by `le_antisymm` (avoid rewriting under the dependent-nonempty motive).
  have hbody : ∀ t : ℕ, ((![r, r, p] : Fin 3 → ℕ) 0 - t) * ((![r, r, p] : Fin 3 → ℕ) 1 - t)
      + minAdmRec (redChain t (![r, r, p] : Fin 3 → ℕ)) = (r - t) * (r - t) + t * p := by
    intro t
    rw [show minAdmRec (redChain t (![r, r, p] : Fin 3 → ℕ)) = t * p by
      rw [minAdmRec_leaf]; simp [redChain]]
    show (r - t) * (r - t) + t * p = (r - t) * (r - t) + t * p
    rfl
  -- the index set `range (min (M 0) (M 1) + 1)` is defeq to `range (r + 1)`; bodies pointwise-equal
  -- (`hbody`), so the two `inf'`s coincide by `le_antisymm` (no rewriting under the dependent motive).
  have hmem : ∀ t : ℕ, t ∈ Finset.range (r + 1) ↔
      t ∈ Finset.range (min ((![r, r, p] : Fin 3 → ℕ) 0) ((![r, r, p] : Fin 3 → ℕ) 1) + 1) := by
    intro t
    have h0 : (![r, r, p] : Fin 3 → ℕ) 0 = r := rfl
    have h1 : (![r, r, p] : Fin 3 → ℕ) 1 = r := rfl
    rw [h0, h1, min_self]
  refine le_antisymm ?_ ?_
  · refine Finset.le_inf' _ _ (fun t ht => ?_)
    exact Finset.inf'_le_of_le _ ((hmem t).1 ht) (le_of_eq (hbody t))
  · refine Finset.le_inf' _ _ (fun t ht => ?_)
    exact Finset.inf'_le_of_le _ ((hmem t).2 ht) (le_of_eq (hbody t).symm)

/-! ## The three `SchurThreshold` contract fields -/

/-- `schurLambdaP p 0 = 0` (the corank-0 leaf): `minAdm(![0,0,p])` is the `inf'` over `range 1 = {0}` of
`(0−t)²+t·p`, i.e. the single `t = 0` term `0`. -/
theorem schurLambdaP_zero (p : ℕ) : schurLambdaP p 0 = 0 := by
  rw [schurLambdaP, minAdm_rrp_eq_inf]
  norm_num

/-- The cap-B bound `schurLambdaP p r ≤ r²/2`, i.e. `minAdm(![r,r,p]) ≤ r²` (the `t = 0` stratum
`(r−0)² + 0·p = r²` witnesses the `inf'`). -/
theorem schurLambdaP_le_sq (p r : ℕ) : schurLambdaP p r ≤ (r ^ 2 : ℝ) / 2 := by
  rw [schurLambdaP, minAdm_rrp_eq_inf]
  -- `minAdm = inf'_{t} [(r−t)²+t·p] ≤ (r−0)²+0·p = r²` (the `t = 0` witness), then `/2`.
  have hle : (Finset.range (r + 1)).inf' (by simp) (fun t => (r - t) * (r - t) + t * p)
      ≤ r * r := by
    have h0 : (0 : ℕ) ∈ Finset.range (r + 1) := by simp
    refine le_trans (Finset.inf'_le _ h0) ?_
    simp
  have hleR : (((Finset.range (r + 1)).inf' (by simp)
      (fun t => (r - t) * (r - t) + t * p) : ℕ) : ℝ) ≤ (r ^ 2 : ℝ) := by
    rw [show (r ^ 2 : ℝ) = ((r * r : ℕ) : ℝ) by push_cast; ring]
    exact_mod_cast hle
  linarith

/-- **The codim sub-additivity (the new arithmetic): `minAdm(![r,r,p]) ≤ jp + minAdm(![r−j,r−j,p])`** for
`1 ≤ j ≤ r`. Proved by the stratum-lift `t' ↦ t'+j`. -/
theorem minAdm_rrp_subadd (p : ℕ) {r j : ℕ} (hj : 1 ≤ j) (hjr : j ≤ r) :
    minAdm (![r, r, p] : Fin 3 → ℕ)
      ≤ j * p + minAdm (![r - j, r - j, p] : Fin 3 → ℕ) := by
  rw [minAdm_rrp_eq_inf, minAdm_rrp_eq_inf]
  -- argmin `t'` for the residual `(r−j)` core
  obtain ⟨t', ht'mem, ht'eq⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (r - j + 1))
    (H := by simp) (f := fun t => (r - j - t) * (r - j - t) + t * p)
  rw [ht'eq]
  have ht'le : t' ≤ r - j := by rw [Finset.mem_range] at ht'mem; omega
  -- the lifted stratum `t' + j ≤ r` of the `r` core; its value equals the residual value + jp
  have hmem : t' + j ∈ Finset.range (r + 1) := by rw [Finset.mem_range]; omega
  refine le_trans (Finset.inf'_le _ hmem) ?_
  -- stratum-lift identity: (r−(t'+j))²+(t'+j)p = ((r−j)−t')²+t'p + jp   (since t'+j ≤ r)
  have hsub : r - (t' + j) = r - j - t' := by omega
  have hexp : (r - (t' + j)) * (r - (t' + j)) + (t' + j) * p
      = j * p + ((r - j - t') * (r - j - t') + t' * p) := by
    rw [hsub]; ring
  rw [hexp]

/-- The cap-A peel bound `schurLambdaP p r ≤ jp/2 + schurLambdaP p (r−j)` for `1 ≤ j ≤ r`. -/
theorem schurLambdaP_peel_le (p : ℕ) {r j : ℕ} (hj : 1 ≤ j) (hjr : j ≤ r) :
    schurLambdaP p r ≤ ((j : ℝ) * (p : ℝ)) / 2 + schurLambdaP p (r - j) := by
  -- divide the ℕ sub-additivity `minAdm(r) ≤ jp + minAdm(r−j)` by 2 (cast to ℝ).
  have hsub := minAdm_rrp_subadd p hj hjr
  have hcast : ((minAdm (![r, r, p] : Fin 3 → ℕ) : ℝ))
      ≤ (j : ℝ) * (p : ℝ) + ((minAdm (![r - j, r - j, p] : Fin 3 → ℕ) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 hsub
    push_cast at this; linarith
  rw [schurLambdaP, schurLambdaP]
  linarith

/-- **The concrete ∀p threshold satisfies the contract.** `schurLambdaP p` is a `SchurThreshold p` — the
abstract contract is inhabited at every `p`, so `core_schurGen_lt_top (p) (schurLambdaP p)` is non-vacuous
∀p. The `p`-general analog of `schurLambda_satisfies_threshold` (`p = 4`). -/
theorem schurLambdaP_satisfies_threshold (p : ℕ) : SchurThreshold p (schurLambdaP p) where
  lambda0 := schurLambdaP_zero p
  radial_le := fun {r} _ => schurLambdaP_le_sq p r
  peel_le := fun {r j} hj hjr => schurLambdaP_peel_le p hj hjr

/-! ## The threshold-match keystone: `schurLambdaP 4 = schurLambda` (p=4 instance check) -/

/-- The `p = 4` value `minAdm(![r,r,4]) = 4r − 4` for `r ≥ 2` (the binding stratum `t = r−2`, value
`(r−(r−2))² + (r−2)·4 = 4 + 4r − 8 = 4r − 4`). The `≤` is the `t = r−2` witness; the `≥` is the per-leaf
bound `4r−4 ≤ (r−t)²+4t` (`(s−2)² ≥ 0` with `s = r−t`), mirroring genm-n4's `rr4_term_ge`. -/
theorem minAdm_rr4_val_ge2 {r : ℕ} (hr : 2 ≤ r) :
    minAdm (![r, r, 4] : Fin 3 → ℕ) = 4 * r - 4 := by
  rw [minAdm_rrp_eq_inf]
  refine le_antisymm ?_ ?_
  · -- `≤`: the `t = r−2` stratum has value `(r−(r−2))² + (r−2)·4 = 4r − 4`.
    have hmem : (r - 2) ∈ Finset.range (r + 1) := by rw [Finset.mem_range]; omega
    refine le_trans (Finset.inf'_le _ hmem) ?_
    have h1 : r - (r - 2) = 2 := by omega
    rw [h1]; omega
  · -- `≥`: every stratum `(r−t)²+4t ≥ 4r−4` (`(s−2)² ≥ 0`, `s = r−t`).
    refine Finset.le_inf' _ _ (fun t ht => ?_)
    rw [Finset.mem_range] at ht
    -- write `r = t + s`; then `(r−t)²+4t = s² + 4(r−s)`... use the ℕ bound directly via `s = r−t`.
    obtain ⟨s, hs⟩ : ∃ s, r = t + s := ⟨r - t, by omega⟩
    subst hs
    rw [Nat.add_sub_cancel_left]
    -- `4(t+s) − 4 ≤ s·s + t·4`. Reduces to `4s ≤ s·s + 4` (the `(s−2)² ≥ 0` core, ℕ via `interval_cases`).
    have hcore : 4 * s ≤ s * s + 4 := by
      rcases Nat.lt_or_ge s 2 with h | h
      · interval_cases s <;> omega
      · obtain ⟨u, hu⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
        subst hu; ring_nf; omega
    omega

/-- `schurLambdaP 4 r = schurLambda r` — the ∀p witness specialises to the landed `p = 4` threshold (the
shape-pin: this IS genm-n4's `minAdm_rr4_eq`, reproved here on the base-independent `minAdm_rrp_eq_inf`).
`r = 0,1` are the `0, ½` leaves (`minAdm = 0, 4`); `r ≥ 2` both sides are `2r − 2`. -/
theorem schurLambdaP_four_eq (r : ℕ) : schurLambdaP 4 r = schurLambda r := by
  rcases Nat.lt_or_ge r 2 with hr | hr
  · interval_cases r
    · rw [schurLambdaP, schurLambda_zero]
      rw [show minAdm (![0, 0, 4] : Fin 3 → ℕ) = 0 by rw [minAdm_rrp_eq_inf]; norm_num]
      norm_num
    · rw [schurLambdaP, schurLambda_one]
      rw [show minAdm (![1, 1, 4] : Fin 3 → ℕ) = 1 by
        rw [minAdm_rrp_eq_inf]
        refine le_antisymm ?_ ?_
        · -- the `t = 0` stratum: `(1−0)²+0·4 = 1`.
          have hmem : (0 : ℕ) ∈ Finset.range (1 + 1) := by simp
          refine le_trans (Finset.inf'_le _ hmem) ?_
          norm_num
        · exact Finset.le_inf' _ _ (fun t ht => by
            rw [Finset.mem_range] at ht; interval_cases t <;> norm_num)]
      norm_num
  · rw [schurLambdaP, minAdm_rr4_val_ge2 hr, schurLambda_eq_of_ge_two hr]
    have h4 : (4 : ℕ) ≤ 4 * r := by omega
    rw [Nat.cast_sub h4]; push_cast; ring

end DLNFibre.DLN.RLCT

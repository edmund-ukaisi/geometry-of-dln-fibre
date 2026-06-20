import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.Case111Bridge

/-!
# `DLNFibre.DLN.RLCT.Validate.Case111` — smallest case end-to-end (validate-small-first GATE)

The first real end-to-end Lean result, for the trivial network `H = (1,1,1)`, `r = 0`, `B = 0`. Here
`dlnLoss (1,1,1) 0 A = (c₁·c₂)²` (the two layers are `1×1`, i.e. scalars `c₁ = A 0 0 0`,
`c₂ = A 1 0 0`) is **already** normal-crossing — no blow-up, no resolution, no `S1`/`L1`/`L2`/`D1`.
The loss is the weighted monomial `(∏|uⱼ|^{2·1})^{−c}` with density `∏|uⱼ|^0 = 1`, i.e. the monomial
data `k = (1,1)`, `h = (0,0)`, `d = 2`.

This is the anti-treadmill checkpoint: a sorry-free assembly that threads the monomial model the
resolution feeds (`monomialThreshold`) through the **one** permitted external citation
(`monomial_rlct`, S2) and lands on the closed form `aoyagiLambda (1,1,1) 0`. Both sides are `1/2`:

* the monomial threshold `min_j (0+1)/(2·1) = 1/2` (S2's threshold-half), and
* `aoyagiLambda (1,1,1) 0 = [−0²+0·(1+1)]/2 + ½·(Adm).inf' Mval = 0 + ½·1 = 1/2`.

## What is proven sorry-free, and where the line is drawn
* `dlnLoss_case111` — the **monomial-form coercion** of the loss (pure polynomial algebra; no
  citation).
* `case111_monomialThreshold` — `monomialThreshold 2 (1,1) (0,0) = ofReal (aoyagiLambda (1,1,1) 0)`,
  via the threshold-half of `monomial_rlct`. The honest end-to-end through the citation:
  `#print axioms` shows it depends on `monomial_rlct` (+ `propext`, `Classical.choice`,
  `Quot.sound`).

## The `rlctAt`-headline: stated, with one named bridge `sorry`
`rlctAt (dlnLoss (1,1,1) 0) deepest111 = ofReal (aoyagiLambda (1,1,1) 0)` is the headline shape
(`deepest111 = fun _ ↦ 0`, the deepest fibre point). It needs one bridge
`rlctAt H (dlnLoss …) wstar = monomialThreshold …`, which is **not** free even in this trivial case:
`rlctAt` integrates `|F|^{−c}` over a neighbourhood of `wstar` in `Params`, whereas
`monomialThreshold` integrates over the unit box `[0,1]^d` against `|uⱼ|`-symmetrised monomials.
Equating the two admissible-exponent down-sets is germ-locality + a box change-of-variables — the
**S1** content (`rlct_germ_local`, `rlct_unit_invariant`), not yet proven. We carry that single step
as the named `sorry` `case111_rlct_eq_monomialThreshold` rather than fold an unproven analytic
bridge silently into a sorry-free `rlctAt`-claim (precision: name a result for what it proves). The
headline `case111_rlct` is assembled from the bridge `sorry` + the sorry-free
`case111_monomialThreshold`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped ENNReal

/-- The deepest singular point of the `(1,1,1)`, `B = 0` fibre: both scalar layers `0`. (`Params` is
a `def`, so the Pi `Zero` is not synthesised under the bare `0` numeral; the witness is shown.) -/
def deepest111 : Params (![1, 1, 1] : Fin 3 → ℕ) := fun _ => 0

/-! ## The monomial-form coercion of the loss -/

/-- For `H = (1,1,1)`, `B = 0`: the loss is the bare monomial `(c₁·c₂)²` in the two scalar entries
`c₁ = A 0 0 0`, `c₂ = A 1 0 0` (the `1×1` layers). Pure polynomial algebra — no citation. This is
the form the weighted-monomial citation consumes (`k = (1,1)`, `h = (0,0)`). -/
theorem dlnLoss_case111 (A : Params (![1, 1, 1] : Fin 3 → ℕ)) :
    dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0 A
      = (A 0 (0 : Fin 1) (0 : Fin 1) * A 1 (0 : Fin 1) (0 : Fin 1)) ^ 2 := by
  -- `simp` reduces the layer product `prodAux` (clearing its recursive casts) to `1 * A 0 * A 1`;
  -- `erw` finishes the single-entry read, rewriting up to the defeq `Fin (H s) = Fin 1` widths.
  simp only [dlnLoss, prod]
  simp [prodAux]
  congr 1
  erw [Matrix.sub_apply, Matrix.zero_apply, sub_zero, Matrix.mul_apply, Fin.sum_univ_one,
    Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq, one_mul]

/-! ## The end-to-end through the one citation (sorry-free) -/

/-- The per-axis ratios for the `(1,1,1)` monomial data `k = (1,1)`, `h = (0,0)` all equal `1/2`, so
their infimum — the S2 threshold — is `1/2`. -/
theorem case111_axisRatio_inf :
    (⨅ j : Fin 2, axisRatio ((![0, 0] : Fin 2 → ℕ) j) ((![1, 1] : Fin 2 → ℕ) j))
      = (1 / 2 : ℝ≥0∞) := by
  have h : ∀ j : Fin 2,
      axisRatio ((![0, 0] : Fin 2 → ℕ) j) ((![1, 1] : Fin 2 → ℕ) j) = (1 / 2 : ℝ≥0∞) :=
    fun j => by fin_cases j <;> simp [axisRatio]
  simp [h]

/-- The closed form for the trivial network: `aoyagiLambda (1,1,1) 0 = 1/2` (regular shift `0`, core
`½·1`). Evaluated by kernel reduction. -/
theorem aoyagiLambda_case111 : aoyagiLambda (![1, 1, 1] : Fin 3 → ℕ) 0 = (1 / 2 : ℚ) := by
  decide +kernel

/-- `ENNReal.ofReal (aoyagiLambda (1,1,1) 0) = 1/2`. -/
theorem ofReal_aoyagiLambda_case111 :
    ENNReal.ofReal (aoyagiLambda (![1, 1, 1] : Fin 3 → ℕ) 0) = (1 / 2 : ℝ≥0∞) := by
  rw [aoyagiLambda_case111, show ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) by norm_num,
    ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- **The gate (sorry-free, AXIOM-FREE).** The monomial-model threshold the resolution feeds for the
trivial network equals the closed form: both are `1/2`. Now proven **without `monomial_rlct`** — the
threshold value comes from `monomialThreshold_case111` (Fubini + the Mathlib rpow integrability iff,
`Case111Bridge`), so `#print axioms` shows only standard axioms. The end-to-end assembly: monomial
data `(k,h) = ((1,1),(0,0))` ▸ `monomialThreshold = 1/2` (Mathlib) ▸ `aoyagiLambda = 1/2`. -/
theorem case111_monomialThreshold :
    monomialThreshold 2 (![1, 1] : Fin 2 → ℕ) (![0, 0] : Fin 2 → ℕ)
      = ENNReal.ofReal (aoyagiLambda (![1, 1, 1] : Fin 3 → ℕ) 0) := by
  rw [monomialThreshold_case111, ofReal_aoyagiLambda_case111]

/-! ## The `rlctAt`-headline (one named bridge `sorry`) -/

/-- The deepest point `deepest111` lies in `optimalSet` (`prod 0 = 0`, so the loss vanishes). -/
theorem deepest111_mem_optimalSet :
    deepest111 ∈ optimalSet (![1, 1, 1] : Fin 3 → ℕ) 0 := by
  have hz : dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0 deepest111 = 0 := by
    rw [dlnLoss_case111]; change ((0 : ℝ) * 0) ^ 2 = 0; ring
  rw [optimalSet_eq_loss_zero]; exact hz

/-- **Bridge `sorry` (the one remaining gap in the `(1,1,1)` headline — baby S1.1).** The local RLCT
of the already-normal-crossing loss at the deepest point equals the monomial-model threshold of its
`(k,h) = ((1,1),(0,0))` data. The RHS is now `1/2` **axiom-free** (`monomialThreshold_case111`,
`Case111Bridge`), so closing this `sorry` makes the whole headline axiom-free. The remaining content
is `rlctAt = 1/2` directly: `rlctAt` integrates `|F|^{−c'} = |c₁|^{−2c'}|c₂|^{−2c'}` over a
`Params`-neighbourhood of `0`, and its admissible-exponent set is again `{c' < 1/2}`. Three pieces
remain (all verified reachable, none an analytic wall — see thread 10):
(i) a measurable equiv `Params (1,1,1) ≃ᵐ (Fin 2 → ℝ)` (each `1×1` layer `≃ᵐ ℝ`) to transport the
volume to the box machinery; (ii) **two-sided** `|x|^{−2c'}` integrability on `[-ε,ε]` (the
neighbourhood crosses `0`, unlike the box `[0,1]`); (iii) the `∃ U ∈ 𝓝 0` quantifier — a box for
`c' < 1/2`, divergence over every neighbourhood for `c' ≥ 1/2`. This is the genuine baby-S1.1 build,
left as a named `sorry` rather than forced. -/
theorem case111_rlct_eq_monomialThreshold :
    rlctAt (![1, 1, 1] : Fin 3 → ℕ) (dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0) deepest111
      = monomialThreshold 2 (![1, 1] : Fin 2 → ℕ) (![0, 0] : Fin 2 → ℕ) := by
  sorry

/-- **The `(1,1,1)` headline.** The local RLCT of the deep-linear loss at the deepest point of the
`B = 0` fibre equals Aoyagi's closed form `aoyagiLambda (1,1,1) 0 = 1/2`. Assembled from the S1
bridge `case111_rlct_eq_monomialThreshold` (the one named `sorry`) and the sorry-free
`case111_monomialThreshold` (the S2 end-to-end). -/
theorem case111_rlct :
    rlctAt (![1, 1, 1] : Fin 3 → ℕ) (dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0) deepest111
      = ENNReal.ofReal (aoyagiLambda (![1, 1, 1] : Fin 3 → ℕ) 0) := by
  rw [case111_rlct_eq_monomialThreshold, case111_monomialThreshold]

end DLNFibre.DLN.RLCT

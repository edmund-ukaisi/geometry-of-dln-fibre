import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.Case222Rlct
import DLNFibre.DLN.RLCT.Validate.Case212

/-!
# `DLNFibre.DLN.RLCT.Validate.RRR` — the reduced-rank-regression (`L = 2`) model

Aoyagi Theorem 1 (the reduced-rank-regression / three-layer benchmark; Aoyagi–Watanabe 2005,
ref. [12]) is **Theorem 2 specialised to `L = 2`** — two composable matrices `A⁽¹⁾A⁽²⁾`, widths
`H⁽¹⁾, H⁽²⁾, H⁽³⁾`, reduced widths `M⁽ˢ⁾ = H⁽ˢ⁾ − r`. The closed form is identical to the general
one once `(ℓ, a, M̃, 𝓜)` are fixed (`theory/aoyagi-2023-worked.tex` §5; the
`Thm-1 expression − Thm-2 expression|_{L+1=3} = 0` identity, `verify-arith-groundtruth.md` Check 4).

**General-`L`-first (operator design constraint, 2026-06-23).** RRR is the **`L = 2` instance** of
the existing general-`L` API (`aoyagiLambda`, `aoyagi_learning_coefficient`), *not* a parallel
RRR-first API. So `rrrLambda H r := aoyagiLambda H r` (`L = 2`, `Fin 3 → ℕ`), and `aoyagi_rrr` is
literally `aoyagi_learning_coefficient (L := 2)`. The closed-form regime split (balanced `ℓ = 2` vs
dominated `ℓ = 1`) of §5 is the cross-check ground truth, **not** the data model — it does not shape
the API.

## What is proven vs. what is honest-`sorry` (proof-state honesty)

- **`aoyagi_rrr` (the headline value, `L = 2`)** is the genuine instance of the general headline, so
  it is **sorry-conditional exactly as the general headline is** — its proof carries no new `sorry`,
  but inherits transitively the two named open obligations of the general assembly: the gauge-slice
  normal form `deepest_regular_core_normal_form` (#44) and the fibre-monotonicity
  `rlctAt_deepest_le_of_optimal` (D1≥). No claim is made beyond the general theorem.
- **`aoyagi_rrr_222` / `aoyagi_rrr_212`** are **fully sorry-free** concrete `L = 2` anchors at the
  deepest point of the `B = 0` fibre — re-exports of `case222_rlct` / `case212_rlct` cast against
  `rrrLambda`. They show the machinery reaches a *proven* RLCT value at `L = 2`: `(2,2,2) → 3/2`
  (rests on the single cited S2 axiom `monomial_rlct`) and `(2,1,2) → 1` (S2-free, axiom-clean).
- **The order `θ` (`rrrTheta`)** — the combinatorial value `a(ℓ − a) + 1` is landed **sorry-free**
  (the `L = 2` instance of `aoyagiTheta`, on given selector data). The **analytic binding** (that
  this value is `monomialOrderAnalytic` of the RRR loss) is **NOT stated** — it is the flagged open
  seam (controller decision): the `L = 2` selector `(ℓ, a)` of `def:Mset-L2` is not yet a Lean def,
  and nothing binds `monomialOrderAnalytic` to `aoyagiTheta` at `L = 2`. See the `θ`-section note.

This file itself is **sorry-free**; the only open obligations it touches are the two general
headline sorries that `aoyagi_rrr` inherits transitively (above), and the un-stated order seam.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal

/-! ## The RRR learning coefficient: the `L = 2` instance of `aoyagiLambda` -/

/-- **RRR learning coefficient (`L = 2`).** The `L = 2` specialisation of the general-`L` closed
form `aoyagiLambda`: `ρ_r + ½·min_T M(T)` on the three reduced widths `M⁽ˢ⁾ = H⁽ˢ⁾ − r`, with
`ρ_r = [−r² + r(H⁽¹⁾ + H⁽³⁾)]/2` the Theorem-3 regular prefactor. **Not** a parallel API — it is
defeq to `aoyagiLambda H r` (general-`L`-first). Faithful to Aoyagi Theorem 1 (`§5`): reproduces
the balanced (`ℓ = 2`) and dominated (`ℓ = 1`) regimes; ground truth `(2,2,2) → 3/2`, `(2,1,2) → 1`,
`(1,1,3) → 1/2` is the `#eval` cross-check below. -/
def rrrLambda (H : Fin 3 → ℕ) (r : ℕ) : ℚ := aoyagiLambda H r

/-- `rrrLambda` is definitionally `aoyagiLambda` (the general-`L`-first identity, made explicit). -/
theorem rrrLambda_eq (H : Fin 3 → ℕ) (r : ℕ) : rrrLambda H r = aoyagiLambda H r := rfl

-- RRR ground-truth cross-check (`§5`, `verify-arith-groundtruth.md`; enforced at build time).
/-- info: 3 / 2 -/
#guard_msgs in
#eval rrrLambda (![2, 2, 2] : Fin 3 → ℕ) 0   -- balanced, ℓ=2, a=2
/-- info: 1 -/
#guard_msgs in
#eval rrrLambda (![2, 1, 2] : Fin 3 → ℕ) 0   -- balanced, ℓ=2, a=1
/-- info: 1 / 2 -/
#guard_msgs in
#eval rrrLambda (![1, 1, 3] : Fin 3 → ℕ) 0   -- dominated, ℓ=1 (drop M⁽³⁾): ½·M⁽¹⁾M⁽²⁾ = ½
/-- info: 4 -/
#guard_msgs in
#eval rrrLambda (![3, 3, 4] : Fin 3 → ℕ) 0   -- coupled core, min_T Mval = 8 → ½·8 = 4

/-! ## `aoyagi_rrr` — the headline value as the `L = 2` instance of the general theorem

This is `aoyagi_learning_coefficient` at `L := 2`. It is **sorry-conditional** to exactly the degree
the general headline is (the two named open obligations of the general assembly), and carries no new
`sorry` of its own. -/

/-- **Aoyagi Theorem 1 (RRR), value form — the `L = 2` instance of the headline.** The global
learning coefficient (the infimum of the local RLCT over the fibre `mult⁻¹(B)`) of the three-layer
deep-linear square-Frobenius loss equals Aoyagi's RRR closed form `rrrLambda H r`, for any rank-`r`
target `B` with every width `≥ r`. Literally `aoyagi_learning_coefficient (L := 2)` — the
general-`L`-first instance, *not* a parallel proof. **Proof-state:** inherits the general headline's
two named open obligations transitively (`deepest_regular_core_normal_form`,
`rlctAt_deepest_le_of_optimal`); no new `sorry`. -/
theorem aoyagi_rrr (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (rrrLambda H r) :=
  aoyagi_learning_coefficient (L := 2) H r B hB hr (by norm_num)

/-! ## Concrete sorry-free `L = 2` anchors (the machinery reaches a proven value)

These are the fully-discharged endpoints: the local RLCT at the deepest point of the `B = 0` fibre,
for two concrete `L = 2` width vectors, equal to `rrrLambda`. They are re-exports of the validated
`case222`/`case212` anchors, recast against `rrrLambda` (no new mathematics). They demonstrate the
deliverable's "as far as the machinery reaches": the RRR value is *proven* (not merely assembled) at
these vectors. -/

/-- **RRR sorry-free anchor `(2,2,2)`.** The local RLCT of the three-layer `(2,2,2)` loss at the
deepest point of the `B = 0` fibre equals `rrrLambda (2,2,2) 0 = 3/2`. Sorry-free; rests on the
single cited S2 axiom `monomial_rlct` (the `≤`-bound) per `case222_rlct`. -/
theorem aoyagi_rrr_222 :
    rlctAt H222 (dlnLoss H222 0) deepest222 = ENNReal.ofReal (rrrLambda H222 0) := by
  rw [case222_rlct, rrrLambda]
  -- aoyagiLambda (2,2,2) 0 = 3/2 (by kernel), so ofReal of its ℝ-cast is the literal 3/2
  have h : aoyagiLambda H222 0 = (3 / 2 : ℚ) := by
    rw [show H222 = (![2, 2, 2] : Fin 3 → ℕ) from by funext i; fin_cases i <;> rfl]
    decide +kernel
  rw [h, show ((3 / 2 : ℚ) : ℝ) = (3 / 2 : ℝ) from by norm_num]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- **RRR sorry-free anchor `(2,1,2)`.** The local RLCT of the three-layer `(2,1,2)` loss at the
deepest point of the `B = 0` fibre equals `rrrLambda (2,1,2) 0 = 1`. Sorry-free and **axiom-clean**
(S2-free) per `case212_rlct`. -/
theorem aoyagi_rrr_212 :
    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
      = ENNReal.ofReal (rrrLambda (![2, 1, 2] : Fin 3 → ℕ) 0) := by
  rw [case212_rlct, rrrLambda]

/-! ## The order `θ` for RRR — the combinatorial value (sorry-free); analytic binding is a SEAM

The RRR order is `θ = a(ℓ − a) + 1` (`aoyagiTheta ℓ a`) with `(ℓ, a)` from the `L = 2` selector
`def:Mset-L2`. The **combinatorial value** `rrrTheta` is landed sorry-free below (the `L = 2`
instance of `aoyagiTheta`, on *given* selector data). The **analytic binding** — that this value is
the analytic pole order `monomialOrderAnalytic` of the RRR loss — is **NOT** stated here, and is the
flagged open seam (controller decision; expedition discuss-at-close item 2). Two pieces are missing,
both upstream:

1. **No `L = 2` selector in Lean.** `def:Mset-L2`'s `(ℓ, a)` (the four-way balanced/dominated split)
   is not defined; only `aoyagiTheta ℓ a` (which takes `(ℓ, a)` as *given* data) exists. A faithful
   `rrrTheta` from `(H, r)` alone would need that selector — itself underspecified at ties (`§5`,
   ledger (F-1)), so even the input data is not yet a clean Lean primitive.
2. **No analytic-order binding.** Nothing equates `monomialOrderAnalytic` of the RRR loss to
   `aoyagiTheta` at `L = 2`. The general `aoyagiTheta_eq` is itself a weak existential `sorry` whose
   conclusion does not even reference the widths (free-choice-provable, capturing nothing), so it is
   **not** mirrored here; the S2 order-conjunct (`monomial_rlct.2`) pins only
   `monomialOrderAnalytic = monomialOrder` on a chart, not the chart-count `= a(ℓ − a) + 1`.

So this file states the combinatorial `rrrTheta` and stops; the loss-to-`aoyagiTheta` binding waits
on the selector def + the chart-count identity (the order-half blocker). -/

/-- **RRR order (`L = 2`), on given selector data.** The `L = 2` instance of `aoyagiTheta`. Takes
the selector `(ℓ, a)` of `def:Mset-L2` as input (the `L = 2` selector itself is not yet a Lean def —
see the section note). Ground truth: `(2,2,2) → θ = 1` (`ℓ=2, a=2`), `(2,1,2) → θ = 2` (`ℓ=2, a=1`),
`(1,1,3) → θ = 1` (`ℓ=1, a=1`). -/
def rrrTheta (ℓ a : ℕ) : ℕ := aoyagiTheta ℓ a

/-- info: 1 -/
#guard_msgs in
#eval rrrTheta 2 2   -- (2,2,2): θ = 2·0 + 1 = 1
/-- info: 2 -/
#guard_msgs in
#eval rrrTheta 2 1   -- (2,1,2): θ = 1·1 + 1 = 2
/-- info: 1 -/
#guard_msgs in
#eval rrrTheta 1 1   -- (1,1,3) dominated: θ = 1·0 + 1 = 1

end DLNFibre.DLN.RLCT

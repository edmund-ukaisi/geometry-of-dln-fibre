import DLNFibre.Core.Aoyagi.ProductResolution
import DLNFibre.Core.CThetaQIPConverse
import DLNFibre.Core.QSeriesExtraction
import Meta.Cordon

/-!
# `Core.Aoyagi.Engine` — Object D (the combinatorial bridge) + the abstract engine value

**BLUEPRINT (v3).** The Core-native combinatorial bridge from the resolution's divisor-exponent
minimum — a **min over the atlas of charts** (Object B) — to the QIP minimum `qipMin` and thence
`cCodim` (via the banked `cCodim_eq_qipMin`, `Core.CThetaQIPConverse:833`), and the abstract assembly
`2·rlct = cCodim`. `Core` never imports `DLN`.

## The soundness fix (v2 defect 4): `divisor_spec` is min-attainment, not exact set-equality

Aoyagi's minimisation (worked.tex:529–542, Lemma 3) identifies the terminal candidates and their
MINIMUM, not the whole spectrum. The obligation the value needs is **min-attainment across the
atlas**: every binding divisor of every chart is `≥ qipMin` (no undershoot, `hlb`), and some binding
divisor of some chart attains it (`hattain`). That is exactly enough to prove `res.divisorMin =
qipMin` (`Finset.inf'` — a min over charts of a min over binding axes — bounded below and attained).

## The bridge is PROVED (no leaf here)

`Resolution.divisorMin_eq_cCodim` is a full proof: `le_antisymm` on the nested `Finset.inf'` from the
two min-attainment facts, `cCodim_eq_qipMin` for `qipMin = cCodim`, `cCodim_nonneg` for the `toNat`
cast. The only frontier upstream of `two_mul_rlctAt_eq_cCodim` is Object B's min-over-charts CoV leaf,
the per-chart value leaf, and the min-attainment obligation (discharged by the existence theorem).
-/

open MeasureTheory Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {N : ℕ}

/-! ## Object D — the divisor-min (over the atlas) ↔ `qipMin` ↔ `cCodim` bridge (PROVED) -/

/-- **Object D (the combinatorial bridge, PROVED).** If, across the atlas, every binding divisor
exponent `jac c a + 1` is `≥ qipMin d` (`hlb`) and some binding divisor of some chart attains
`qipMin d` (`hattain`) — the min-attainment form (v2 defect 4 fix) — then the resolution's
divisor minimum (a min over charts of a min over binding axes) equals `(cCodim d 0).toNat`:
`res.divisorMin = qipMin d = cCodim d 0`. Uses only `Finset.inf'` order facts, the banked QIP
equality `cCodim_eq_qipMin`, and `cCodim_nonneg`. Core-native, no `DLN`. -/
theorem Resolution.divisorMin_eq_cCodim {D M : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ}
    (res : Resolution F (0 : Fin D → ℝ)) (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) (hq : (qipFeasible d).Nonempty)
    (hlb : ∀ (c : Fin res.numCharts) (a : Fin D),
      a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
      qipMin d hq ≤ ((res.charts c).jac a + 1 : ℤ))
    (hattain : ∃ (c : Fin res.numCharts) (a : Fin D),
      a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
      ((res.charts c).jac a + 1 : ℤ) = qipMin d hq) :
    res.divisorMin = ((cCodim d 0 h).toNat : ℝ) := by
  have hqc : qipMin d hq = cCodim d 0 h := (cCodim_eq_qipMin d hd h hq).symm
  have hcc0 : 0 ≤ cCodim d 0 h := cCodim_nonneg h
  have htn : ((cCodim d 0 h).toNat : ℤ) = cCodim d 0 h := Int.toNat_of_nonneg hcc0
  have hcast : ((cCodim d 0 h).toNat : ℝ) = ((qipMin d hq : ℤ) : ℝ) := by
    rw [hqc]; exact_mod_cast htn
  rw [hcast, Resolution.divisorMin]
  apply le_antisymm
  · -- ≤ : some chart's binding divisor attains `qipMin`.
    obtain ⟨c, a, ha, hae⟩ := hattain
    refine (Finset.inf'_le _ (Finset.mem_univ c)).trans ?_
    show (res.charts c).chartMin ≤ _
    rw [Chart.chartMin]
    refine (Finset.inf'_le _ ha).trans ?_
    have : ((res.charts c).jac a + 1 : ℝ) = ((qipMin d hq : ℤ) : ℝ) := by exact_mod_cast hae
    exact le_of_eq this
  · -- ≥ : every chart's every binding divisor is `≥ qipMin`.
    refine Finset.le_inf' _ _ (fun c _ ↦ ?_)
    rw [Chart.chartMin]
    refine Finset.le_inf' _ _ (fun a ha ↦ ?_)
    have hle := hlb c a ha
    have : ((qipMin d hq : ℤ) : ℝ) ≤ ((res.charts c).jac a + 1 : ℝ) := by exact_mod_cast hle
    exact this

/-! ## The abstract engine value `2·rlct = cCodim` (WIRED from Object B + Object D) -/

/-- **The abstract engine value.** For a certified resolution atlas `res` of `∑ Fᵢ²` at the origin
whose binding divisors satisfy the min-attainment against `qipMin d`, `2·rlctAt (∑ Fᵢ²) 0 = cCodim
d 0`: Object B's `2·rlct = divisorMin` (min over charts) composed with Object D's bridge
`divisorMin = cCodim`. This is the `rlct_core = ½·cCodim` value the corollary consumes. -/
@[blueprint]
theorem Resolution.two_mul_rlctAt_eq_cCodim {D M : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ}
    (res : Resolution F (0 : Fin D → ℝ)) (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) (hq : (qipFeasible d).Nonempty)
    (hlb : ∀ (c : Fin res.numCharts) (a : Fin D),
      a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
      qipMin d hq ≤ ((res.charts c).jac a + 1 : ℤ))
    (hattain : ∃ (c : Fin res.numCharts) (a : Fin D),
      a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
      ((res.charts c).jac a + 1 : ℤ) = qipMin d hq) :
    2 * rlctAt (sumSqFam F) 0 = ((cCodim d 0 h).toNat : ℝ) := by
  rw [res.two_mul_rlctAt_eq_divisorMin,
    res.divisorMin_eq_cCodim d hd h hq hlb hattain]

end DLNFibre.Core.Aoyagi

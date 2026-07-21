import DLNFibre.Core.Aoyagi.ProductResolution
import DLNFibre.Core.CThetaQIPConverse
import DLNFibre.Core.QSeriesExtraction
import Meta.Cordon

/-!
# `Core.Aoyagi.Engine` — Object D (the combinatorial bridge) + the abstract engine value

**BLUEPRINT (v3).** The Core-native combinatorial bridge from the resolution's divisor-exponent
minimum to the QIP minimum `qipMin` and thence `cCodim` (via the banked `cCodim_eq_qipMin`,
`Core.CThetaQIPConverse:833`), and the abstract assembly `2·rlct = cCodim` for a certified
resolution. `Core` never imports `DLN` — this module stays network-free.

## The soundness fix (v2 defect 4): `divisor_spec` is min-attainment, not exact set-equality

v2 asserted `{jacⱼ+1} = {Gqip d e}` (an exact image). Aoyagi's minimisation (worked.tex:529–542,
Lemma 3) identifies the terminal candidates and their MINIMUM, not the whole spectrum. The honest
obligation the value needs is **min-attainment**: every binding divisor's exponent is `≥` the QIP
minimum (no undershoot), and some binding divisor attains it. That is `hdiv_lb` + `hdiv_attain`
below, and it is exactly enough to prove `min divisor exponent = qipMin` (`Finset.inf'` bounded below
and attained).

## The bridge is PROVED (no leaf here)

`divisorMin_eq_cCodim` is a full proof: `le_antisymm` on `Finset.inf'` from the two min-attainment
facts, `cCodim_eq_qipMin` for `qipMin = cCodim`, and `cCodim_nonneg` for the `toNat` cast. The only
frontier upstream of `two_mul_rlctAt_eq_cCodim` is Object B's CoV leaf and the min-attainment
obligation (discharged by the existence theorem in the DLN application).
-/

open MeasureTheory Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {N : ℕ}

/-! ## Object D — the divisor-min ↔ `qipMin` ↔ `cCodim` bridge (PROVED) -/

/-- **Object D (the combinatorial bridge, PROVED).** If, over the binding axes, every divisor
exponent `jac d + 1` is `≥ qipMin d` and some binding divisor attains `qipMin d` (the min-attainment
form — v2 defect 4 fix), then the divisor-exponent minimum equals `(cCodim d 0).toNat`:
`⨅ binding (jac d + 1) = qipMin d = cCodim d 0`. Uses only `Finset.inf'` order facts, the banked QIP
equality `cCodim_eq_qipMin`, and `cCodim_nonneg` (for the `toNat` cast). Core-native, no `DLN`. -/
theorem divisorMin_eq_cCodim (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty)
    {D : ℕ} {kexp jac : Fin D → ℕ} (hbind : (bindingAxes kexp).Nonempty)
    (hdiv_lb : ∀ a ∈ bindingAxes kexp, qipMin d hne ≤ (jac a + 1 : ℤ))
    (hdiv_attain : ∃ a ∈ bindingAxes kexp, (jac a + 1 : ℤ) = qipMin d hne) :
    (bindingAxes kexp).inf' hbind (fun a ↦ (jac a + 1 : ℝ)) = ((cCodim d 0 h).toNat : ℝ) := by
  -- `qipMin = cCodim` (banked QIP); `cCodim ≥ 0` gives `(cCodim.toNat : ℝ) = (cCodim : ℝ)`.
  have hqc : qipMin d hne = cCodim d 0 h := (cCodim_eq_qipMin d hd h hne).symm
  have hcc0 : 0 ≤ cCodim d 0 h := cCodim_nonneg h
  have htn : ((cCodim d 0 h).toNat : ℤ) = cCodim d 0 h := Int.toNat_of_nonneg hcc0
  have hcast : ((cCodim d 0 h).toNat : ℝ) = ((qipMin d hne : ℤ) : ℝ) := by
    rw [hqc]; exact_mod_cast htn
  rw [hcast]
  -- `inf' = (qipMin : ℝ)` by antisymmetry: lower bound (`hdiv_lb`) + attainment (`hdiv_attain`).
  apply le_antisymm
  · obtain ⟨a, ha, hae⟩ := hdiv_attain
    refine (Finset.inf'_le _ ha).trans ?_
    have : ((jac a + 1 : ℤ) : ℝ) = ((qipMin d hne : ℤ) : ℝ) := by rw [hae]
    push_cast at this ⊢; linarith
  · refine Finset.le_inf' _ _ (fun a ha ↦ ?_)
    have := hdiv_lb a ha
    have hcast2 : ((qipMin d hne : ℤ) : ℝ) ≤ ((jac a + 1 : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at hcast2 ⊢; linarith

/-! ## The abstract engine value `2·rlct = cCodim` (WIRED from Object B + Object D) -/

/-- **The abstract engine value.** For a certified resolution `res` of `∑ Fᵢ²` at the origin whose
binding divisors satisfy the min-attainment against `qipMin d`, `2·rlctAt (∑ Fᵢ²) 0 = cCodim d 0`:
Object B's integer form `2·rlct = ⨅ binding (jac d + 1)` composed with Object D's bridge
`⨅ = cCodim`. This is the `rlct_core = ½·cCodim` value the corollary consumes, with the resolution's
existence and the min-attainment as the only obligations. -/
@[blueprint]
theorem Resolution.two_mul_rlctAt_eq_cCodim {D M : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ}
    (res : Resolution F 0) (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty)
    (hdiv_lb : ∀ a ∈ bindingAxes (res.bexp res.k₀), qipMin d hne ≤ (res.jac a + 1 : ℤ))
    (hdiv_attain : ∃ a ∈ bindingAxes (res.bexp res.k₀), (res.jac a + 1 : ℤ) = qipMin d hne) :
    2 * rlctAt (sumSqFam F) 0 = ((cCodim d 0 h).toNat : ℝ) := by
  rw [res.two_mul_rlctAt_eq_min,
    divisorMin_eq_cCodim d hd h hne res.hbind hdiv_lb hdiv_attain]

end DLNFibre.Core.Aoyagi

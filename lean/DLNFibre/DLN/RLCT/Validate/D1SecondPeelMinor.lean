import DLNFibre.DLN.RLCT.Validate.D1SecondPeelChart
import DLNFibre.DLN.RLCT.Validate.D1HChartRank

/-!
# `DLNFibre.DLN.RLCT.Validate.D1SecondPeelMinor` — the SECOND-peel minor `hminor₂` from a rank bound

The genuinely-new analytic content of the L = 2 D1 `≥`-leg de-risk: discharge the second-peel
selected-minor non-degeneracy `hminor₂` (consumed by `secondPeel_hchart_residual`) from a RANK LOWER
BOUND on the residual vector's Jacobian, structurally identical to how the FIRST peel's `hminor`
discharges from `nReg ≤ rank(jacFlatL2)` (`exists_jacFlatL2_minor`).

## The construction (network-free, the `exists_jacFlatL2_minor` analog)

For a `C¹` (here `C²`) residual vector `h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)`, the **Jacobian
matrix** `jacResid h t0 : Matrix (Fin n) (Fin N) ℝ` has `(i, c)` entry the `c`-th directional
derivative of the `i`-th component at `t0`:

    jacResid h t0 i c = (fderiv ℝ (fun t => h t i) t0) (Pi.single c 1).

The `hminor₂` shape `secondPeel_hchart_residual` consumes is exactly the det of the `(eh, ec)`
submatrix of this Jacobian (`jacResid_submatrix_eq`). So a rank bound `extra ≤ (jacResid h t0).rank`
+ the banked determinantal engine `exists_minor_of_le_rank` produce injective `eh, ec` with that det
`≠ 0` — i.e. `hminor₂`, EXISTENTIALLY (`exists_secondPeel_minor`).

## The honest scope (what stays a NAMED-OPEN gate)

The rank lower bound `extra ≤ (jacResid h t0).rank` itself — i.e. that the slice residual carries
`extra = extraCount m a b` first-order regular directions — is the middle-stratum first-differential
fact (verify-first STEP-0 verdict: BOUNDED, the SAME gauge-fixed linear injection as the first peel,
with the middle-stratum layer ranks `(r+a, r+b)` replacing the deepest `(r, r)`; the dimension count
`(r+a)·H0 + (r+b)·H2 − (r+a)(r+b) − nReg = extraCount`, sympy-exact). Tying it to the BUMP-GLOBALISED
first-peel residual `q (0,·)` at its basepoint requires unwinding the IFT chart `Ψsymm` + split
homeomorph + bump — NOT built here. So this module lands the rank-bound ⟹ `hminor₂` BRICK (the
determinantal reuse), leaving the rank bound as a named hypothesis the eventual chart-unwind supplies.

Network-free, generic over a `C¹` residual vector. No DLN/#44/#120 dependency.
-/

open Matrix Module
namespace DLNFibre.DLN.RLCT

section SecondPeelMinor

variable {N n : ℕ}

/-- **The residual Jacobian matrix** `jacResid h t0 : Matrix (Fin n) (Fin N) ℝ`: the `(i, c)` entry is
the `c`-th partial derivative of the `i`-th component of `h` at `t0` (`fderiv` of the scalar component
`fun t => h t i`, applied to the `c`-th coordinate tangent `Pi.single c 1`). -/
noncomputable def jacResid (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)) (t0 : Fin N → ℝ) :
    Matrix (Fin n) (Fin N) ℝ :=
  Matrix.of (fun i c => (fderiv ℝ (fun t => h t i) t0) (Pi.single c 1))

/-- The `(i, c)` entry of `jacResid` unfolds to the component-derivative form. -/
@[simp] theorem jacResid_apply (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)) (t0 : Fin N → ℝ)
    (i : Fin n) (c : Fin N) :
    jacResid h t0 i c = (fderiv ℝ (fun t => h t i) t0) (Pi.single c 1) := rfl

/-- **The `(eh, ec)` submatrix of `jacResid` is the `hminor₂` matrix** consumed by
`secondPeel_hchart_residual`: `(jacResid h t0).submatrix eh ec = Matrix.of (fun k k' => fderiv (h ·
(eh k)) t0 (single (ec k') 1))`. A definitional bridge between the two minor encodings. -/
theorem jacResid_submatrix_eq {extra : ℕ} (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (t0 : Fin N → ℝ) (eh : Fin extra → Fin n) (ec : Fin extra → Fin N) :
    (jacResid h t0).submatrix eh ec
      = Matrix.of (fun k k' : Fin extra =>
          (fderiv ℝ (fun t => h t (eh k)) t0) (Pi.single (ec k') 1)) := by
  ext k k'
  simp only [Matrix.submatrix_apply, jacResid_apply, Matrix.of_apply]

/-- **The second-peel minor exists, from a rank bound** (the `exists_jacFlatL2_minor` analog). Given
`extra ≤ (jacResid h t0).rank`, there are injective selectors `eh : Fin extra → Fin n` (components)
and `ec : Fin extra → Fin N` (coordinates) with the `extra × extra` Jacobian minor invertible — the
EXACT `hminor₂` shape `secondPeel_hchart_residual` consumes. Wraps the banked determinantal engine
`exists_minor_of_le_rank` and rewrites the minor through `jacResid_submatrix_eq`. -/
theorem exists_secondPeel_minor {extra : ℕ} (h : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n))
    (t0 : Fin N → ℝ) (hrank : extra ≤ (jacResid h t0).rank) :
    ∃ (eh : Fin extra → Fin n) (ec : Fin extra → Fin N),
      Function.Injective eh ∧ Function.Injective ec ∧
      (Matrix.of (fun k k' : Fin extra =>
        (fderiv ℝ (fun t => h t (eh k)) t0) (Pi.single (ec k') 1))).det ≠ 0 := by
  obtain ⟨eh, ec, heh, hec, hdet⟩ := exists_minor_of_le_rank (jacResid h t0) hrank
  exact ⟨eh, ec, heh, hec, by rwa [jacResid_submatrix_eq] at hdet⟩

end SecondPeelMinor

end DLNFibre.DLN.RLCT

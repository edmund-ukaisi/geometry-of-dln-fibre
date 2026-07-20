/-
Conditional smoothness plumbing: a presentation whose chosen square sub-Jacobian is a unit is smooth.

For a field `k`, `n` variables and `c` relations `v : Fin c → MvPolynomial (Fin n) k`, and an injective
column-selector `a : Fin c → Fin n` choosing which `c` of the `n` variables the square sub-Jacobian
differentiates by, the chart algebra `S = MvPolynomial (Fin n) k ⧸ (span (range v))` is smooth as soon as
the `c × c` minor determinant `det (i j ↦ pderiv (a i) (v j))` is a UNIT in `S`. Sharper: `S` is standard
smooth of relative dimension `n - c`.

This is a reusable building block. The minor-unit hypothesis IS the single field `jacobian_isUnit` of
`Algebra.SubmersivePresentation`; we do NOT discharge it here (that is the rank lemma, a separate tide).
Callers whose chart is a localization `S_g ≃ₐ[k] (this quotient)` transport the conclusions along the
iso via `Algebra.Smooth.of_equiv` / `IsStandardSmoothOfRelativeDimension.of_algEquiv`.

The route is reducedness-free: `SubmersivePresentation` carries no `Reduced`/`Flat`/`Noetherian`/`IsDomain`
hypothesis, and `IsStandardSmooth ⟹ Smooth` is side-condition-free.
-/
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Extension.Presentation.Submersive

open Algebra MvPolynomial

namespace DLNFibre.Core

noncomputable section

variable {k : Type*} [Field k] {n c : ℕ}

/-- The chart algebra `MvPolynomial (Fin n) k ⧸ (span (range v))` for the relation family `v`. -/
abbrev ChartAlg (v : Fin c → MvPolynomial (Fin n) k) : Type _ :=
  MvPolynomial (Fin n) k ⧸ (Ideal.span (Set.range v))

/-- The naive pre-submersive presentation of the chart algebra: `n` variables, `c` relations `v`,
with the injective `a : Fin c → Fin n` selecting the `c` columns of the square sub-Jacobian. -/
def chartPreSubmersive (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) :
    PreSubmersivePresentation k (ChartAlg v) (Fin n) (Fin c) :=
  PreSubmersivePresentation.naive (R := k) (σ := Fin n) (ι := Fin c) (v := v) a ha

/-- The `c × c` sub-Jacobian determinant of the relations `v` along the chosen variables `a`,
viewed in the chart algebra: exactly the Jacobian of the naive pre-submersive presentation. -/
def subJacobian (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) : ChartAlg v :=
  (chartPreSubmersive v a ha).jacobian

/-- The caller-facing closed form of the minor-unit hypothesis: `subJacobian` is the image, under
the quotient map `MvPolynomial (Fin n) k ↠ ChartAlg v`, of the `c × c` minor determinant
`det (i j ↦ pderiv (a i) (v j))`. -/
theorem subJacobian_eq (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) :
    subJacobian v a ha =
      Ideal.Quotient.mk (Ideal.span (Set.range v))
        (Matrix.det (fun i j : Fin c ↦ MvPolynomial.pderiv (a i) (v j))) := by
  have hmat : (chartPreSubmersive v a ha).jacobiMatrix
      = (fun i j : Fin c ↦ MvPolynomial.pderiv (a i) (v j)) := by
    ext i j; rw [chartPreSubmersive, PreSubmersivePresentation.jacobiMatrix_naive]
  rw [subJacobian, PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hmat]
  rfl

/-- The submersive presentation built from the relations `v`, the column-selector `a`, and the
minor-unit hypothesis. Its `dimension` is `n - c`. -/
def chartSubmersive (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) (hunit : IsUnit (subJacobian v a ha)) :
    SubmersivePresentation k (ChartAlg v) (Fin n) (Fin c) where
  __ := chartPreSubmersive v a ha
  jacobian_isUnit := hunit

/-- **Conditional smoothness** (the headline): if the chosen square sub-Jacobian of the relations
is a unit in the chart algebra, the chart is `Smooth k`. The hypothesis `hunit` is the minor-unit
hypothesis; it is NOT discharged here. -/
theorem isSmooth_chart_of_isUnit_subJacobian (v : Fin c → MvPolynomial (Fin n) k)
    (a : Fin c → Fin n) (ha : Function.Injective a) (hunit : IsUnit (subJacobian v a ha)) :
    Smooth k (ChartAlg v) :=
  have : IsStandardSmooth k (ChartAlg v) := (chartSubmersive v a ha hunit).isStandardSmooth
  inferInstance

/-- **Sharper:** standard smooth of the right relative dimension `n - c`. -/
theorem isStandardSmoothOfRelativeDimension_chart_of_isUnit_subJacobian
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n) (ha : Function.Injective a)
    (hunit : IsUnit (subJacobian v a ha)) :
    IsStandardSmoothOfRelativeDimension (n - c) k (ChartAlg v) :=
  (chartSubmersive v a ha hunit).isStandardSmoothOfRelativeDimension <| by
    show (chartSubmersive v a ha hunit).toPresentation.dimension = n - c
    simp [Presentation.dimension]

/-! ### Transport to a chart algebra presented up to isomorphism

The downstream fibre-smoothness atlas does not meet `ChartAlg v` on the nose: each chart is a
localization `S` together with an iso `e : ChartAlg v ≃ₐ[k] S`. These wrappers move the conclusions
across `e`; the minor-unit hypothesis is stated in `S` as `IsUnit (e (subJacobian v a ha))`. -/

variable {S : Type*} [CommRing S] [Algebra k S]

/-- `Smooth k S` for a chart `S` presented up to a `k`-algebra iso from `ChartAlg v`, given the
transported sub-Jacobian is a unit in `S`. -/
theorem isSmooth_of_algEquiv_chart_of_isUnit_subJacobian
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n) (ha : Function.Injective a)
    (e : ChartAlg v ≃ₐ[k] S) (hunit : IsUnit (e (subJacobian v a ha))) :
    Smooth k S :=
  have : Smooth k (ChartAlg v) :=
    isSmooth_chart_of_isUnit_subJacobian v a ha (by
      simpa using hunit.map (e.symm : S →+* ChartAlg v))
  Smooth.of_equiv e

/-- `IsStandardSmoothOfRelativeDimension (n - c) k S` for a chart `S` presented up to a `k`-algebra
iso from `ChartAlg v`, given the transported sub-Jacobian is a unit in `S`. -/
theorem isStandardSmoothOfRelativeDimension_of_algEquiv_chart_of_isUnit_subJacobian
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n) (ha : Function.Injective a)
    (e : ChartAlg v ≃ₐ[k] S) (hunit : IsUnit (e (subJacobian v a ha))) :
    IsStandardSmoothOfRelativeDimension (n - c) k S :=
  have : IsStandardSmoothOfRelativeDimension (n - c) k (ChartAlg v) :=
    isStandardSmoothOfRelativeDimension_chart_of_isUnit_subJacobian v a ha (by
      simpa using hunit.map (e.symm : S →+* ChartAlg v))
  IsStandardSmoothOfRelativeDimension.of_algEquiv (n := n - c) e

/-! ### Non-vacuity witness

The minor-unit hypothesis is genuinely satisfiable on a non-trivial chart: with one variable and the
single relation `x = 0`, the `1 × 1` minor is `pderiv x x = 1`, a unit. The chart is `k[x]/(x) ≅ k`,
standard smooth of relative dimension `1 - 1 = 0`. This shows the headlines are not vacuous. -/
example {k : Type*} [Field k] :
    IsUnit (subJacobian (k := k) (n := 1) (c := 1) (fun _ ↦ X 0) (fun _ ↦ 0)
      (Function.injective_of_subsingleton _)) := by
  rw [subJacobian_eq]
  simp [Matrix.det_unique, pderiv_X]

end

end DLNFibre.Core

**Recommendation**
Use a precise hybrid: land the concrete quotient lemma, plus a thin `AlgEquiv` wrapper for chart algebras. Do not make the primary API abstract over arbitrary `Presentation`.

The key reason: the reusable work is matching the concrete `c × c` determinant with Mathlib’s `PreSubmersivePresentation.naive` Jacobian and getting `dimension = n - c`; once a `SubmersivePresentation` exists, Mathlib already supplies the abstract theorem.

**Recommended Signatures**
Known at this pin: `Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv` exists, and `Algebra.Smooth.of_equiv` exists. I did not find/verify a `Smooth.of_algEquiv` name.

```lean
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Extension.Presentation.Submersive

namespace DLNFibre.Core

noncomputable section

variable {k : Type*} [CommRing k] {n c : ℕ}

abbrev ChartAlg (v : Fin c → MvPolynomial (Fin n) k) : Type _ :=
  MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range v)

def subJacobian (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n) :
    ChartAlg v :=
  algebraMap (MvPolynomial (Fin n) k) (ChartAlg v)
    (((fun i j : Fin c => MvPolynomial.pderiv (a i) (v j)) :
      Matrix (Fin c) (Fin c) (MvPolynomial (Fin n) k)).det)

def chartPreSubmersive
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) :
    Algebra.PreSubmersivePresentation k (ChartAlg v) (Fin n) (Fin c) :=
  sorry

theorem chartPreSubmersive_jacobian
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) :
    (chartPreSubmersive v a ha).jacobian = subJacobian v a :=
  sorry

def chartSubmersive
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) (hJ : IsUnit (subJacobian v a)) :
    Algebra.SubmersivePresentation k (ChartAlg v) (Fin n) (Fin c) :=
  sorry

theorem isStandardSmoothOfRelativeDimension_chartAlg_of_isUnit_subJacobian
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) (hJ : IsUnit (subJacobian v a)) :
    Algebra.IsStandardSmoothOfRelativeDimension (n - c) k (ChartAlg v) :=
  sorry

theorem smooth_chartAlg_of_isUnit_subJacobian
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) (hJ : IsUnit (subJacobian v a)) :
    Algebra.Smooth k (ChartAlg v) :=
  sorry

theorem isStandardSmoothOfRelativeDimension_of_algEquiv_chartAlg_of_isUnit_subJacobian
    {S : Type*} [CommRing S] [Algebra k S]
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) (e : ChartAlg v ≃ₐ[k] S)
    (hJ : IsUnit (e (subJacobian v a))) :
    Algebra.IsStandardSmoothOfRelativeDimension (n - c) k S :=
  sorry

theorem smooth_of_algEquiv_chartAlg_of_isUnit_subJacobian
    {S : Type*} [CommRing S] [Algebra k S]
    (v : Fin c → MvPolynomial (Fin n) k) (a : Fin c → Fin n)
    (ha : Function.Injective a) (e : ChartAlg v ≃ₐ[k] S)
    (hJ : IsUnit (e (subJacobian v a))) :
    Algebra.Smooth k S :=
  sorry

end

end DLNFibre.Core
```

**Indexing Trap**
For `naive`, call it with `(σ := Fin n) (ι := Fin c)`. Its output is indexed as generators `Fin n`, relations `Fin c`:

```lean
Algebra.PreSubmersivePresentation k (ChartAlg v) (Fin n) (Fin c)
```

Then `Presentation.dimension = Nat.card (Fin n) - Nat.card (Fin c) = n - c`. Reversing these gives `c - n`.

**Silent Failure Points**
Do not define `subJacobian` using `naive ... a sorry`; make it the concrete determinant in the quotient ring. Also, the unit hypothesis must live in the chart ring: either `IsUnit (subJacobian v a)` for `ChartAlg v`, or `IsUnit (e (subJacobian v a))` after transport to `S`.

`ha : Function.Injective a` is essential; if `c > n`, this hypothesis is impossible, while `n - c` is truncated Nat subtraction. For `Fin` indices, `Finite`/`Fintype`/`DecidableEq` are fine; for future arbitrary indices, add those assumptions explicitly.
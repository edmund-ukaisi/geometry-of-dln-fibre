**Base Assignment**

Use `IsLocalization.tensorProduct_tensorProduct`, not `IsLocalization.Away.tensor`.

| Lemma | Mathlib symbol | Assignment |
|---|---|---|
| polynomial tensor iso | `MvPolynomial.algebraTensorAlgEquiv R A` | `R = k`, `A = F`, `σ = SchurVar q p r` |
| localization base change | `IsLocalization.tensorProduct_tensorProduct` | `R = k`, `A = P := MvPolynomial ι k`, `M = Submonoid.powers f`, `B = Sf := Localization.Away f`, `S = F` |
| final comparison | `IsLocalization.algEquivOfAlgEquiv` | base scalar `k`, source base `PF := MvPolynomial ι F`, target base `P ⊗[k] F` |

Here `f := detSchurS q p r`, `g := MvPolynomial.map (algebraMap k F) f`.

**Recommended Chain**

1. Build
   `e : PF ≃ₐ[k] P ⊗[k] F`
   from `(MvPolynomial.algebraTensorAlgEquiv k F).symm`, restrict scalars from `F` to `k`, then compose with `Algebra.TensorProduct.comm k F P`.

2. Prove
   `e g = algebraMap P (P ⊗[k] F) f`
   using `MvPolynomial.algebraTensorAlgEquiv_symm_map`.

3. Supply
   `IsLocalization (Submonoid.powers (algebraMap P (P ⊗[k] F) f)) (Sf ⊗[k] F)`
   from `IsLocalization.tensorProduct_tensorProduct`.

4. Use `Submonoid.map_powers` and step 2 to produce the submonoid equality for `IsLocalization.algEquivOfAlgEquiv`.

5. Finish with
   `IsLocalization.algEquivOfAlgEquiv (Localization.Away g) (Sf ⊗[k] F) e H`.

**Lean Skeleton**

```lean
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Away.Basic

open scoped TensorProduct

namespace DLNFibre.Core

universe u v

variable {k : Type u} [Field k]

noncomputable def mvPolynomialAwayMapTensorAlgEquiv
    {F : Type v} [CommRing F] [Algebra k F]
    {ι : Type*} (f : MvPolynomial ι k) :
    Localization.Away (MvPolynomial.map (algebraMap k F) f)
      ≃ₐ[k] Localization.Away f ⊗[k] F := by
  let P : Type _ := MvPolynomial ι k
  let PF : Type _ := MvPolynomial ι F
  let g : PF := MvPolynomial.map (algebraMap k F) f
  let Sf : Type _ := Localization.Away f

  let eF : PF ≃ₐ[F] F ⊗[k] P :=
    (MvPolynomial.algebraTensorAlgEquiv k F).symm
  let e : PF ≃ₐ[k] P ⊗[k] F :=
    (eF.restrictScalars k).trans (Algebra.TensorProduct.comm k F P)

  have heg : e g = algebraMap P (P ⊗[k] F) f := by
    change (Algebra.TensorProduct.comm k F P)
        ((MvPolynomial.algebraTensorAlgEquiv k F).symm
          (MvPolynomial.map (algebraMap k F) f))
      = algebraMap P (P ⊗[k] F) f
    rw [MvPolynomial.algebraTensorAlgEquiv_symm_map]
    simp

  haveI hlocTarget : IsLocalization
      (Submonoid.powers (algebraMap P (P ⊗[k] F) f))
      (Sf ⊗[k] F) := by
    simpa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (IsLocalization.tensorProduct_tensorProduct
        (R := k) (A := P) (S := F)
        (M := Submonoid.powers f) (B := Sf))

  have H : Submonoid.map (e : PF →+* P ⊗[k] F) (Submonoid.powers g)
      = Submonoid.powers (algebraMap P (P ⊗[k] F) f) := by
    rw [Submonoid.map_powers, heg]

  simpa [g, Sf] using
    (IsLocalization.algEquivOfAlgEquiv
      (Localization.Away g) (Sf ⊗[k] F) e H)

noncomputable def detSchurSAwayBaseChangeAlgEquiv
    (q p r : ℕ) {F : Type v} [CommRing F] [Algebra k F] :
    Localization.Away
        (MvPolynomial.map (algebraMap k F) (detSchurS (k := k) q p r))
      ≃ₐ[k] SchurLoc (k := k) q p r ⊗[k] F :=
  mvPolynomialAwayMapTensorAlgEquiv
    (F := F) (ι := SchurVar q p r) (detSchurS (k := k) q p r)

end DLNFibre.Core
```

For the concrete fibre ring:

```lean
noncomputable def chartGfibBaseChangeAlgEquiv
    {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Localization.Away (chartGfib k d r hp hq)
      ≃ₐ[k]
    SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
      ⊗[k] sweepFibreRing k d r hp hq := by
  simpa [chartGfib] using
    (detSchurSAwayBaseChangeAlgEquiv (k := k)
      (d 0) (d (Fin.last (N + 1))) r
      (F := sweepFibreRing k d r hp hq))
```

**Pitfalls**

`IsLocalization.Away.tensor` is the wrong first tool if you set `R = k`: `detSchurS` is not in `k`. If you set `R = P`, it gives a localization of something like `SchurLoc ⊗[P] PF`, which then needs an extra tensor reassociation/cancellation argument.

The target tensor product is not literally declared as `Localization.Away`; it is a generic `IsLocalization` obtained from `IsLocalization.tensorProduct_tensorProduct`. That is exactly what `IsLocalization.algEquivOfAlgEquiv` wants.

The only likely v4.29 friction is the line with `Algebra.algebraMapSubmonoid`. If `simpa [Algebra.algebraMapSubmonoid, Submonoid.map_powers]` does not close, keep the target instance at the `Algebra.algebraMapSubmonoid` shape and make `H` target that shape instead.

`algebraTensorAlgEquiv` is `F`-linear, not directly `k`-linear. Use `.restrictScalars k` before composing with `Algebra.TensorProduct.comm`.

No `detSchurS_ne_zero` is needed for the equivalence. It only matters for nontriviality/domain consequences.
import DLNFibre.Core.OrbitPullbackDim
import DLNFibre.Core.PolynomialDimension
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Integral

/-!
# `DLNFibre.Core.AffineNoetherRank` — A4.1: `ringKrullDim = trdeg` for the pullback image

Route-c second link: for the finitely-generated `k`-domain `Aimg = (orbitPullback M).range`,
its Krull dimension equals its transcendence degree over `k`:

> `(ringKrullDim (orbitPullback M).range).unbotD 0 = (Algebra.trdeg k (orbitPullback M).range).toNat`.

Both equal the **Noether-normalization rank** `s` of the kernel `ker μ_M^*`: the landed Noether engine
`ringKrullDim_quotient_eq_noetherRank` produces an integral injective `k[Fin s] →ₐ (R ⧸ p)` with
`ringKrullDim (R ⧸ p) = s`, and that same integral injective map forces `trdeg = s` (the quotient is
algebraic over the polynomial subring, so `trdeg_add_eq` + `MvPolynomial.trdeg_of_isDomain` +
`trdeg_eq_zero` collapse to `s`). The image `Aimg` is `k`-algebra isomorphic to `R ⧸ ker` (first iso,
landed as `quotientKerEquivRangeOrbitPullback`), with the coordinate index reindexed `RepCoord d ≃ Fin n`
(`renameEquiv`), so both invariants transport (`ringKrullDim_eq_of_ringEquiv`, `AlgEquiv.trdeg_eq`).

Char-free: no algebraic closure, no `CharZero` (the Noether engine and `trdeg` API are char-free).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Algebra

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The general trdeg-of-Noether-rank bridge -/

/-- An integral injective `k`-algebra map from a polynomial ring `k[Fin s]` into a `k`-domain `B`
forces `trdeg k B = s`: `B` is algebraic over the image of `k[Fin s]`, so by tower additivity
`trdeg_add_eq` the degree splits as `trdeg_k k[Fin s] + trdeg_{k[Fin s]} B = s + 0`. -/
theorem trdeg_eq_of_integral_injective {s : ℕ} {B : Type u} [CommRing B] [IsDomain B] [Algebra k B]
    (g : MvPolynomial (Fin s) k →ₐ[k] B) (hinj : Function.Injective g) (hint : g.IsIntegral) :
    Algebra.trdeg k B = (s : Cardinal) := by
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr hinj
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) B :=
    (Algebra.isIntegral_def).mpr (fun b ↦ hint b)
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) B := inferInstance
  have h : Algebra.trdeg k (MvPolynomial (Fin s) k) + Algebra.trdeg (MvPolynomial (Fin s) k) B
      = Algebra.trdeg k B := trdeg_add_eq k (MvPolynomial (Fin s) k)
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero, Cardinal.mk_fin,
    Cardinal.lift_natCast] at h
  exact h.symm

/-- **The dimension-equals-trdeg bridge for an f.g. domain quotient.** For a prime `p` of
`R = k[Fin n]`, the Krull dimension of `R ⧸ p` and its transcendence degree over `k` both equal the
Noether-normalization rank `s`, hence agree: `(ringKrullDim (R ⧸ p)).unbotD 0 = (trdeg k (R ⧸ p)).toNat`.
The Noether engine (`ringKrullDim_quotient_eq_noetherRank`) supplies the integral injective
`k[Fin s] →ₐ (R ⧸ p)` and `ringKrullDim = s`; `trdeg_eq_of_integral_injective` gives `trdeg = s`. -/
theorem ringKrullDim_quotient_unbotD_eq_trdeg_toNat (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (ringKrullDim (MvPolynomial (Fin n) k ⧸ p)).unbotD 0
      = (Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ p)).toNat := by
  obtain ⟨s, _, ⟨g, hg_inj, hg_int⟩, hdim⟩ := ringKrullDim_quotient_eq_noetherRank k n p
  have htr : Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ p) = (s : Cardinal) :=
    trdeg_eq_of_integral_injective g hg_inj hg_int
  rw [hdim, htr, Cardinal.toNat_natCast]
  rfl

/-! ## Transport to the orbit-pullback image -/

/-- **A4.1 headline.** For the pullback image `Aimg = (orbitPullback M).range`, a finitely-generated
`k`-domain, the Krull dimension equals the transcendence degree:
`(ringKrullDim (orbitPullback M).range).unbotD 0 = (Algebra.trdeg k (orbitPullback M).range).toNat`.
The first iso (`quotientKerEquivRangeOrbitPullback`) presents `Aimg` as `R_RepCoord ⧸ ker`; the
coordinate index is reindexed `RepCoord d ≃ Fin n` (`renameEquiv`), carrying `ker` to a prime `p` of
`k[Fin n]`; then `ringKrullDim_quotient_unbotD_eq_trdeg_toNat` applies, transported back through
`ringKrullDim_eq_of_ringEquiv` and `AlgEquiv.trdeg_eq`. Char-free. -/
theorem ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    (ringKrullDim (orbitPullback M).range).unbotD 0
      = (Algebra.trdeg k (orbitPullback M).range).toNat := by
  -- reindex `RepCoord d ≃ Fin n` (it is `Finite`)
  letI : Fintype (RepCoord d) := Fintype.ofFinite _
  set n := Fintype.card (RepCoord d) with hn
  let e : RepCoord d ≃ Fin n := Fintype.equivFin _
  -- the renaming algebra-iso and the image prime `p`
  let R := renameEquiv k e
  let Rr : MvPolynomial (RepCoord d) k ≃+* MvPolynomial (Fin n) k := R.toRingEquiv
  set ker := RingHom.ker (orbitPullback M).toRingHom with hker
  haveI : ker.IsPrime := RingHom.ker_isPrime (orbitPullback M).toRingHom
  set p : Ideal (MvPolynomial (Fin n) k) := ker.map (Rr : _ →+* _) with hp
  haveI : p.IsPrime := by
    rw [hp, Ideal.map_comap_of_equiv Rr]
    infer_instance
  -- `R_RepCoord ⧸ ker ≃ₐ[k] R_Fin ⧸ p`
  let Φ : (MvPolynomial (RepCoord d) k ⧸ ker) ≃ₐ[k] (MvPolynomial (Fin n) k ⧸ p) :=
    Ideal.quotientEquivAlg ker p R rfl
  -- chain: `Aimg ≃ₐ R_RepCoord ⧸ ker ≃ₐ R_Fin ⧸ p`
  let Ψ : (orbitPullback M).range ≃ₐ[k] (MvPolynomial (Fin n) k ⧸ p) :=
    (quotientKerEquivRangeOrbitPullback M).symm.trans Φ
  rw [ringKrullDim_eq_of_ringEquiv Ψ.toRingEquiv, AlgEquiv.trdeg_eq Ψ,
    ringKrullDim_quotient_unbotD_eq_trdeg_toNat n p]

end DLNFibre.Core

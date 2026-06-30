import DLNFibre.Core.OrbitPullbackDim
import DLNFibre.Core.PolynomialDimension
import DLNFibre.Core.Dimension.Localization

/-!
# `DLNFibre.Core.AffineNoetherRank` — A4.1: `ringKrullDim = trdeg` for the pullback image

Route-c second link: for the finitely-generated `k`-domain `Aimg = (orbitPullback M).range`,
its Krull dimension equals its transcendence degree over `k`:

> `(ringKrullDim (orbitPullback M).range).unbotD 0`
> ` = (Algebra.trdeg k (orbitPullback M).range).toNat`.

This is the **orbit specialisation** of the general affine-dimension fact. The two char-free engine
bricks now live one layer down, in the dimension stack: `Dimension.trdeg_eq_of_integral_injective`
(integral injective `⟹ trdeg = s`, beside the `dim`-invariance twin in `Dimension.Integral`) and
`Dimension.ringKrullDim_quotient_unbotD_eq_trdeg_toNat` (the `dim = trdeg` quotient form, derived
from the general f.g.-domain `Dimension.ringKrullDim_eq_trdeg_of_fg_domain`, in
`Dimension.Localization`).
Here we only transport that quotient form along the orbit isomorphism: the image `Aimg` is
`k`-algebra isomorphic to `R ⧸ ker` (first iso, landed as `quotientKerEquivRangeOrbitPullback`),
with the coordinate index reindexed `RepCoord d ≃ Fin n` (`renameEquiv`), so both invariants
transport (`ringKrullDim_eq_of_ringEquiv`, `AlgEquiv.trdeg_eq`).

Char-free: no algebraic closure, no `CharZero` (the dimension engine and `trdeg` API are char-free).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Algebra DLNFibre.Core.Dimension

universe u

variable {k : Type u} [Field k] {N : ℕ}

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

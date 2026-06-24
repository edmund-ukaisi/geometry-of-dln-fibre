import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.DeterminantalStratumDim
import DLNFibre.Core.FibreCodim
import DLNFibre.Core.FibreHeightDirect
import DLNFibre.Core.AffineDomainDimension
import DLNFibre.Core.OrbitTangentCotangent

/-!
# `DLNFibre.Core.FibreDimFibration` — the fibre-dimension count toward Lemma 4.6 (H4)

Rung **H4** of the HEIGHT-DIRECT route to Lehalleur–Rimányi Lemma 4.6's geometry: the dimension of
the multiplication-map fibre `mult⁻¹(E)` over a rank-`r` normal form `E`, via the fibration
`mult|_{Σ̄^r} : Σ̄^r ↠ Mat^{≤r}` (dominant) and the generic-fibre-dimension count

> `codimRepCanonical (mult⁻¹ E) = C + δ`,   `C = cCodim d r`,  `δ = r(d_0 + d_N − r)`.

This module banks the **base-stratum dimension brick** the count consumes, and the **easy
inequality** `codimRepCanonical (fibre E) ≤ C + δ` (the flatness-free half), proved via the no-
going-down height inequality (Stacks 00OM) — see the per-theorem docstrings. The **hard inequality**
`codimRepCanonical (fibre E) ≥ C + δ` is the genuine no-jump residual (it needs that `E` lies in the
exact-rank good locus where the fibre dimension does not jump — generic flatness / generic
smoothness, with the going-down equality `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
requiring `Algebra.HasGoingDown ⟸` flatness, which `mult` lacks globally since the fibre dimension
jumps as the rank drops). It is **NOT** proved here and is named honestly as such; nothing in this
module claims the full identity.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k]

/-! ## The base-stratum Krull dimension brick: `ringKrullDim O(Mat^{≤r}) = δ`

The base of the fibration is the rank-`≤ r` determinantal variety in the target matrices
`Mat_{m × n}` (`n = d_0`, `m = d_N`), encoded as the `N = 1` product-rank locus
`productRankLocusLE (dStratum n m) r`. Its coordinate ring `O(Mat^{≤r}) = MvPolynomial (RepCoord
(dStratum n m)) k ⧸ vanishingIdeal(…)` is a finite-type domain (the vanishing ideal is prime —
irreducible determinantal variety) of Krull dimension `δ = r(n + m − r)`. From the LANDED thermometer
`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
nontrivial, so `ringKrullDim ≠ ⊥`). -/

/-- **The base-stratum Krull dimension** `ringKrullDim O(Mat^{≤r}) = δ`. For `r ≤ n`, `r ≤ m`, over an
algebraically closed field of characteristic `0`, the coordinate ring of the rank-`≤ r` determinantal
variety `Mat^{≤r}_{m × n}` (the `N = 1` product-rank locus) has Krull dimension `r(n + m − r) = δ`.
The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
it to the genuine `WithBot ℕ∞` Krull dimension, using that the vanishing ideal is prime (the quotient
is a nontrivial domain, so `ringKrullDim ≠ ⊥`). -/
theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
    (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
    ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸
        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r))
      = (r * (n + m - r) : ℕ) := by
  set I := MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
    (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r) with hI
  haveI hIp : I.IsPrime :=
    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
      productRankLocusLE (k := k) (dStratum n m) r) = (r * (n + m - r) : ℕ) :=
    varietyDim_productRankLocusLE_stratum n m r hn hm
  rw [varietyDim, ← hI] at hvd
  -- the quotient is a nontrivial domain, so `ringKrullDim ≠ ⊥`.
  haveI : Nontrivial (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hIp.ne_top
  have hne : ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) ≠ ⊥ :=
    fun h ↦ by simpa [h] using
      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (RepCoord (dStratum n m)) k ⧸ I)
  obtain ⟨w, hw⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hw, WithBot.unbotD_coe] at hvd
  rw [← hw, hvd]
  norm_cast

/-! ## The base-stratum closed-point height: `height m = δ` for any maximal ideal of `O(Mat^{≤r})`

By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
`Fintype`-indexed) and the base Krull dimension `= δ` just established: every maximal ideal of the
irreducible base `O(Mat^{≤r})` has height `δ`. The base-side input to the going-down/00OM easy
direction. -/

/-- **The base-stratum closed-point height `= δ`.** For `r ≤ n`, `r ≤ m`, every maximal ideal `𝔪` of
the base coordinate ring `O(Mat^{≤r}_{m×n}) = MvPolynomial (RepCoord (dStratum n m)) k ⧸
vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
irreducible determinantal base, with `ringKrullDim O(Mat^{≤r}) = δ`. -/
theorem height_maximal_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
    (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m)
    (𝔪 : Ideal (MvPolynomial (RepCoord (dStratum n m)) k ⧸
        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)))
    [𝔪.IsMaximal] :
    (𝔪.height : WithBot ℕ∞) = (r * (n + m - r) : ℕ) := by
  haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
      (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)).IsPrime :=
    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
  rw [height_eq_ringKrullDim_of_isMaximal_fintype,
    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]

/-! ## Affine-domain equidimensionality over a `Fintype` coordinate index

`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
`MvPolynomial σ k` (`σ` finite) through `renameEquiv`, exactly as
`height_eq_ringKrullDim_of_isMaximal_fintype` does for the maximal corollary. This is the engine the
nested catenary `height P = height Q + height_{R/Q}(P/Q)` (the `+C` composition for the easy
direction) is built from. -/

/-- **Affine-domain equidimensionality, finite index.** For `σ` finite, `I` a prime of
`MvPolynomial σ k`, the domain `A = MvPolynomial σ k ⧸ I`, and a prime `p` of `A`:
`height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Transports
`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
algebra equivalences. -/
theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (p : Ideal (MvPolynomial σ k ⧸ I)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial σ k ⧸ I) ⧸ p)
      = ringKrullDim (MvPolynomial σ k ⧸ I) := by
  classical
  haveI : Fintype σ := Fintype.ofFinite _
  set e : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin (Fintype.card σ)) k :=
    MvPolynomial.renameEquiv k (Fintype.equivFin σ) with he
  set J : Ideal (MvPolynomial (Fin (Fintype.card σ)) k) := I.map (e : _ →+* _) with hJ
  haveI : J.IsPrime := by rw [hJ]; exact Ideal.map_isPrime_of_equiv e
  -- the induced quotient algebra equivalence `A ≃ₐ[k] A'`
  set Φ : (MvPolynomial σ k ⧸ I) ≃ₐ[k] (MvPolynomial (Fin (Fintype.card σ)) k ⧸ J) :=
    Ideal.quotientEquivAlg I J e rfl with hΦ
  -- transport `p` to a prime `p'` of `A'`
  set p' : Ideal (MvPolynomial (Fin (Fintype.card σ)) k ⧸ J) := p.map (Φ : _ →+* _) with hp'
  haveI : p'.IsPrime := by rw [hp']; exact Ideal.map_isPrime_of_equiv Φ
  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
  -- transport the three terms back along `Φ` (heights, both quotient Krull dims) and `e`.
  rw [hp', height_map_algEquiv Φ p,
    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
  exact hL

end DLNFibre.Core

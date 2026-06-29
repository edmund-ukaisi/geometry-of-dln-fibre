import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.DeterminantalStratumDim
import DLNFibre.Core.FibreCodim
import DLNFibre.Core.FibreHeightDirect
import DLNFibre.Core.DeepChartRing
import DLNFibre.Core.Dimension.AffineDomain
import DLNFibre.Core.AffineNoetherRank
import DLNFibre.Core.Dimension.Smooth

/-!
# `DLNFibre.Core.FibreDimFibrationProbe` — SPECIFY-stage contracts for H4

Un-aggregated probe pinning the exact engine signatures the H4 fibre-dimension count consumes, plus
the candidate-statement shapes. NOT aggregated; throwaway durable contract artefact in the
`FlatTrivialProductProbe`/`ChartFlatnessProbe` tradition. Zero sorry — every `example` is a compiling
contract.

**Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal Dimension

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Pinned engine handles (contracts) -/

/-- LANDED: `codim Σ̄^r = C` (ℕ∞ form). -/
example [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    codimRepCanonical (productRankLocusLE (k := k) d r) = ((cCodim d r h).toNat : ℕ∞) :=
  codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h

/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
example [IsAlgClosed k] [CharZero k] (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
      = (r * (n + m - r) : ℕ) :=
  varietyDim_productRankLocusLE_stratum n m r hn hm

/-- LANDED: H1 retarget — `codim(fibre B) = height(fibreGenIdeal B)`. -/
example [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height :=
  codimRepCanonical_fibre_eq_height_fibreGenIdeal d B

/-- LANDED: the one-sided lower bound `codim Σ̄^r ≤ codim(fibre B)` (so `codim(fibre B) ≥ C`). -/
example (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ}
    (hB : B.rank = r) :
    codimRepCanonical (productRankLocusLE (k := k) d r) ≤ codimRepCanonical (fibre d B) :=
  codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre B hB

/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
example [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (Z : Set (Tuple (k := k) d))
    (hp : (vanishingIdeal k (canonicalCoord d '' Z) :
      Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
  codimRepCanonical_eq_card_sub_varietyDim Z hp

/-- LANDED: affine-domain equidimensionality (NO flatness) — `height p + dim(A/p) = dim A`. -/
example (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (p : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
  affine_domain_height_add_ringKrullDim_quotient_eq k n I p

/-- LANDED: equidim at a closed point — `height m = dim A` for `m` maximal. -/
example (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (m : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
  height_eq_ringKrullDim_of_isMaximal k n I m

/-- LANDED (Mathlib, NO going-down): the inequality height-additivity (Stacks 00OM). The EASY
direction lever for `codim ≤ C+δ`. -/
example {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    P.height ≤ p.height + (P.map (Ideal.Quotient.mk <| p.map (algebraMap R S))).height :=
  Ideal.height_le_height_add_of_liesOver p P

/-- The base `Mat^{≤r}` over the target `Mat_{d_N × d_0}` is `productRankLocusLE (dStratum (d 0)
(d last N)) r` — its vanishing ideal is PRIME (irreducible determinantal variety), so the domain
machinery applies. -/
example [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hq : r ≤ d 0) (hp : r ≤ d (Fin.last N)) :
    (vanishingIdeal k (canonicalCoord (dStratum (d 0) (d (Fin.last N))) ''
        productRankLocusLE (k := k) (dStratum (d 0) (d (Fin.last N))) r) :
      Ideal (MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k)).IsPrime :=
  isPrime_vanishingIdeal_productRankLocusLE_stratum (d 0) (d (Fin.last N)) r hq hp

/-! ## Candidate: the base ringKrullDim = δ (the brick the going-down/00OM route consumes)

`ringKrullDim (O(Mat^{≤r})) = δ` over `[IsAlgClosed][CharZero]`, where `O(Mat^{≤r}) =
MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
unfolds to exactly `(ringKrullDim (… ⧸ vanishingIdeal …)).unbotD 0`, plus the quotient is nontrivial
(prime ideal) so the dim is not `⊥`. -/

/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
example (Z : Set (RepCoord (dStratum 2 2) → k)) :
    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
      MvPolynomial.vanishingIdeal (K := k) k Z)).unbotD 0 := rfl

end DLNFibre.Core

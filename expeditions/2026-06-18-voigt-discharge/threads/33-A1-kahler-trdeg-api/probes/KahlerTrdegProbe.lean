import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
Scratch probe (NOT part of the library): pin which trdeg / Kähler / dimension
bricks exist at Mathlib v4.29 by forcing them to typecheck.
-/

open Algebra

-- ===== Item 2: trdeg API (PRESENT) =====
section Trdeg
variable (R A A' S : Type*) [CommRing R] [CommRing A] [CommRing A'] [CommRing S]
  [Algebra R A] [Algebra R A'] [Algebra R S] [Algebra S A] [IsScalarTower R S A]

-- trdeg is a Cardinal
#check (Algebra.trdeg R A : Cardinal)
-- finite for finite-type over a domain (root namespace)
#check @trdeg_lt_aleph0
-- monotone under inj / surj alg homs (root namespace)
#check @trdeg_le_of_injective
#check @trdeg_le_of_surjective
-- equiv invariance
#check @AlgEquiv.trdeg_eq
-- tower additivity (domain, root namespace)
#check @trdeg_add_eq
-- trdeg of mvPolynomial over a domain = #ι
#check @MvPolynomial.trdeg_of_isDomain
-- transcendence basis API
#check @IsTranscendenceBasis
#check @exists_isTranscendenceBasis
#check @IsTranscendenceBasis.cardinalMk_eq_trdeg
end Trdeg

-- ===== Item 3: Kähler differentials (Ω of poly ring free; finite for ess-finite-type) =====
section Kahler
variable (R : Type*) [CommRing R] (σ : Type*)
-- Ω of a polynomial ring is free with basis {dx_i}
#check @KaehlerDifferential.mvPolynomialBasis
-- Ω is module-finite for ess-finite-type
#check @KaehlerDifferential.finite
end Kahler

-- ===== Item 5: AlgHom first-iso (PRESENT) =====
section FirstIso
variable (R M P : Type*) [CommRing R] [CommRing M] [CommRing P] [Algebra R M] [Algebra R P]
#check @RingCon.quotientKerEquivRangeₐ
end FirstIso

-- ===== Item 1 / 4: the ABSENT bricks — these SHOULD fail to typecheck =====
-- ringKrullDim A = trdeg k A  : no such lemma name exists (probe by guessing)
-- (Left commented; confirmed absent by grep — no file mentions both krullDim and trdeg.)

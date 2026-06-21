/-
Height under a flat, quasi-finite-at-a-prime algebra.

If `S` is a flat `R`-algebra (both Noetherian) and `S` is `R`-quasi-finite at a prime `Q`,
then `Q` and the prime `Q.under R` it lies over have the same height: the fibre over
`Q.under R` contributes nothing because quasi-finiteness forces `Q` to be minimal in that fibre.

This is the height-preservation brick of the étale route to "smooth ⟹ regular": étale ⟹ flat +
quasi-finite, so heights are preserved along an étale map, reducing `ringKrullDim` of a local ring
to the dimension of an affine-space base.

`Algebra.QuasiFiniteAt R Q` here is Mathlib's finite-fibre-dimension condition
(`κ(p) ⊗ S` finite over `κ(p)`), which is *weaker* than the Stacks 00PL "finite type + isolated in
its fibre" notion — the two coincide for finite-type `S`. The result holds in this weaker generality.
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalStructure

open Algebra

namespace DLNFibre.Core

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The image of `Q` in the fibre `S ⧸ (Q.under R)S` has height `0` when `S` is `R`-quasi-finite
at `Q`: any prime below it pulls back to a prime of `S` with the same contraction to `R`, hence
equal to `Q` by quasi-finiteness. -/
theorem fibre_height_eq_zero_of_quasiFiniteAt (Q : Ideal S) [Q.IsPrime]
    [Algebra.QuasiFiniteAt R Q] :
    (Q.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S)))).height = 0 := by
  -- Abbreviations: `pS = (Q.under R) S`, `f = quotient map onto the fibre`.
  set pS : Ideal S := (Q.under R).map (algebraMap R S) with hpS
  set f : S →+* S ⧸ pS := Ideal.Quotient.mk pS with hf
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hkerf : RingHom.ker f = pS := Ideal.mk_ker
  -- `comap f ⊥ = pS` (the kernel of the quotient map), in usable form.
  have hbot : (⊥ : Ideal (S ⧸ pS)).comap f = pS := by
    rw [← RingHom.ker_eq_comap_bot]; exact hkerf
  -- `pS ≤ Q`, since `Q` lies over `Q.under R`.
  have hpSQ : pS ≤ Q := hpS.trans_le Ideal.map_comap_le
  -- `J := Q.map f` is prime and pulls back to `Q`.
  have hJprime : (Q.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (hkerf.trans_le hpSQ)
  have hJcomap : (Q.map f).comap f = Q := by
    rw [Ideal.comap_map_of_surjective f hsurj, hbot, sup_eq_left.mpr hpSQ]
  -- height = primeHeight = 0 ⟺ minimal prime.
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff]
  refine ⟨⟨hJprime, bot_le⟩, ?_⟩
  -- Minimality: any prime `K ≤ J` equals `J`.
  rintro K ⟨hKprime, -⟩ hKJ
  -- `K' := K.comap f`, with `pS ≤ K' ≤ Q`.
  have hK'prime : (K.comap f).IsPrime := hKprime.comap f
  have hpSK' : pS ≤ K.comap f := (le_of_eq hkerf.symm).trans (Ideal.ker_le_comap f)
  have hK'Q : K.comap f ≤ Q := by rw [← hJcomap]; exact Ideal.comap_mono hKJ
  -- `K'.under R = Q.under R`: both equal `Q.under R`.
  have hunder : (K.comap f).under R = Q.under R := by
    refine le_antisymm (Ideal.comap_mono hK'Q) ?_
    have h1 : Q.under R ≤ pS.comap (algebraMap R S) := hpS.symm ▸ Ideal.le_comap_map
    exact h1.trans (Ideal.comap_mono hpSK')
  -- Quasi-finiteness: `K' = Q`, hence `K = K'.map f = Q.map f = J`, so `J ≤ K`.
  have hK'Q' : K.comap f = Q := QuasiFiniteAt.eq_of_le_of_under_eq hK'Q hunder
  have hKJ' : K = Q.map f :=
    calc K = (K.comap f).map f := (Ideal.map_comap_of_surjective f hsurj K).symm
      _ = Q.map f := by rw [hK'Q']
  exact hKJ'.ge

/-- For a flat, Noetherian `R`-algebra `S` quasi-finite at a prime `Q`, the height of `Q`
equals the height of the prime `Q.under R` it lies over. -/
theorem Ideal.height_eq_under_of_flat_quasiFiniteAt
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (Q : Ideal S) [Q.IsPrime] [Algebra.QuasiFiniteAt R Q] :
    Q.height = (Q.under R).height := by
  have := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.under R) Q
  rw [fibre_height_eq_zero_of_quasiFiniteAt Q, add_zero] at this
  exact this

/-- Étale algebras are flat and quasi-finite, so an étale Noetherian `R`-algebra `S` preserves
the height of every prime: `Q.height = (Q.under R).height`. -/
theorem Ideal.height_eq_under_of_etale
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S]
    (Q : Ideal S) [Q.IsPrime] :
    Q.height = (Q.under R).height :=
  Ideal.height_eq_under_of_flat_quasiFiniteAt Q

/-- Non-vacuity: the hypotheses hold for the identity algebra `R = S` (flat and module-finite over
itself), where the statement reduces to `Q.height = Q.height`. -/
example [IsNoetherianRing R] (Q : Ideal R) [Q.IsPrime] :
    Q.height = (Q.under R).height :=
  Ideal.height_eq_under_of_flat_quasiFiniteAt (R := R) (S := R) Q

end DLNFibre.Core

import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Basic
import DLNFibre.Core.Dimension.Localization
import DLNFibre.Core.Dimension.Codimension
import DLNFibre.Core.Dimension.AffineDomain
import DLNFibre.Core.Dimension.Regular
import DLNFibre.Core.RingTheory.Ideal.CotangentLocalization

/-!
# `Orbit.Dimension` — the `varietyDim = trdeg` anchor (A4.1) + B4 `SmoothCotangentDim`

The squeeze's **lower anchor** and its **upper cotangent identity** on the abstract
affine-`G`-variety carrier `AlgebraicGeometry.Group.Orbit.AffineGVariety` (`Orbit/Basic.lean`). For
an orbit-image variety presented as the kernel/range of the coordinate pullback `μ* = aeval fρ`:

* **A4.1 anchor** — its dimension is the transcendence degree of the orbit coordinate algebra
  `k[fρ]`: `varietyDim Z = (trdeg k (μ*.range)).toNat`, when `vanishingIdeal Z = ker μ*`;
* **B4 `SmoothCotangentDim` (A6.1 second half)** — at a **smooth `k`-rational point** `m` of a
  finite-type `k`-domain coordinate ring `A = MvPolynomial σ k ⧸ I` (`I` parameterized; for the
  orbit-image presentation `I = ker μ*`), the Zariski cotangent space `m.Cotangent` has
  `k`-dimension equal to the variety dimension: `finrank k (m.Cotangent) = varietyDim Z`.

This file holds the **abstract** A4.1 anchor + B4; the DLN matrix-tuple specialisations re-derive
from them through the orbit↔kernel bridge `vanishingIdeal_range_orbitMap_eq_ker` (A4.1:
`ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat`, `Core/AffineNoetherRank.lean`; B4: R6
`finrank_cotangent_eq_varietyDim`, `Core/OrbitTangentCotangent.lean`).

## B4 — the smooth-point cotangent identity (A6.1 second half), name = content

B4 lifts R6 onto the carrier. The hypotheses are the **point's** smoothness and `k`-rationality, NOT
a smooth-point *existence* claim — the existence (the M3 generic-smoothness density argument: a
dense `k`-orbit meets the open smooth locus, giving a genuinely `k`-rational smooth point over a
possibly non-algebraically-closed `k`) is the concrete model's burden, discharged in the DLN
instance, never a hypothesis of B4. The pinned hypothesis bundle:

* `[Finite σ]` — `A` is a finite-type `k`-algebra (needed by M3 + the affine-domain dimension);
* `[PerfectField k]` — M3's residue-field formal smoothness (no algebraic closedness; `ℝ` ok);
* `m` maximal with `[Algebra.IsSmoothAt k m]` — the point IS smooth;
* `hrat : Ideal.ResidueField m ≃ₐ[k] k` — the point IS `k`-rational (residue field is `k`);
* `hZ : vanishingIdeal Z = I` — the A0 bridge linking `varietyDim Z` to `ringKrullDim A`.

The route is the R6 chain stated abstractly: L2a localization collapse
(`Ideal.finrank_cotangentSpace_localization_eq_cotangent`), the κ/k bridge
(`finrank_eq_finrank_of_residueField_equiv`, GAP2), M3
(`finrank_cotangentSpace_eq_of_isSmoothAt` at a smooth point), GAP3
(`ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`), and `varietyDim Z = ringKrullDim A` (the
A0 bridge + the `varietyDim` definition). All bricks are DLN-free Phase-1 dimension facts.

## What enters where (name = content)

* `[Finite G.ρ]` is a hypothesis on these lemmas — NOT on the base carrier. It is the
  finite-generation input: with `G.ρ` finite the orbit coordinate algebra
  `G.pullback.range = Algebra.adjoin k (range G.fρ)` is a finitely-generated `k`-algebra, so the
  Phase-1 `dim = trdeg` fact (`ringKrullDim_eq_trdeg_of_fg_domain`) applies. The base carrier
  `Orbit/Basic.lean` deliberately keeps `ρ` finiteness off, so the irreducibility layer carries the
  minimal hypotheses; finiteness is added here, where dimension needs it.
* The **A0 bridge** `vanishingIdeal k Z = RingHom.ker G.pullback.toRingHom` is a hypothesis on
  `varietyDim_eq_trdeg_of_eq_ker`: the orbit↔kernel equality is a model-specific input that the
  concrete instance supplies (for the DLN matrix tuple, `vanishingIdeal_range_orbitMap_eq_ker`); the
  abstract carrier never asserts the orbit or its point set exists.

The transport is the first-iso `MvPolynomial G.ρ k ⧸ ker μ* ≃ₐ[k] μ*.range`
(`Ideal.quotientKerEquivRange`), carried through `ringKrullDim_eq_of_ringEquiv`. The orbit
coordinate algebra is a domain (subalgebra of the domain `G.R`), automatically.

The eventual Mathlib home is `Mathlib.AlgebraicGeometry.Group.Orbit.Dimension`; the namespace here
mirrors that target (bare `AlgebraicGeometry.Group.Orbit`) so the lift is a file-move.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace AlgebraicGeometry.Group.Orbit

open MvPolynomial Module DLNFibre.Core.Dimension

namespace AffineGVariety

universe u

variable {k : Type u} [Field k] (G : AffineGVariety k)

/-- The orbit coordinate algebra `G.pullback.range = k[fρ]` is a **finitely-generated** `k`-algebra
when the ambient coordinate index `G.ρ` is finite: it is the range of `μ* : MvPolynomial G.ρ k →ₐ[k]
G.R`, and `MvPolynomial G.ρ k` is finite-type over `k` for finite `G.ρ`. -/
instance finiteType_pullback_range [Finite G.ρ] : Algebra.FiniteType k G.pullback.range := by
  haveI : Fintype G.ρ := Fintype.ofFinite _
  exact Algebra.FiniteType.of_surjective G.pullback.rangeRestrict
    (AlgHom.rangeRestrict_surjective _)

/-- **Abstract A4.1 anchor (orbit-coordinate-algebra form).** For a finite ambient coordinate index
`G.ρ`, the Krull dimension of the orbit coordinate algebra `G.pullback.range = k[fρ]` equals its
transcendence degree over `k`:
`(ringKrullDim G.pullback.range).unbotD 0 = (Algebra.trdeg k G.pullback.range).toNat`.

`G.pullback.range` is a finitely-generated `k`-domain (`finiteType_pullback_range`; a subalgebra of
the domain `G.R`), so this is the Phase-1 f.g.-domain fact `ringKrullDim_eq_trdeg_of_fg_domain` read
off in `.unbotD`/`.toNat` form. Char-free. -/
theorem ringKrullDim_pullback_range_unbotD_eq_trdeg_toNat [Finite G.ρ] :
    (ringKrullDim G.pullback.range).unbotD 0
      = (Algebra.trdeg k G.pullback.range).toNat := by
  rw [ringKrullDim_eq_trdeg_of_fg_domain (k := k) G.pullback.range]
  exact WithBot.unbotD_coe 0 _

/-- **Abstract A4.1 anchor (variety-dimension form).** For a finite ambient coordinate index `G.ρ`
and a point set `Z ⊆ G.ρ → k` whose vanishing ideal *is* the pullback kernel — the **A0 bridge**
`vanishingIdeal k Z = ker μ*` that each concrete model supplies (for the DLN matrix tuple,
`vanishingIdeal_range_orbitMap_eq_ker`) — the variety dimension of `Z` equals the transcendence
degree of the orbit coordinate algebra `k[fρ]`:
`varietyDim Z = (Algebra.trdeg k G.pullback.range).toNat`.

The vanishing ideal is rewritten to `ker μ*` by the bridge; the coordinate ring
`MvPolynomial G.ρ k ⧸ ker μ*` is `k`-algebra isomorphic to `μ*.range` (first iso theorem
`Ideal.quotientKerEquivRange`), transporting the Krull dimension
(`ringKrullDim_eq_of_ringEquiv`); then the orbit-coordinate-algebra anchor closes it. Char-free; the
abstract carrier never asserts `Z` (or the orbit) exists — the bridge is the model input. -/
theorem varietyDim_eq_trdeg_of_eq_ker [Finite G.ρ] {Z : Set (G.ρ → k)}
    (hZ : MvPolynomial.vanishingIdeal k Z = RingHom.ker G.pullback.toRingHom) :
    varietyDim Z = ((Algebra.trdeg k G.pullback.range).toNat : ℕ∞) := by
  -- transport the coordinate ring through the first iso onto the orbit coordinate algebra
  let Ψ : (MvPolynomial G.ρ k ⧸ RingHom.ker G.pullback.toRingHom) ≃ₐ[k] G.pullback.range :=
    Ideal.quotientKerEquivRange G.pullback
  rw [varietyDim, hZ, ringKrullDim_eq_of_ringEquiv Ψ.toRingEquiv,
    ringKrullDim_eq_trdeg_of_fg_domain (k := k) G.pullback.range]
  exact WithBot.unbotD_coe 0 _

end AffineGVariety

variable {k : Type u} [Field k]

/-! ## B4 — the smooth-point cotangent identity (A6.1 second half) -/

/-- **B4 — `SmoothCotangentDim` (A6.1 second half), abstract.** At a **smooth `k`-rational point**
`m` of a finite-type `k`-domain coordinate ring `A = MvPolynomial σ k ⧸ I` (`σ` finite, `I` prime —
the orbit-image presentation ideal), the Zariski cotangent space `m.Cotangent` has `k`-dimension
equal to the variety dimension of any point set `Z` whose vanishing ideal is `I`:
`finrank k (m.Cotangent) = varietyDim Z`.

The hypotheses are the **point's** properties — `m` smooth (`[Algebra.IsSmoothAt k m]`) and
`k`-rational (`hrat : Ideal.ResidueField m ≃ₐ[k] k`) — NOT a smooth-point *existence* claim; the
existence (M3 generic-smoothness density: a dense `k`-orbit meets the open smooth locus, yielding a
genuinely `k`-rational smooth point over a possibly non-algebraically-closed `k`) is the concrete
model's burden, discharged in the DLN instance (`isSmoothAt_normalFormIdeal` +
`residueFieldAtPrimeNormalFormEquiv`), never a hypothesis here.

`I` is **parameterized** (not hard-wired to `ker μ*`): like B3's `InfinitesimalAction`, this lets
the concrete model instantiate `I = orbitIdeal M` and re-derive R6 `finrank_cotangent_eq_varietyDim`
**definitionally** (no quotient/cotangent transport). For the carrier orbit-image presentation
`I = ker G.pullback`, the A0 bridge `hZ` reads `vanishingIdeal Z = ker μ*` (`P2.3`'s anchor uses the
same input).

Route (R6 stated abstractly): `varietyDim Z =[A0 bridge `hZ` + def] ringKrullDim A` (a finite nat
`n`); `=[GAP3] ringKrullDim (AtPrime m)`; `=[M3, smooth point] finrank κ (CotangentSpace m)`;
`=[GAP2, `k`-rational residue field] finrank k (CotangentSpace m)`; `=[L2a localization
collapse] finrank k (m.Cotangent)`. All DLN-free Phase-1 dimension facts. Char carried via
`[PerfectField k]` (M3). -/
theorem finrank_cotangent_eq_varietyDim [PerfectField k] {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [hI : I.IsPrime]
    (m : Ideal (MvPolynomial σ k ⧸ I)) [hm : m.IsMaximal] [Algebra.IsSmoothAt k m]
    (hrat : Ideal.ResidueField m ≃ₐ[k] k)
    {Z : Set (σ → k)} (hZ : MvPolynomial.vanishingIdeal k Z = I) :
    (finrank k (m.Cotangent) : ℕ∞) = varietyDim Z := by
  classical
  haveI : Fintype σ := Fintype.ofFinite _
  haveI : m.IsPrime := hm.isPrime
  haveI : IsDomain (MvPolynomial σ k ⧸ I) := Ideal.Quotient.isDomain I
  haveI : Algebra.FiniteType k (MvPolynomial σ k ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ_surjective k I)
  -- `varietyDim Z = ringKrullDim A` as a finite nat `n`
  have hge : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ k ⧸ I) :=
    ringKrullDim_nonneg_of_nontrivial
  have hle : ringKrullDim (MvPolynomial σ k ⧸ I) ≤ (Nat.card σ : WithBot ℕ∞) := by
    refine le_trans (ringKrullDim_quotient_le I) ?_
    rw [ringKrullDim_mvPolynomial_finite]
  have hbot : ringKrullDim (MvPolynomial σ k ⧸ I) ≠ ⊥ := by
    intro h; rw [h] at hge; simp at hge
  have hcardlt : (Nat.card σ : WithBot ℕ∞) < (⊤ : WithBot ℕ∞) := compareOfLessAndEq_eq_lt.mp rfl
  have htop : ringKrullDim (MvPolynomial σ k ⧸ I) ≠ (⊤ : WithBot ℕ∞) :=
    ne_of_lt (lt_of_le_of_lt hle hcardlt)
  obtain ⟨w, hw⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hwtop : w ≠ ⊤ := fun h ↦ htop (by rw [← hw, h]; rfl)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((n : ℕ∞) : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ I) :=
    ⟨w.toNat, by rw [ENat.coe_toNat hwtop, hw]⟩
  have hvar : varietyDim Z = (n : ℕ∞) := by
    rw [varietyDim, hZ, ← hn, WithBot.unbotD_coe]
  -- GAP3: localization at the maximal ideal has the same dim
  have hdimLoc : ringKrullDim (Localization.AtPrime m) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [ringKrullDim_localizationAtPrime_isMaximal_eq_fintype I m, ← hn]
  -- M3: smooth point ⟹ finrank κ (CotangentSpace) = n
  have hM3 : finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
      (IsLocalRing.CotangentSpace (Localization.AtPrime m)) = n :=
    finrank_cotangentSpace_eq_of_isSmoothAt (k := k) (A := MvPolynomial σ k ⧸ I) m hdimLoc
  -- κ/k bridge (GAP2): the residue field is `k`-rational
  haveI : IsScalarTower k (IsLocalRing.ResidueField (Localization.AtPrime m))
      (IsLocalRing.CotangentSpace (Localization.AtPrime m)) := by
    refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
    rw [IsScalarTower.algebraMap_apply k (Localization.AtPrime m)
        (IsLocalRing.ResidueField (Localization.AtPrime m)) r, algebraMap_smul, algebraMap_smul]
  have hbridge : finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime m))
      = finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) :=
    finrank_eq_finrank_of_residueField_equiv hrat
  -- L2a collapse: `finrank k (m.Cotangent) = finrank k (CotangentSpace (AtPrime m))`
  have hcollapse : finrank k (m.Cotangent)
      = finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime m)) :=
    (Ideal.finrank_cotangentSpace_localization_eq_cotangent (k := k) m).symm
  rw [hvar, hcollapse, hbridge, hM3]

end AlgebraicGeometry.Group.Orbit

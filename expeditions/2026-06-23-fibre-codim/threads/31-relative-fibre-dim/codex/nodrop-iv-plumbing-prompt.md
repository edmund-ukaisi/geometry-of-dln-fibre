<task>
Lean 4 + Mathlib v4.29.0 proof-engineering / API-name validation (NOT strategy).

I am proving in Lean 4 (Mathlib pinned at v4.29.0):

  theorem ringKrullDim_localizationAway_eq_of_fg_domain
    (D : Type u) [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D]
    (g : D) (hg : g ≠ 0) :
    ringKrullDim (Localization.Away g) = ringKrullDim D

where k is a Field.

I ALREADY HAVE (proved, sorry-free), via Noether normalization
(exists_integral_inj_algHom_of_fg) + my engine's trdeg_eq_of_integral_injective:

  theorem ringKrullDim_eq_trdeg_of_fg_domain (A : Type u) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toNat : WithBot ℕ∞)

So the headline reduces to:
  (a) Algebra.trdeg k (Localization.Away g D) = Algebra.trdeg k D, AND
  (b) discharging the instances [IsDomain (Localization.Away g D)],
      [Algebra k (Localization.Away g D)], [Algebra.FiniteType k (Localization.Away g D)],
      [IsScalarTower k D (Localization.Away g D)] so that
      ringKrullDim_eq_trdeg_of_fg_domain applies to A := Localization.Away g D.

My intended route for (a): the tower k ⊆ D ⊆ Frac D and k ⊆ (D[1/g]) ⊆ Frac D, with Frac D
algebraic over both D and D[1/g], so trdeg_add_eq (stacks 030H) gives
trdeg k (Frac D) = trdeg k D + 0 and = trdeg k (D[1/g]) + 0, hence equal.

I need EXACT v4.29 names. Questions:

QUESTION 1 (route (a)):
 - Exact name: "FractionRing D is algebraic over D" (Algebra.IsAlgebraic D (FractionRing D)) —
   is it an instance, or a lemma I must invoke (e.g. IsFractionRing.isAlgebraic / something)?
 - For S = Localization.Away g D (a localization of a domain at a nonzero element, so
   M = Submonoid.powers g ≤ nonZeroDivisors D): how do I get the scalar tower D → S → Frac D
   with [IsScalarTower D S (FractionRing D)] and the fact [IsFractionRing S (FractionRing D)]?
   I see IsFractionRing.isFractionRing_of_isDomain_of_isLocalization in
   RingTheory/Localization/LocalizationLocalization.lean — what are its exact hypotheses and
   the algebra/scalar-tower instances it needs me to provide (Algebra S (FractionRing D),
   IsScalarTower D S (FractionRing D))? How do I construct Algebra (Localization.Away g D)
   (FractionRing D) at v4.29 (IsLocalization.lift? Localization.algebra via a submonoid
   inclusion? IsScalarTower.of_algebraMap_eq?)?
 - trdeg_add_eq exact signature at v4.29: it is in
   RingTheory/AlgebraicIndependent/TranscendenceBasis.lean and reads
   [Nontrivial R] {A} [CommRing A] [NoZeroDivisors A] [Algebra R A] [Algebra S A]
   [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
   trdeg R S + trdeg S A = trdeg R A. Confirm and tell me the cleanest way to discharge
   [FaithfulSMul k D] (k field → D domain k-algebra) and [FaithfulSMul D (FractionRing D)]
   and [FaithfulSMul S (FractionRing D)] — exact instance/lemma names
   (faithfulSMul_iff_algebraMap_injective and the injectivity facts).
 - Is there a MORE DIRECT trdeg-under-localization lemma at v4.29 I am missing (something like
   Algebra.trdeg_localization / IsLocalization-preserves-trdeg)? grep terms to try.

QUESTION 2 (route (b), the instances):
 For Localization.Away g D with [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FiniteType k D]
 and g ≠ 0:
 - [IsDomain (Localization.Away g D)] — automatic instance? (IsLocalization domain instance,
   exact name?)
 - [Algebra k (Localization.Away g D)] and [IsScalarTower k D (Localization.Away g D)] —
   automatic? exact instance names (Localization.algebra, IsScalarTower.subsemiring? etc.).
 - [Algebra.FiniteType k (Localization.Away g D)] — I found
   RingTheory/Localization/Away/AdjoinRoot.lean:57 has `Algebra.FiniteType R (Localization.Away f)`.
   Confirm it is an instance and that it composes with FiniteType k D to give FiniteType k (D[1/g])
   (Algebra.FiniteType.trans), and give the exact name of the transitivity lemma.
</task>

<output_contract>
Two sections, "Q1" and "Q2". For each sub-question give the EXACT Lean v4.29 declaration name
(fully qualified) and whether it is an `instance` (auto) or a `theorem`/`lemma` I must invoke.
Where I must construct an algebra/scalar-tower instance by hand, give the 1-3 line Lean incantation.
If a name does not exist at v4.29, say so explicitly and give the nearest alternative. Flag any
place my intended route has a gap (e.g. a missing instance that is NOT automatic). Be terse and
name-precise; this is plumbing validation. Do not restate strategy.
</output_contract>

<grounding_rules>
You are reasoning about Mathlib v4.29.0 specifically. If you are not certain a name exists at that
pin, say "uncertain at v4.29 — verify by grep: <term>" rather than assert it. Distinguish names you
are confident about from ones you are inferring.
</grounding_rules>

<task>
Lean 4 + Mathlib (pin v4.29.0). I am proving "smooth point ⟹ regular local ring" for a
finite-type algebra A over an algebraically closed field k, at a maximal ideal m where A is
smooth (IsSmoothAt k m). I want the CLEANEST route and a sizing on whether it fits PRESENT
Mathlib API (no new sub-library), or fires a kill-condition (a genuinely-absent
conormal/left-exactness sub-library).

ALREADY LANDED (M2, a theorem I can cite as a black box), with k ANY field:
  theorem ringKrullDim_localizationAtPrime_eq_of_isSmoothAt
    (m : Ideal A) [m.IsMaximal] [IsSmoothAt k m] :
    ∃ (n : ℕ) (f : A), f ∉ m ∧
      IsStandardSmoothOfRelativeDimension n k (Localization.Away f) ∧
      Module.rank (Localization.Away f) (Ω[Localization.Away f⁄k]) = (n : Cardinal) ∧
      ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞)
So at the smooth point, ringKrullDim (AtPrime m) = n, AND on the chart S = A[1/f], Ω[S⁄k] is
free of rank n. (M2 is NON-circular: it computes the Krull dimension via an étale-over-affine
route, never using any cotangent/tangent identity.)

TARGET:
  theorem smooth_point_isRegularLocalRing
    [IsAlgClosed k] (m : Ideal A) [m.IsMaximal] [IsSmoothAt k m] :
    IsRegularLocalRing (Localization.AtPrime m)
plus a named companion finrank_cotangentSpace = n.

KEY MATHLIB BRICKS I HAVE CONFIRMED EXIST at this pin:
1. IsRegularLocalRing.of_spanFinrank_maximalIdeal_le [IsLocalRing R] [IsNoetherianRing R]
     (le : (maximalIdeal R).spanFinrank ≤ ringKrullDim R) : IsRegularLocalRing R
   (regularity from the EASY inequality spanFinrank ≤ dim; the reverse dim ≤ spanFinrank is
    Krull's height bound, ringKrullDim_le_spanFinrank_maximalIdeal, used inside it).
2. IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace [IsNoetherianRing R] :
     (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R)
   where CotangentSpace R := (maximalIdeal R).Cotangent  (= m/m² as a ResidueField-module).
3. The conormal exact sequence, for a surjection algebraMap A B with B = A/I:
     KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
       (h : Function.Surjective (algebraMap A B)) :
       Function.Exact (kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B)
   where  kerCotangentToTensor R A B : (RingHom.ker (algebraMap A B)).Cotangent →ₗ[A] B ⊗[A] Ω[A⁄R]
   and    mapBaseChange R A B : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R]
   and    exact_mapBaseChange_map : Function.Exact (mapBaseChange) (map ... ) with
          map_surjective giving B ⊗ Ω[A⁄R] → Ω[B⁄R] surjective.

MY PROPOSED REDUCTION (please vet hard):
Let R := Localization.AtPrime m, a Noetherian local k-algebra. Its residue field κ = ResidueField R.
Under [IsAlgClosed k] and m maximal, κ ≅ k (k-rational point; same Nullstellensatz/Zariski fact M2's
sibling uses). The maximal ideal of R is m_R, and CotangentSpace R = m_R/m_R².

I claim I only need the INEQUALITY finrank κ (m_R/m_R²) ≤ n, because:
  - M2 gives ringKrullDim R = n;
  - of_spanFinrank_maximalIdeal_le needs spanFinrank ≤ ringKrullDim, i.e. (via brick 2)
    finrank κ (CotangentSpace R) ≤ n.
So the HARD left-exact/H1-vanishing end (m/m² ↪ κ⊗Ω injective) is NOT needed — only the SURJECTIVITY
m_R/m_R² ↠ κ ⊗_R Ω[R⁄k], which gives finrank(m/m²) ≤ finrank(κ ⊗ Ω). Apply the conormal sequence to the
surjection R ↠ κ: since Ω[κ⁄k] = Ω[k⁄k] = 0 (κ=k a field, separable/trivial), mapBaseChange has image 0,
so by exactness kerCotangentToTensor is surjective onto κ ⊗_R Ω[R⁄k]; hence
finrank κ (m_R/m_R²) ≤ finrank κ (κ ⊗_R Ω[R⁄k]) = rank_R Ω[R⁄k] = n (Kähler localizes: Ω[R⁄k] is free of
rank n over R since Ω[S⁄k] free rank n and R = S localized; κ ⊗_R (free rank n) has κ-dim n).

QUESTIONS — answer each, flagging inference vs. a lemma you are confident exists at v4.29:
(Q1) Is the reduction to the INEQUALITY finrank(m/m²) ≤ n sound? Any hidden need for injectivity?
(Q2) The conormal sequence brick 3 has RING-level maps (A-linear / B-linear) and needs R = κ surjective
     algebraMap. To get finrank κ (m/m²) ≤ finrank κ (κ ⊗_R Ω) I must read the SURJECTION over κ. But
     kerCotangentToTensor is R-linear into κ ⊗_R Ω (which is a κ-module). Does "R-linear surjective onto a
     κ-module" give the κ-dimension bound finrank κ (m/m²) ≤ finrank κ (κ⊗Ω)? (m/m² is already a κ-module;
     is kerCotangentToTensor κ-linear, or do I need to descend scalars? Spell out the cleanest way to land
     finrank κ (m/m²) ≤ n.)
(Q3) finrank κ (κ ⊗_R Ω[R⁄k]) = n: cleanest path? Ω[R⁄k] free rank n over R (needs Kähler-localizes:
     name the lemma — IsLocalization base change of Kähler? or Ω of a localization is the localized module).
     Then κ ⊗_R (R-free rank n) is κ-free rank n. Name the finrank/base-change lemmas.
(Q4) κ ≅ k under [IsAlgClosed k], m maximal, in usable form: which Mathlib lemma gives ResidueField (AtPrime m)
     ≅ k, or do I instead show Ω[ResidueField⁄k] = 0 directly (separable field ext / IsAlgClosed)? Do I even
     NEED κ = k, or does Ω[κ⁄k] = 0 follow from κ being a finite/separable/trivial extension regardless?
     (Actually I suspect I need Ω[κ⁄k]=0, and that's automatic if κ/k is separably generated of tr.deg 0 =
     algebraic separable; with IsAlgClosed and Nullstellensatz κ = k so Ω[κ⁄k]=0 trivially. Confirm.)
(Q5) HONEST SIZING: does this assemble on present API (estimate LoC + the 5-8 load-bearing lemma names), or
     does any step (esp. Q2 scalar descent, Q3 Kähler-localizes) need an ABSENT sub-library? If absent, name
     the precise missing piece. This is the last flagged scope-surprise in the build; an early honest "it
     balloons HERE" is more valuable than an optimistic plan.
(Q6) Is there a SHORTER route I'm missing — e.g. a direct Mathlib lemma "Ω[R⁄k] free rank n + κ=k ⟹ R regular",
     or smooth-local ⟹ regular already in Mathlib (I found NO IsRegularLocalRing producers beyond PID/field)?
</task>

<output_contract>
Answer Q1–Q6 in order, terse. For each lemma you name, mark [CONFIRMED-recalled] vs [GUESS] and give the
fully-qualified Mathlib name + rough signature. End with a single verdict line:
  VERDICT: BOUNDED (~X LoC, route = …)  |  KILL (missing = …).
Do NOT write full Lean proofs; give the skeleton (lemma chain) only.
</output_contract>

<grounding_rules>
You may rely on recalled Mathlib but you MUST mark recall confidence. If you are unsure a lemma exists at
v4.29, say [GUESS] and give the mathematical content so I can grep for it. Distinguish "mathematically true"
from "available as a single Mathlib lemma". Flag any step where the κ-linearity vs R-linearity mismatch could
bite.
</grounding_rules>

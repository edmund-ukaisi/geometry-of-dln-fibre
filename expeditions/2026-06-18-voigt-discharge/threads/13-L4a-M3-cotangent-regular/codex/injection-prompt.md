<task>
Lean 4 + Mathlib v4.29.0. FOCUSED follow-up. I need exactly ONE thing: the cleanest path to

  finrank κ (CotangentSpace R) ≤ n      -- equivalently finrank κ (m/m²) ≤ n

where:
  R := Localization.AtPrime m  (a local k-algebra, k a field, [IsAlgClosed k]),
  κ := IsLocalRing.ResidueField R = R ⧸ maximalIdeal R,
  CotangentSpace R := (maximalIdeal R).Cotangent  (the κ-vector space m/m²),
  [IsSmoothAt k m]  which UNFOLDS DEFINITIONALLY to  Algebra.FormallySmooth k R  (Mathlib: IsSmoothAt R p := FormallySmooth R (Localization.AtPrime p)),
  and I separately have  Ω[R⁄k] is free of rank n over R  (so finrank κ (κ ⊗[R] Ω[R⁄k]) = n by Module.finrank_baseChange).

You already established (correct): I need an INJECTION m/m² ↪ κ ⊗[R] Ω[R⁄k], NOT a surjection.
The natural candidate map is
  KaehlerDifferential.kerCotangentToTensor k R κ : (RingHom.ker (algebraMap R κ)).Cotangent →ₗ[R] κ ⊗[R] Ω[R⁄k]
and RingHom.ker (algebraMap R κ) = maximalIdeal R (IsLocalRing.ker_residue + ResidueField.algebraMap_eq), so its
source IS m/m² = CotangentSpace R. I have the conormal exactness
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange (h : Surjective (algebraMap R κ)) :
    Function.Exact (kerCotangentToTensor k R κ) (mapBaseChange k R κ).
That gives range(kerCotangentToTensor) = ker(mapBaseChange); for INJECTIVITY I need ker(kerCotangentToTensor) = 0.

THE QUESTION: at v4.29, what is the cleanest existing path to "kerCotangentToTensor k R κ is injective" (or any
equivalent map m/m² ↪ κ⊗Ω) GIVEN FormallySmooth k R (and, if needed, FormallySmooth k κ / κ separable over k)?

Candidate routes I see — tell me which actually lands at v4.29, with EXACT lemma names + how they connect to
kerCotangentToTensor / IsLocalRing.CotangentSpace (the bridging is my worry):

ROUTE A (Jacobi–Zariski H1): triple k → R → κ. Mathlib has
  Algebra.H1Cotangent.exact_δ_mapBaseChange : Function.Exact (δ k R κ) (mapBaseChange k R κ)
  Algebra.H1Cotangent.exact_map_δ          : Function.Exact (map k k R κ ...) (δ ...)
and KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange.
  - Is the map m/m² = (maximalIdeal R).Cotangent IDENTIFIED in Mathlib with anything in the H1Cotangent /
    Extension.Cotangent world for the surjection R ↠ κ? i.e. is there a Mathlib equiv
    (maximalIdeal R).Cotangent ≃ (some Extension.Cotangent) so that kerCotangentToTensor = the cotangentComplex?
  - If FormallySmooth k R ⟹ Subsingleton (H1Cotangent k R) and FormallySmooth k κ ⟹ Subsingleton(H1Cotangent k κ),
    does the JZ sequence pin ker(kerCotangentToTensor) = 0? Spell out the 3-4 lemma chain. Flag every place the
    (maximalIdeal R).Cotangent ↔ H1Cotangent/Extension.Cotangent identification is needed but possibly ABSENT.

ROUTE B (split injection from FormallySmooth, the Generators.self route): Mathlib
  Algebra.FormallySmooth.iff_split_injection : FormallySmooth R A ↔ split-injective (I/I² → A ⊗[P] Ω[P/R])
  for P = Generators.self R A. But that's the cotangent complex of A/R via its OWN presentation P, with
  I = ker(P → A), NOT the conormal map of R ↠ κ. Does this route even apply to my m/m² (which is the conormal
  of R↠κ, a DIFFERENT surjection)? If not, say so plainly.

ROUTE C (is there a DIRECT lemma): does Mathlib v4.29 have anything like
  "R local, FormallySmooth k R, κ formally smooth/separable over k ⟹ kerCotangentToTensor k R κ injective"
  or "the conormal sequence of R ↠ κ is split exact when R/k smooth"  — even phrased via Module.Projective /
  shortExact split? Name it if it exists.

ROUTE D (sidestep — bound finrank without the conormal map): Is there a cleaner inequality? e.g.
  finrank κ (m/m²) = finrank κ (κ ⊗[R] Ω[R⁄k])  directly from a Mathlib "smooth ⟹ Ω basis ↔ regular system of
  parameters" or "FormallySmooth R + local ⟹ m/m² ≃ κ⊗Ω"? Or via Module.Projective Ω[R/k] + the conormal
  being a split surjection of projectives forcing the kernel-side iso? Name the lemma.

For EACH route: VERDICT one of {LANDS at v4.29 (give the 3-6 lemma chain) | NEEDS bridging lemma X (name the
mathematical content + whether X is in Mathlib) | DEAD}. Then a final line: RECOMMENDED ROUTE = … , and an
honest LoC for just this injection step. If ALL routes need an absent (maximalIdeal R).Cotangent ↔ H1Cotangent
bridge, say KILL and name that bridge precisely — that is the kill-condition I must report.
</task>

<output_contract>
Per-route verdict as specified, terse, exact Mathlib names with [CONFIRMED-recalled]/[GUESS] tags. End with
RECOMMENDED ROUTE + LoC + (BOUNDED|KILL). No full Lean proofs; lemma chains only.
</output_contract>

<grounding_rules>
Mark recall confidence on every lemma. The load-bearing uncertainty is the identification of
IsLocalRing.CotangentSpace R = (maximalIdeal R).Cotangent (and kerCotangentToTensor) with the
Algebra.Extension.Cotangent / H1Cotangent machinery — be explicit about whether that bridge exists as a Mathlib
lemma or must be built. Do not assert a route LANDS unless every link is a real lemma.
</grounding_rules>

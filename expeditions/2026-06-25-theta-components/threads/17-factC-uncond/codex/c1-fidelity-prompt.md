<task>
Red-team a Lean 4 + Mathlib formalisation for SOUNDNESS / FIDELITY (not Lean syntax — assume it
compiles axiom-clean). Two questions.

## Q1 — Is the C1 statement and its proof mechanism mathematically correct AND faithful?

Statement (general CA): for a REDUCED Noetherian ring R with a prime q such that I ≤ q for a
distinguished minimal prime I, and NO OTHER minimal prime J ≤ q, the quotient map R → R⧸I induces
a k-algebra iso `Localization.AtPrime R q ≃ₐ[k] Localization.AtPrime (R⧸I) (q.map (mk I))`.

Proof: the kernel I dies in `Localization.AtPrime R q`. For x ∈ I, let T = ⨅ of the OTHER minimal
primes (a Finset.inf over minimalPrimes filtered ≠ I; finite by Noetherian). T ⊄ q (else q prime ⟹
some other J ≤ q, contradicting uniqueness), so pick s ∈ T \ q. Then x·s lies in every minimal prime
(in I since x∈I; in each other J since s∈T≤J), hence in sInf(minimalPrimes) = radical ⊥ = ⊥ (reduced).
s ∉ q ⟹ algebraMap x = 0 in AtPrime q. So I.map(algebraMap) = ⊥; localAlgHom is bijective (inj via the
killed kernel; surj since mk surjective); the iso transfers IsSmoothAt by FormallySmooth.iff_of_equiv.

Specialization used in the application: q := I itself (a minimal prime as its own generic point).
Then "no other minimal prime ≤ I" is claimed FREE by incomparability of minimal primes. Confirm:
(a) the mechanism has no gap; (b) q = I makes huniq genuinely free; (c) any HIDDEN assumption
(e.g. does the argument secretly need q ≠ ⊤, or R⧸I nontrivial, or finitely many minimal primes
beyond Noetherian)?

## Q2 — Is the C2 reduction HONEST about what is open?

The C2 lemma `isSmoothAt_sweepFibre_of_component_orbitSmooth` ASSUMES a hypothesis
`e : sweepFibreRing⧸I ≃ₐ[k] orbitRing M` (a k-algebra iso of the fibre's top-component quotient with
an orbit-closure coordinate ring), plus `I ∈ minimalPrimes`, and CONCLUDES `IsSmoothAt k I` of
sweepFibreRing. The claim is that `e` (call it C2(a)) is the SINGLE remaining open geometric input,
and everything else (C1, the domain generic-point step, OrbitSmooth's smoothness at the normal-form
point) is unconditional.

Is the hypothesis `e` LOAD-BEARING and NOT smuggling the conclusion? I.e. could `e` be vacuous
(no such M/iso ever exists, making the lemma trivially-true-but-useless), or conversely could it be
so strong that it trivially implies the conclusion without the CA work? Assess whether this is an
honest reduction of "fact C" to one named geometric fact, or whether it overclaims/underclaims.
</task>

<output_contract>
For Q1: VERDICT (sound / gap) + the single sharpest concern. For Q2: VERDICT (honest reduction /
overclaim / vacuous) + reasoning. Be terse. Flag inference vs. confident fact.
</output_contract>

<grounding_rules>
You do not have the Lean source; reason from the math description. Flag anything you cannot verify
without the code.
</grounding_rules>

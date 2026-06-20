<task>
You are a decorrelated second reviewer auditing the FIDELITY of a Lean 4 + Mathlib
formalisation against an informal mathematical claim. I want your independent read on
whether the Lean statements are the RIGHT rendering of the cited theorem, and whether
anything in the proof chain looks "too clean" / overclaimed. You are NOT checking the
Lean compiles (it does, axiom-clean: [propext, Classical.choice, Quot.sound]); you are
judging whether name=content and the statement is neither weaker nor stronger than
advertised.

CONTEXT — the mathematics.
Equioriented type-A quiver A_{N+1} (a chain of vector spaces d_0 → d_1 → ... → d_N,
linear maps A_i). A "tuple" M is a point of Rep_d = ∏_i Hom(k^{d_i}, k^{d_{i+1}}),
i.e. a composable matrix tuple. The group G_d = ∏_v GL_{d_v} acts by base change
(P • A)_i = P_{i+1} A_i P_i^{-1}. For i ≤ j the "interval sub-product" is
submult(A,i,j) = A_j ··· A_{i+1} (empty product = identity at i=j), and the rank
pattern r_{ij}(A) = rank(submult(A,i,j)) (so r_{ii} = d_i).

The cited theorem is Abeasis–Del Fra (the paper reads it as Lehalleur–Rimányi 2024
Thm 3.8): the Zariski closure of the G_d-orbit Ō_M equals the determinantal rank locus
orbitRankLocus(M) = { A | r_{ij}(A) ≤ r_{ij}(M) for all i ≤ j }, and this closure is
irreducible.

THE TWO LEAN HEADLINES (over MvPolynomial (RepCoord d) k, the coordinate ring of Rep_d,
with canonicalCoord : Rep_d ≃ (RepCoord d → k) the honest entry-flattening):

1. [Field k] [Infinite k]:
   vanishingIdeal k (canonicalCoord '' orbitRankLocus M) = vanishingIdeal k (orbitSet M)
   where orbitSet M = canonicalCoord '' (G_d · M) is the flattened orbit.

2. [Field k] [IsAlgClosed k]:
   (vanishingIdeal k (canonicalCoord '' orbitRankLocus M)).IsPrime

Both are proved unconditionally (no extra hypotheses). The proof of (1):
 - easy ≤ : O_M ⊆ orbitRankLocus M (base change preserves rank pattern), order-reverse.
 - hard ≥ : every rank-locus point lies in the Zariski closure repClosure(orbitSet M),
   via a "box-move chain" (Abeasis–Del Fra degeneration order on rank patterns) where
   each step is a geometric 1-parameter degeneration of interval modules, transported to
   realizers by the rank-pattern bridge (same rank pattern ⟹ same orbit, Cor 2.9) and
   G_d-stability of the closure. Then push vanishingIdeal: vanishingIdeal(closure S) =
   vanishingIdeal(S) (Galois connection u∘l∘u = u, no Nullstellensatz needed).
(2) rewrites (1)'s ideal to vanishingIdeal(orbitSet M), which is prime because the orbit
is the image of the irreducible group G_d under a polynomial map (kernel into a domain).

The statement card explicitly does NOT claim the Set-level equality
orbitRankLocus M = Ō_M; only the ideal-level (= same vanishing ideal = same Zariski
closure) statement.

SPECIFIC QUESTIONS:
(A) Is "same vanishing ideal" the correct ideal-level rendering of "same Zariski closure"
    over an infinite (not nec. algebraically closed) field? Over a general infinite field,
    is vanishingIdeal(S) = vanishingIdeal(T) equivalent to closure(S) = closure(T) where
    closure = zeroLocus∘vanishingIdeal (the k=K read=write field operator)? Is the
    headline named honestly given it does NOT prove the Set-level rank-locus = closure?
(B) Is requiring only [Infinite k] for headline (1) plausibly correct (not secretly needing
    algebraic closedness)? Note the easy inclusion and the degeneration are purely about
    vanishing ideals / Zariski closure, and primeness (2) is the only place IsAlgClosed
    enters. Does that division of hypotheses smell right?
(C) The primeness (2) gives "irreducible variety". Over a NON-algebraically-closed field,
    would calling a prime vanishing ideal "irreducible variety" be an overclaim? Is the
    [IsAlgClosed k] hypothesis the honest guard for that language?
(D) Anything about the chain that looks too clean? In particular: a degeneration argument
    that proves orbitRankLocus ⊆ closure(orbit) at the IDEAL level (not the harder Set
    level) — is there a subtle gap where the ideal statement could hold while the geometric
    claim it advertises fails? Is the "we only claim the ideal equality" scoping a genuine
    honest weakening, or could it be hiding that the Set-level statement is actually false
    as stated (e.g. over a finite or non-closed field)?
</task>

<output_contract>
Five short sections labelled (A)–(D) plus a final one-line VERDICT
(RIGHT-RENDERING / OVERCLAIM / UNDER-SPECIFIED). Each of (A)–(D): 3–6 sentences,
concrete. If you identify a genuine fidelity gap, state it as a precise mathematical
discrepancy, not a vibe.
</output_contract>

<grounding_rules>
Distinguish what you can assert as standard commutative-algebra fact (cite the mechanism:
Galois connection between zeroLocus and vanishingIdeal, radical ideals, Nullstellensatz
needing algebraic closure) from what is inference about THIS specific formalisation that
you cannot verify without the source. Flag inference vs fact explicitly. Do not assume the
Lean is wrong just because it is clean; do not rubber-stamp it either.
</grounding_rules>

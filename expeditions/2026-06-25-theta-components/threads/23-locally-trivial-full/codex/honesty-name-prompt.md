<task>
You are an algebraic geometer red-teaming a NAMING/HONESTY question in a Lean 4 + Mathlib formalisation. Do NOT trust my framing; judge independently.

Setting (Lehalleur–Rimányi style determinantal geometry). Fix a type-A dimension vector d : Fin (N+2) → ℕ and a rank r. There is a "multiplication" map mult sending a tuple of matrices A to a product matrix mult(A). Define:
- productRankLocus d r := { A | rank(mult A) = r }  -- the rank-EXACTLY-r locus, call it Σ^r. This is LOCALLY CLOSED (constructible), NOT Zariski-closed.
- sweepSigma := image of Σ^r under a coordinate embedding (still the rank-=r set, in coordinate space).
- sweepSigmaRing := MvPolynomial(coords) / vanishingIdeal(sweepSigma).
  KEY: a quotient by a vanishing ideal is the coordinate ring of the ZARISKI CLOSURE. The closure of the rank-=r locus is the determinantal variety rank ≤ r, call it Σ̄^r. So Spec(sweepSigmaRing) = Σ̄^r (the CLOSURE, rank ≤ r), which has a boundary stratum of rank < r points.

What was assembled in Lean (all machine-checked, zero sorry, axioms = [propext, Classical.choice, Quot.sound]):
A structure `PivotLocalProductAtlas` with fields:
  (1) cover : ∀ x ∈ sweepSigma (the rank-=r set), ∃ pivot (s,t) [injective r-subsets of rows/cols] with the r×r minor det of mult evaluated at x a UNIT. (i.e. a POINT-SET cover of the rank-=r locus by principal-open charts D(Δ_{s,t}). This is proved via "a rank-r matrix has an invertible r×r minor".) NOTE: this is a pointwise ∀x∃pivot statement, NOT a statement that the minors {Δ_{s,t}} generate the unit ideal (span = ⊤) of sweepSigmaRing.
  (2) triv : at every pivot (s,t), an AlgEquiv Localization.Away(Δ_{s,t}) ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing  (a local product trivialization into a fixed standard fibre).
  (3) overlapTransition : on each pair of pivots, the canonical R-algebra transition AlgEquiv between the two iterated localizations of sweepSigmaRing at Δ_I, Δ_J (the standard localization-initiality cocycle: it round-trips to identity, symm law, base-fixing).
  (4) transitionFactors : the transition between two trivializations equals the transition between the underlying chart equivs (the shared tensor "fibre tail" cancels), so transitions are base-algebraic (gauge transports).

The deliverable is NAMED `reducedFibre_locallyTrivialOnRankLocus`. The module docstring states explicitly: a bare scheme-theoretic `locallyTrivial` over Spec(sweepSigmaRing) = Σ̄^r (the closure) is FALSE, because the rank-<r boundary points lie in NO chart (all r×r minors vanish there); the charts cover exactly the OPEN rank-=r locus Σ^r; so the cover is the point-set cover, NOT span = ⊤ over the closure ring; the residual to a bare scheme-theoretic statement is to localize sweepSigmaRing to the rank-=r open and prove span=⊤ there.

THE QUESTION I want adjudicated, independently and skeptically:
Is naming this `reducedFibre_locallyTrivialOnRankLocus` an HONEST representation, given that (i) the cover is a point-set ∀x∃pivot statement, not span=⊤ over the structure ring, and (ii) the base ring is the closure Σ̄^r but the cover is only over the open rank-=r locus Σ^r? Or is ANY use of "locallyTrivial" in the name an overclaim a careful algebraic geometer would object to?
</task>

<output_contract>
Answer in 4 short sections, terse:
1. VERDICT on the name: is "locallyTrivialOnRankLocus" honest, an overclaim, or should it be even weaker? One of {HONEST, MILD-OVERCLAIM, OVERCLAIM}.
2. The single sharpest reason for your verdict (the load-bearing gap, if any, between what a working geometer means by "the bundle is locally trivial over Σ^r" and what fields (1)-(4) actually establish).
3. Is the point-set cover (∀x∃pivot, minor a unit) genuinely the right notion of "covers Σ^r" here, or does honest "locally trivial over Σ^r" REQUIRE the span=⊤ (unit ideal) statement over the localized open — i.e. is the residual the authors flag (localize + span=⊤) actually load-bearing for the word "locally trivial", or is it cosmetic?
4. If you'd pick a different name, give the one you'd defend (e.g. keep OnRankLocus, or downgrade to LocalProductAtlasWithCover / PointwiseLocalTriviality). One line.
</output_contract>

<grounding_rules>
Distinguish what is OBSERVED (from my description of the Lean fields) vs INFERRED (your geometric judgement). Flag any place where my description is too thin for you to be sure, and say what you'd need to check. Do not invent Lean API. The point at issue is purely whether the English word "locally trivial" in the name is earned by fields (1)-(4) as described.
</grounding_rules>

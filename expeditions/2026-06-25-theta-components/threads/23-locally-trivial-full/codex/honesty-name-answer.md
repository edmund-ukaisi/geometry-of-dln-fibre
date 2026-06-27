**1. Verdict**

**MILD-OVERCLAIM.**  
`OnRankLocus` prevents the serious false claim “locally trivial over the closure,” but `locallyTrivial` still suggests an actual scheme/open-subscheme local triviality statement, which fields (1)-(4) do not quite formalize.

**2. Sharpest Reason**

Observed: the cover is only `∀ x ∈ sweepSigma, ∃ pivot`, i.e. a point-set rank-exactly-`r` cover.  
Inferred judgment: a working geometer hearing “locally trivial over `Σ^r`” expects an open cover of the base locus as a geometric object, not merely coverage of its coordinate/rational points.

**3. Point-Set Cover vs Span**

The point-set cover is the right geometric intuition: rank `r` matrices are exactly where some `r × r` minor is nonzero. But for an honest scheme-theoretic “locally trivial over `Σ^r`” theorem, the residual “restrict/localize to the rank locus and prove the pivot opens cover there,” equivalently a unit-ideal/open-cover statement in the chosen formal model, is load-bearing, not cosmetic.

It is not required over `sweepSigmaRing` itself; that would be false because `Spec(sweepSigmaRing)` is the closure and contains the rank `< r` boundary.

**4. Name I’d Defend**

`reducedFibre_pivotLocalProductAtlasOnRankLocus`.

That keeps the real achievement: local product charts, transitions, and pointwise coverage on the rank locus, without sounding like the full scheme-level locally triviality theorem has already been packaged.
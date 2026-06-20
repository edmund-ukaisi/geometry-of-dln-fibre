**A. FIDELITY of (1)**
Yes: for `A = k[x₁,…,xₙ]/I` with `I` prime, the statement is the standard dimension formula
`ht(p) + dim(A/p) = dim A`, i.e. affine domains are equidimensional/catenary in this sense.
Using `WithBot ℕ∞` with ordinary addition is appropriate; since affine `k`-algebras are Noetherian of finite Krull dimension, this should not be a vacuous `⊤ = ⊤`.
Inference about Mathlib: assuming `Ideal.height` is supremum length of prime chains below `p`, it is the usual codimension/height.
`I` prime is mathematically needed for this headline as stated: arbitrary affine rings are not equidimensional, so the formula can fail. It may hold beyond domains, e.g. equidimensional affine algebras, but not generally.

**B. HYPOTHESES of brick (2)**
The brick is not true for arbitrary integral extensions: going-up gives one inequality, but equality of heights needs going-down or equivalent hypotheses.
`R` integrally closed domain plus integral extension is a standard sufficient going-down setup; `IsDomain R` and `IsIntegrallyClosed R` are genuinely doing work.
Injectivity is also needed if “under” is contraction along `R → S`: without it, e.g. `R → R/I`, contractions can collapse heights.
`IsDomain S` is likely stronger than needed: for a prime `P`, `S/P` is a domain, but going-down/height comparison usually does not require all of `S` to be a domain if hypotheses are phrased locally.
`IsNoetherianRing R` may be a proof/Mathlib convenience; the core going-down theorem does not inherently require Noetherianity, though finite-height equality statements often use it cleanly.
Missing hypothesis if integrally closed is removed: integral extensions can fail going-down, and then height equality can fail.

**C. CORROLLARIES (3),(4)**
The names match the content: (3) says closed/maximal primes have height equal to ambient dimension; (4) translates that to the local ring at such a maximal ideal.
Assuming `[m.IsMaximal]` is honest scoping, not a hidden Nullstellensatz gap: the result is conditional on maximality, not claiming every relevant ideal is maximal.
Yes, `height m = dim A` is equidimensionality at closed points, and it is true for all maximal ideals of this affine domain.
For (4), the name is accurate if Mathlib’s `ringKrullDim (Localization.AtPrime m)` is known to equal `height m`; that is the standard local dimension formula.

**D. VERDICT**
Faithful: (1) captures affine-domain equidimensionality; no hypothesis is too weak, though brick (2) likely has stronger-than-mathematically-minimal assumptions, especially `IsDomain S` and possibly Noetherianity; no content gap, but (4)’s name is local-ring-at-maximal, not a general localization statement.

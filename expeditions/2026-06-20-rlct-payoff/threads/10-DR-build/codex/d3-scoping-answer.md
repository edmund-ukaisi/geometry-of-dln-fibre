**Scope Choice**
- Land first on `codimRepCanonical (fibre d 0) = ⨅_{M ∈ orbitIdeals d 0} codimRepCanonical (orbitRankLocus M)` (i.e. bridge (a) only). This is exactly the “codimension of a finite union is the minimum codimension of its irreducible components” statement justified by `minimalPrimes_sigmaIdeal_eq`, `orbitIdeals_isPrime`, and Mathlib’s height facts, so it stays inside the algebraic tools you already have.
- Treat the Kostant-partition identification (bridge (b)) as a follow-on lemma: it relies on Gabriel-style orbit classification plus Lean bookkeeping between `intervalDirectSum (listOfPartition m)` and arbitrary corner-0 tuples. That matching is the genuinely new geometric input and deserves its own milestone rather than being smuggled into the D3 target.

**RLCT Payoff**
- The R2 payoff `rlct(lossDLN 0) = cCodim d 0 / 2` explicitly references `cCodim`. To state it honestly you must point Lean (or the paper exposition) to the bridge `codimRepCanonical (fibre d 0) = cCodim d 0`; otherwise the symbol `cCodim` remains an unexplained external quantity.
- However, for a *numerical* witness like `(2,2,2)` you can already combine `cCodim_d222_zero = 3` (once proved) with `codimRepCanonical (fibre d222 0) = 3` to certify the RLCT value in that concrete case. So: full bridge for the general theorem, concrete equality for the illustrative example.

**Difficulty Estimate**
- Bridge (a): ~120–180 LoC, medium friction. Most work is instantiating existing Mathlib lemmas (`height_eq_primeHeight`, finiteness of minimal primes) with the sigma-ideal data and managing `ℕ∞` ↔ `ℕ` casts. Expect a few auxiliary lemmas about infimums over finite sets and `Ideal.height` monotonicity.
- Bridge (b): easily 300 LoC+, likely multi-day. You must (i) formalise the bijection between corner-0 tuples and Kostant partitions in Lean, (ii) prove the corresponding orbits coincide, and (iii) transfer codimension data through that bijection. Each substep touches representation-theoretic infrastructure that is not yet abstracted, so plan it as a separate roadmap item (D4-level or preparatory expedition) rather than squeezing it into a 200–410 LoC module.

**Naming**
- Bridge (a) lemma: `codimRepCanonical_fibre_zero_eq_iInf_orbitCodim` (stresses it is a fibre-level codimension equality via an infimum over orbit closures).
- Bridge (b) lemma: `iInf_orbitCodim_zero_eq_cCodim` (made explicit that it matches the Kostant-partition infimum defining `cCodim`).
- Combined statement (once both bridges land): `codimRepCanonical_fibre_zero_eq_cCodim`. Keeping “fibre” in the name avoids suggesting a statement about the entire multiplication variety and honours the warning against overclaiming.

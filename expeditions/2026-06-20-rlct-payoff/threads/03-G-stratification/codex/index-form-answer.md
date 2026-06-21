**Recommendation.** Use **(A)** as the G2 headline theorem, and also export **(B)** as the `simp`/rewriting-friendly membership form. **Fact:** with the stated definitions, `⊆` is immediate by `M := A`, while `⊇` is the corner-rank inequality from `A ∈ orbitRankLocus M`. **Lean-ergonomics judgement:** (A) is the cleanest set-level stratification statement; (B) is what downstream proofs will actually destruct.

Also export auxiliary bricks:

- `orbitRankLocus_subset_productRankLocusLE_of_corner_le`
- `mem_productRankLocusLE_iff_exists_mem_orbitRankLocus`
- `orbitRankLocus_eq_of_rankPattern_eq`, or the corresponding iff, since G3 will quotient/collapse by rank patterns.

**For G3.** **Inference:** the Mathlib finite-union irreducible-components API is better served by a **canonical finite index** or finite set of rank patterns, not by the raw all-`M` union. But I would not force that into the G2 headline. Keep G2 mathematically transparent with (A)/(B), and let G3 introduce the finite/canonical indexing lemma needed to pass from the infinite-looking union to a finite family of distinct orbit closures. That keeps finiteness and maximality bookkeeping near the component argument where it matters.

**Trap check.** **Fact:** taking `M := A` does not make (A) vacuous; the reverse inclusion still uses the orbit-closure rank inequalities. **Inference:** it does hide the Gabriel-normal-form content if this theorem is advertised as “the Gabriel/Kostant stratification,” because the bare set equality over all tuples needs no normal forms and no finiteness. So the statement is correct and useful, but it should not be the only delivered formalization of the paper’s canonical stratification.

Yes, deliver the Gabriel-membership/normal-form lemma as a **separate named brick**. **Fact from the brief:** it is not logically required for the all-`M` set equality. **Lean-ergonomics judgement:** separating it is cleaner: G2 gets a robust union theorem, while later threads can use Gabriel to replace arbitrary tuples by canonical representatives, prove equality of orbit closures via rank patterns, and obtain the finite distinct family needed for maximal-component statements.
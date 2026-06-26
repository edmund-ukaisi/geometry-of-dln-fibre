# L6.4 / L1★ — orbit closure = rank locus, at the ideal level (Abeasis–Del Fra)

The determinantal rank locus `orbitRankLocus M` and the `G_d`-orbit `O_M` have the same vanishing
ideal — equivalently the same Zariski closure `Ō_M = orbitRankLocus M` — and that ideal is prime, so
the rank locus is an irreducible variety. Module: `lean/DLNFibre/Core/OrbitClosure.lean`.

---

> **Claim (L6.4 headline).** For a composable matrix tuple `M : Tuple d` over an infinite field, the
> vanishing ideal of the flattened determinantal rank locus `canonicalCoord '' orbitRankLocus M`
> equals the vanishing ideal of the orbit `O_M`. (So `Ō_M = orbitRankLocus M` as closed sets.)
>
> - **Lean:** `DLNFibre.Core.vanishingIdeal_orbitRankLocus_eq_orbitSet`
>   (`lean/DLNFibre/Core/OrbitClosure.lean` @ `f9ceea8`)
> - **Gloss.** `[Field k] [Infinite k]`; `M : Tuple d`. Then
>   `vanishingIdeal k (canonicalCoord d '' orbitRankLocus M) = vanishingIdeal k (orbitSet M)` in
>   `MvPolynomial (RepCoord d) k`. `orbitRankLocus M = {A | ∀ i ≤ j, rankPattern A i j ≤ rankPattern M
>   i j}` (the determinantal rank conditions); `orbitSet M = canonicalCoord '' (G_d · M)`.
> - **Proved.** Both inclusions of ideals, unconditionally over any infinite field. Easy `≤` is the
>   order-reversal of `O_M ⊆ orbitRankLocus M` (`vanishingIdeal_orbitRankLocus_le_orbitSet`, L6.3);
>   hard `≥` is the box-move degeneration: every rank-locus point lies in `Ō_M`
>   (`image_orbitRankLocus_subset_repClosure_orbitSet`), via the box-move chain `box_move_chain_of_le`
>   (L6.2c) composed with the per-move degeneration `Core.BoxMoveGeneral` (L6.1) through the
>   rank-pattern bridge and `G_d`-stability of the orbit closure.
> - **Assumed.** `[Infinite k]` (the polynomial-curve degeneration engine needs an infinite field).
> - **Cited.** none — the box-move generation (L6.2c), per-move degeneration (L6.1), complete invariant
>   (Cor 2.9), and Gabriel normal form are all proved in-repo and consumed here as lemmas.
> - **Deferred.** none for the ideal-level statement. (A `Set`-level `orbitRankLocus M = Ō_M` over an
>   algebraically closed field would follow from this + the Nullstellensatz; not stated here.)
> - **Status.** sorry-free

---

> **Claim (L1★, irreducibility of the rank locus).** Over an algebraically closed field, the vanishing
> ideal of the rank locus `canonicalCoord '' orbitRankLocus M` is prime — the rank locus is an
> irreducible variety.
>
> - **Lean:** `DLNFibre.Core.isPrime_vanishingIdeal_orbitRankLocus`
>   (`lean/DLNFibre/Core/OrbitClosure.lean` @ `f9ceea8`)
> - **Gloss.** `[Field k] [IsAlgClosed k]`; `M : Tuple d`. Then
>   `(vanishingIdeal k (canonicalCoord d '' orbitRankLocus M)).IsPrime`.
> - **Proved.** Primeness, from the L6.4 headline (rewrites the ideal to `vanishingIdeal (orbitSet M)`)
>   plus L1's `isPrime_vanishingIdeal_orbitSet` (the orbit is irreducible).
> - **Assumed.** `[IsAlgClosed k]` (inherited from L1; `IsAlgClosed → Infinite` supplies the L6.4
>   hypothesis).
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free

---

## Per-step crux (the one genuinely hard glue)

> **Lean:** `DLNFibre.Core.boxMoveStep_repClosure_subset` /
> `boxMoveStep_repClosure_realizer_subset` (`@ f9ceea8`).
> A single applicable box move `BoxMoveStep r r''` (the upper pattern `r` achievable, supported,
> diagonal `= d`) drops the orbit closure: `repClosure (orbitSet Tq) ⊆ repClosure (orbitSet Tp)` for
> any tuples realizing `r''`/`r`. Proof: integer→`Fin` box-coordinate extraction; the residual Kostant
> array `mRest = diffTri r − δ(a,e) − δ(c,b)` (split: `− δ(a,e)`) realized by `listOfArray`; the
> dimension cast `dg = d` via the diagonal `cumul` identity; the split / non-split geometric
> degeneration (`splitMove_/nonsplitMove_intervalDirectSum_mem_closure`) reconciled with the realizers
> by the rank-pattern bridge (`repClosure_orbitSet_eq_of_rankPattern_eq`) and `G_d`-stability
> (`orbitSet_subset_repClosure_orbitSet_of_canonical_mem`).

## Axiom footprint

`#print axioms` on both headlines and the per-step crux: `[propext, Classical.choice, Quot.sound]`
only — no `sorryAx`, no custom axioms. `scripts/sorries` = 0 across the whole library; `lake build`
green (2695 jobs).

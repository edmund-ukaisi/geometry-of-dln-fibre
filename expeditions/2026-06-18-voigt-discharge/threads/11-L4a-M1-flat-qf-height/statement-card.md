# Statement card — L4a-M1: flat + quasi-finite-at preserves prime height

> **Claim.** If `S` is a flat, Noetherian `R`-algebra (with `R` Noetherian) and `S` is `R`-quasi-finite
> at a prime `Q : Ideal S`, then `Q` and the prime `Q.under R` it lies over have equal height:
> `Q.height = (Q.under R).height`. Specialises to étale `S` (étale ⟹ flat + quasi-finite).
>
> - **Lean:** `DLNFibre.Core.Ideal.height_eq_under_of_flat_quasiFiniteAt`
>   (`lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean` @ `602bcb5ac459d2b5e749ed47147768b1f3a819d7`)
> - **Gloss.** For `[CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
>   [Module.Flat R S]` and a prime `Q : Ideal S` with `[Algebra.QuasiFiniteAt R Q]`, the Krull height
>   of `Q` (length of the longest chain of primes below it) equals the height of its contraction
>   `Q.under R = Q.comap (algebraMap R S)`. The fibre of `Spec S → Spec R` over `Q.under R`
>   contributes nothing to the height of `Q`.
> - **Proved.**
>   - `Ideal.height_eq_under_of_flat_quasiFiniteAt` — the headline, unconditionally (within the four
>     listed typeclass hypotheses).
>   - `fibre_height_eq_zero_of_quasiFiniteAt` — the load-bearing step: for `[QuasiFiniteAt R Q]`,
>     the image of `Q` in the fibre ring `S ⧸ (Q.under R)·S` has height `0`. Proof: that image is a
>     **minimal prime** of the fibre — any prime `K` below it comaps to a prime `K'` of `S` with
>     `(Q.under R)·S ≤ K' ≤ Q` and `K'.under R = Q.under R`, so `K' = Q` by
>     `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`; minimality then gives height `0` via
>     `Ideal.primeHeight_eq_zero_iff`. (No `[IsNoetherianRing]`/`[Flat]` needed for this step.)
>   - `Ideal.height_eq_under_of_etale` — corollary for `[Algebra.Etale R S]`; `Module.Flat` and
>     `Algebra.QuasiFiniteAt` are both discharged by instance inference from `Etale`.
>   - Non-vacuity: an in-file `example` instantiates `R = S` (identity algebra, flat + module-finite
>     over itself), where the statement is `Q.height = Q.height`.
> - **Assumed.** `[IsNoetherianRing R]` and `[IsNoetherianRing S]` (both required by the going-down
>   height-additivity lemma `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, `@[stacks 00ON]`,
>   whose file-level context carries `[IsNoetherianRing R]`); `[Module.Flat R S]` (gives
>   `Algebra.HasGoingDown` by `Algebra.HasGoingDown.of_flat`); `[Algebra.QuasiFiniteAt R Q]`
>   (= `Algebra.QuasiFinite R (Localization.AtPrime Q)`). These are the minimal hypotheses for the
>   stated generality; the downstream M2 use (`R = k[x₁..xₙ]`, `S` étale) satisfies all four.
> - **Cited.** none — every step is a named Mathlib lemma reproved/applied here, not an external
>   analytic interface. Mathlib lemmas used: `Algebra.HasGoingDown.of_flat`,
>   `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (00ON),
>   `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`, `Ideal.primeHeight_eq_zero_iff`,
>   `Ideal.map_isPrime_of_surjective`, `Ideal.comap_map_of_surjective`,
>   `Ideal.map_comap_of_surjective`, `Ideal.{map_comap_le, le_comap_map, ker_le_comap, mk_ker}`,
>   `Algebra.Etale`/`Smooth.flat`, `Module.Finite ⟹ QuasiFinite`.
> - **Deferred.** none. (This module is the M1 brick only; the smooth ⟹ regular assembly that
>   consumes it lives in M2/M3 and is out of scope here.)
> - **Status.** sorry-free; axioms `[propext, Classical.choice, Quot.sound]`. Awaiting reviewer
>   fidelity check.

## Kill-condition outcome

The controller-watched kill-condition was: *L4a balloons if fibre-prime-height-0 fails to assemble
from the present quasi-finite API.* It **did NOT fire.** The fibre-height-0 step assembles directly:
`Algebra.QuasiFiniteAt.eq_of_le_of_under_eq` (only needs `QuasiFiniteAt R Q`) discharges
"`Q` minimal over `(Q.under R)·S`", and `Ideal.primeHeight_eq_zero_iff` converts minimality to
height `0`. The Artinian-fibre route was not needed — the `eq_of_le_of_under_eq` path is shorter and
self-contained. The étale route's height-preservation brick is therefore in honest Lean.

## What fought back (notes for M2/M3)

- The going-down lemma `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` carries a **file-level
  `[IsNoetherianRing R]`** (not only `[IsNoetherianRing S]`), so the headline must assume `R`
  Noetherian. Confirmed by reading the section variables, not the lemma line alone.
- `comap_map_of_surjective` yields `I ⊔ comap f ⊥` (not `I ⊔ RingHom.ker f`); bridge with
  `RingHom.ker_eq_comap_bot` before applying `Ideal.mk_ker`.
- A `let f := Ideal.Quotient.mk pS` triggers a `whnf` heartbeat timeout (the quotient unfolds);
  `set pS … with` + `set f … with` keeps both opaque and the proof fast (~5 s).
- The `minimalPrimes` membership goal unfolds to `Minimal`, whose minimality obligation is
  `J ≤ K` (given `K ≤ J`), not `K = J` — prove the equality and take `.ge`.

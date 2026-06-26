# C1 design consult — localization recovers a component in a reduced ring

## Context (Lean 4 + Mathlib v4.29)
I want a reusable commutative-algebra lemma. Setting:
- `R` a commutative ring, REDUCED (`IsReduced R`), Noetherian-ish if helpful.
- `R` has finitely many minimal primes `{I_j}` (its irreducible components).
- A prime ideal `q` of `R` with `I_M ⊆ q` for a distinguished minimal prime `I_M`,
  and `I_j ⊄ q` for every OTHER minimal prime `j ≠ M`.
  (Geometrically: `q` is a generic point of the component `V(I_M)`, sitting off all other components.)

## Goal
Construct a `k`-algebra (or just ring) isomorphism
  `Localization.AtPrime R q  ≃  Localization.AtPrime (R ⧸ I_M) (q.map (Ideal.Quotient.mk I_M))`.
Then I'll use `Algebra.FormallySmooth.iff_of_equiv` to transfer `IsSmoothAt k q (R)` from the
quotient-ring side (which I prove smooth via orbit-closure machinery on `R/I_M`, a domain).

## My intended mechanism
The quotient map `π : R → R/I_M` has kernel `I_M`. I claim `π` becomes an iso after localizing at `q`:
i.e. `Localization.AtPrime R q ≃ Localization.AtPrime (R/I_M) (π(q))`.
Equivalently: the localization map `R_q → (R/I_M)_{π q}` is an iso, because `I_M` maps to `0` in `R_q`.

Why does `I_M` die in `R_q`? In a reduced ring `⋂_j I_j = nilradical = ⊥ = 0`.
For `x ∈ I_M`: I want `s ∉ q` with `s·x = 0` in `R`, so `x/1 = 0` in `R_q`.
Take `s ∈ (⋂_{j≠M} I_j) \ q` — exists by prime avoidance since `I_j ⊄ q` for `j≠M` and there are
finitely many. Then `x·s ∈ I_M ∩ ⋂_{j≠M} I_j = ⋂_j I_j = ⊥ = 0`. So `s·x = 0`, `s ∉ q`. Done.

## Questions
1. Is this mechanism correct? Any gap (e.g. do I need `s` to avoid q AND the product to land in ALL minimal primes)?
2. Cleanest Mathlib route to "I_M maps to 0 in the localization ⟹ the localization factors as an iso through R/I_M".
   Candidates: `IsLocalization.AtPrime` is `R_q`; I want `(R/I_M)_{πq}` to ALSO be an `IsLocalization` of `R` at `q.primeCompl`
   (since the kernel I_M ⊆ q dies). Is there a Mathlib lemma "localization away from an ideal contained in the
   complement-of-q-killing-set"? Or should I build the iso `R_q ≃ (R/I_M)_{πq}` directly via `IsLocalization.ringEquivOfRingEquiv`
   / a universal-property argument: `(R/I_M)_{πq}` IS a localization of `R` at `q.primeCompl` (composite map R → R/I_M → (R/I_M)_{πq}
   inverts q.primeCompl and is `IsLocalization` because the kernel dies)?
3. Is "prime avoidance over finitely many minimal primes" (`Ideal.subset_union_prime` / the `biUnion` form) the right tool,
   and is `minimalPrimes_finite` available for Noetherian rings to get finiteness?
4. Alternative: is there an even slicker route using `IsLocalization.AtPrime.prime_unique_of_minimal` or the fact that
   `R_q` has a unique minimal prime so its nilradical-quotient is already a domain? I specifically need the iso to the
   quotient-ring localization, not just "R_q is local".

Please give the cleanest Mathlib-idiomatic proof skeleton (lemma names that exist in v4.29 if you can recall them),
flag any mechanism gap, and rate the difficulty (line count).

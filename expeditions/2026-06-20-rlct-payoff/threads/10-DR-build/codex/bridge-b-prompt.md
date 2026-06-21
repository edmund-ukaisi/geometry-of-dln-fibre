# Bridge (b) tractability — does codim-min of corner-0 orbits = cCodim reduce cleanly? (Lean4/Mathlib v4.29)

## Setup
`cCodim d 0 h := (kostantPartitions d 0).inf' h (fun m ↦ codimForm N (extendℤ m))` where
`kostantPartitions d 0 : Finset (Fin(N+1)×Fin(N+1) → ℕ)` is the Finset of arrays m with
m_{ij}=0 off i≤j, ∑_{i≤k≤j} m_{ij} = d_k at every k, and m(0,last)=0.

LANDED (over [IsAlgClosed k][CharZero k]):
- `cCodim_eq_inf_geomCodim : cCodim d 0 h = (kostantPartitions d 0).inf' h (fun m ↦ ((codimRepCanonical (orbitRankLocus (intervalDirectSum (listOfPartition m)))).toNat : ℤ))`.
- `codimRepCanonical_orbitRankLocus_eq_codimForm (L) : ((codimRepCanonical (orbitRankLocus (intervalDirectSum L))).toNat : ℤ) = codimForm N (multiplicityArray L)`.
- orbit↔Kostant correspondence: `kostantArrayOfRank (rankFn M)` is the Kostant array (SuppArray ℤ) of a tuple M;
  `realizer m hm : Tuple` realizes a CMPlus array; `orbitCMPlusEquiv : Quotient orbitSetoid ≃ {m // CMPlus d m}`;
  `cMPlus_iff_mem_image`. `kostantPartitions` uses Fin×Fin→ℕ encoding; the correspondence uses SuppArray (N:ℤ) ℤ + CMPlus.
- `orbitRankLocus_eq_of_rankPattern_eq`: orbit closures equal when rank patterns agree.

## Bridge (a) (I am proving this, ~120-180 LoC):
`codimRepCanonical (fibre d 0) = ⨅ over corner-0 orbit family of codimRepCanonical (orbitRankLocus M)`
via height(sigmaIdeal 0)=inf over minimal primes (minimalPrimes_sigmaIdeal_eq) + height_eq_primeHeight +
exists_minimalPrimes_le/height_mono to drop to all members.

## Question (decision: attempt bridge (b) now, or defer it cleanly?)
To get `codimRepCanonical (fibre d 0) = cCodim d 0` I must show bridge (a)'s RHS infimum
`⨅_{M : (mult M).rank ≤ 0} codimRepCanonical(Ō_M)` equals the cCodim `inf'_{m ∈ KP}` above.
Both are infima of codimForm-values over corner-0 orbit closures. The hard sub-step is matching the
INDEX SETS / VALUE SETS:
  S₁ = {codimRepCanonical(Ō_M).toNat : M corner-0 tuple}   (an ⨅ over a Set/Type)
  S₂ = {codimForm N (extendℤ m) : m ∈ kostantPartitions d 0}   (an inf' over a Finset)
and these need TWO encoding bridges: (i) extendℤ (Fin×Fin→ℕ) ↔ multiplicityArray/kostantArrayOfRank
(SuppArray ℤ), (ii) every corner-0 tuple's orbit = realizer of some KP element and vice versa.

1. Is this index/value-set match a ~80-150 LoC job given the landed correspondence, or a multi-day
   encoding-reconciliation (SuppArray ℤ ↔ Fin×Fin→ℕ, CMPlus ↔ kostantPartitions-membership)?
2. Concretely for (2,2,2): is there a SHORTER route to `codimRepCanonical (fibre d222 0) = 3`
   that bypasses the general set-match — e.g. exhibit the specific min-codim orbit M₀ (the maximal
   corner-0 orbit) with codimRepCanonical(Ō_{M₀})=3 AND show every corner-0 Ō_M has codim ≥ 3?
   The "≥ 3" lower bound over ALL corner-0 orbits is the crux — is it any cheaper than bridge (b)?
3. If bridge (b) is multi-day: confirm the honest deliverable is R2 stated against
   `codimRepCanonical (fibre K d 0)` (the genuine geometric codim of the zero-product fibre), with
   `= cCodim`/`= C` named as the DEFERRED bridge (b), NOT in the R2 theorem name. Is that the right
   precision call, or does it leave the payoff too weak to be worth landing?
Keep it terse. I need a build/scope decision, not prose.

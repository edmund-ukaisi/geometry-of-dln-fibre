# Thread 04 — Phase G3 + θ (irreducible components of `Σ̄^r` and the count `θ`) — statement card

Module: `lean/DLNFibre/Core/SigmaComponents.lean` (318 LoC, sorry-free, axiom-clean) @ `99eafe0`.
Build: whole `DLNFibre` library green (3014 jobs); `scripts/sorries` = 0.
Axioms (all headlines, via `#print axioms`): `[propext, Classical.choice, Quot.sound]`.

**SPIKE VERDICT: architecture clean.** The recon-recommended PrimeSpectrum-via-intersection-ideal
route closed without obstruction (see §SPIKE). G3 (components = maximal `Ō_M`) **landed firmly**.
θ landed the **top-dimensional ⟹ component** half (min-codim ⟹ component, the load-bearing geometric
content); the COUNT `numTop = θ` has a precisely-scoped gap (the Kostant-partition ↔ orbit-ideal
count-bijection), reported below — NOT sorry-patched.

---

## SPIKE (the architecture gate)

> **`minimalPrimes_sInf_of_finite_of_isPrime`** (general algebra, `[CommRing R]`):
> for a finite family `s : Set (Ideal R)` of prime ideals,
> `(sInf s).minimalPrimes = {p | p ∈ s ∧ ∀ q ∈ s, q ≤ p → p ≤ q}` — the minimal primes of `sInf` of a
> finite family of primes are exactly the **inclusion-minimal members**. Via `IsPrime.inf_le'`
> (prime avoidance over `Finset.inf`, through `Set.Finite.toFinset` + `Finset.inf_id_eq_sInf`).

This pins the `minimalPrimes (⨅ finite primes)` ⟹ "the minimal members" lemma the brief flagged as the
architecture risk. It compiled cleanly; the architecture is confirmed (no point-space union-algebra
needed — work Spec-side on `PrimeSpectrum (MvPolynomial (RepCoord d) k)`). The Mathlib bricks
(`Ideal.minimalPrimes.equivIrreducibleComponents`, `Ideal.height_strict_mono_of_is_prime`) `#check`ed
in a scratch and were consumed directly.

---

## Headline G3 — irreducible components of `Σ̄^r` are the maximal `Ō_M`

> **Claim.** The irreducible components of the closed rank-`≤ r` product locus `Σ̄^r` are exactly the
> **maximal** orbit closures `Ō_M = orbitRankLocus M` (orbit-closure / rank-pattern order) among the
> corner-`≤ r` family (Le Halleur–Rimányi 2024, Cor 4.4 — the maximal reading, settled by the worked
> examples).
>
> - **Lean (minimal-primes form):** `DLNFibre.Core.minimalPrimes_sigmaIdeal_eq`
>   (`[IsAlgClosed k]`): `(sigmaIdeal d r).minimalPrimes = {p | p ∈ orbitIdeals d r ∧ p
>   inclusion-minimal}`, where `sigmaIdeal d r := vanishingIdeal (canonicalCoord d '' Σ̄^r)` and
>   `orbitIdeals d r := {vanishingIdeal (Ō_M) | (mult d M).rank ≤ r}`.
> - **Lean (irreducible-components order-iso):** `DLNFibre.Core.irreducibleComponents_sigmaIdeal_equiv`:
>   `{inclusion-minimal orbit ideals} ≃o (irreducibleComponents (zeroLocus (sigmaIdeal d r)))ᵒᵈ`
>   (Mathlib `Ideal.minimalPrimes.equivIrreducibleComponents`).
> - **Lean (orbit-closure order = reversed orbit-ideal order):**
>   `DLNFibre.Core.vanishingIdeal_orbitRankLocus_le_iff`:
>   `vanishingIdeal Ō_M ≤ vanishingIdeal Ō_M' ↔ canonicalCoord '' Ō_M' ⊆ canonicalCoord '' Ō_M`
>   — so "inclusion-minimal orbit ideal" `=` "maximal orbit closure", making the "maximal `Ō_M`"
>   reading load-bearing, not prose.
> - **Proved.** The minimal-primes characterisation, the components order-iso, and the order-reversal,
>   over `[Field k]` (+ `[IsAlgClosed k]` for the prime-ideal facts). The chain: G2 set union
>   `Σ̄^r = ⋃_M Ō_M` (LANDED) → `vanishingIdeal` turns it into `sigmaIdeal = sInf orbitIdeals`
>   (`sigmaIdeal_eq_sInf_orbitIdeals`) → the SPIKE gives the minimal primes = inclusion-minimal
>   members → `equivIrreducibleComponents` gives the topological components.
> - **Assumed.** `[Field k]` (uniform); `[IsAlgClosed k]` for primality of `vanishingIdeal Ō_M`
>   (`Core.OrbitClosure.isPrime_vanishingIdeal_orbitRankLocus`). No `[CharZero k]` for G3 (it is a
>   prime-spectrum / Nullstellensatz statement, not a Voigt-codim one).
> - **Cited.** none.
> - **Deferred.** The COUNT `numTop = θ` (the count-bijection gap, below). The DLN-side
>   fibre/loss/RLCT readings (Phases D/R).
> - **Faithfulness anchor.** The components are stated for `zeroLocus (sigmaIdeal d r)` on
>   `PrimeSpectrum`, where `sigmaIdeal d r = vanishingIdeal (canonicalCoord d '' Σ̄^r)` — the genuine
>   vanishing ideal of the flattened `Σ̄^r`. The Spec incarnation is the standard one (the point-space
>   `MvPolynomial.zeroLocus` lacks the union/component API at this pin); the bridge to `Σ̄^r` is the
>   explicit `sigmaIdeal_eq_sInf_orbitIdeals` (G2-derived).

This closes **step (ii)** of the `Core.CThetaGeometric` aggregate roadmap ("its orbit stratification
`Σ^r = ⋃_M Ō_M`" → its components).

---

## Headline θ-A — top-dimensional components = minimal-codimension orbit closures

> **Claim.** A corner-`≤ r` orbit closure `Ō_M` of **minimal geometric codimension** among the
> corner-`≤ r` family is an irreducible component of `Σ̄^r` (the geometric "min-codim is
> top-dimensional, hence a component" content).
>
> - **Lean:** `DLNFibre.Core.orbitRankLocus_minCodim_mem_minimalPrimes` (`[IsAlgClosed k]`):
>   `(mult d M).rank ≤ r` + `(∀ M' corner ≤ r, codimRepCanonical (Ō_M) ≤ codimRepCanonical (Ō_M'))`
>   `⟹ vanishingIdeal (Ō_M) ∈ (sigmaIdeal d r).minimalPrimes`.
> - **Mechanism.** The strict drop of `Ideal.height` under proper prime inclusion
>   (`Ideal.height_strict_mono_of_is_prime`, with `FiniteHeight` from the new instance
>   `finiteRingKrullDim_mvPolynomial_repCoord`): a non-maximal `Ō_M` sits strictly inside another
>   corner closure `Ō_M'`, so `vanishingIdeal Ō_M' ⊊ vanishingIdeal Ō_M`, forcing
>   `codim Ō_M' < codim Ō_M` — contradicting minimality. Hence min-codim ⟹ maximal ⟹ component.
> - **Supporting brick.** `codimRepCanonical_orbitRankLocus_eq_height` (`rfl`): the LANDED Voigt codim
>   `codimRepCanonical (Ō_M)` IS `(vanishingIdeal Ō_M).height` — the height feeding the count.
> - **Proved.** Unconditional given the hypotheses, over `[Field k] [IsAlgClosed k]`.

---

## The θ COUNT gap (precisely scoped — NOT closed, NOT sorry-patched)

The brief's full θ deliverable is `θ = numTop = #top-dimensional irreducible components`. θ-A delivers
the **direction** (min-codim ⟹ component). The remaining COUNT equality
`numTop d r = (top-dim components).card` needs a **bijection**

    {Kostant partitions m attaining min codimForm}  ↔  {min-height minimal primes of sigmaIdeal}

with three sub-pieces, none reachable from the strict-mono brick alone:

1. **Surjectivity onto components via Kostant reps.** Every minimal prime is `vanishingIdeal Ō_M` for
   some *Kostant-partition* representative `M = ⊕ M_{ab}` (not merely some tuple). The input is the
   LANDED Gabriel brick `Core.SigmaStratification.exists_orbitRankLocus_mem_rankPattern_eq` + the
   partition realizer `Core.CThetaGeometric.listOfPartition` / `intervalDirectSum`; the missing glue
   is "every corner-`≤ r` rank pattern is realised by a corner-`≤ r` Kostant partition" as a
   surjection onto the family.
2. **Injectivity partitions → orbit ideals.** Distinct corner-`≤ r` Kostant partitions give distinct
   orbit ideals (distinct rank patterns ⟹ distinct closures ⟹, over `[IsAlgClosed]`, distinct prime
   ideals). Needs the rank-pattern ↔ partition bijection at the *ideal* level.
3. **min-height ↔ min-codimForm.** `(vanishingIdeal Ō_{⊕m}).height = codimForm N (extendℤ m)` is
   LANDED (`Core.CThetaGeometric.codimForm_extendℤ_eq_geomCodim` + the `rfl`
   `codimRepCanonical_orbitRankLocus_eq_height`), so the height-minimisers ARE the `codimForm`-minimisers
   `= numTop`'s minimisers — but transporting the COUNT needs the bijection (1)+(2) restricted to the
   minimisers.

**Single missing lemma (the count-bijection):** a `Finset`-card-preserving bijection between
`(kostantPartitions d r).filter (codimForm = cCodim)` and
`(sigmaIdeal d r).minimalPrimes.filter (height = cCodim)` (top-dimensional components). Estimate:
~150–250 LoC (consumes the LANDED partition realizer + Gabriel brick + the height = codimForm bridge;
the work is the injectivity/surjectivity bookkeeping the recon flagged as the time-sink). This is the
honest **roadmap** item; G3 + θ-A are the bedrock it stands on.

---

## Supporting bricks (same module, same SHA)

- `minimalPrimes_sInf_of_finite_of_isPrime` — the SPIKE (general algebra).
- `orbitIdeals` / `orbitIdeals_finite` — the finite family of prime orbit ideals (finiteness via
  `rpBounded`, the padded bounded rank pattern, a finite-type invariant the family map factors
  through, `familyMap_factorsThrough_rpBounded` + `Function.factorsThrough_iff`).
- `sigmaIdeal` / `sigmaIdeal_eq_sInf_orbitIdeals` — the aggregate ideal of `Σ̄^r` and the G2 bridge.
- `orbitIdeals_isPrime` — every family member is prime (`[IsAlgClosed k]`).
- `finiteRingKrullDim_mvPolynomial_repCoord` — `instance`: `FiniteRingKrullDim` of the coordinate ring
  (`= Nat.card`), giving `FiniteHeight` for the strict-mono brick.

## Non-vacuity witness in-file

`(2,2,2)`, `r = 0` (zero-product locus) over `AlgebraicClosure ℚ` (`[IsAlgClosed] [CharZero]`):
the zero tuple lies in `Σ̄^0` (`zero_mem_productRankLocusLE_d222`, product `0`), so
`orbitIdeals d222 0` is nonempty (`orbitIdeals_d222_zero_nonempty`); the bridge
`sigmaIdeal = sInf orbitIdeals` and the G3 minimal-primes characterisation fire on it (two `example`s).
This is the geometric side of the LANDED combinatorial `Core.CTheta.numTop_d222_zero = 1` (three
maximal Kostant partitions ⟹ three components, one top-dimensional); the COUNT match is the gap above.

## Status

sorry-free + axiom-clean; **awaiting reviewer fidelity AUDIT** (does the Lean statement match the
paper's Cor 4.4 components claim? is the θ-A scoping honest, the count gap correctly named?). Codex
decorrelation was attempted but Codex is non-functional in this environment (`codex doctor` /
`codex exec` time out, exit 144 / 143) — flagged for the controller; the reviewer is the decorrelation.

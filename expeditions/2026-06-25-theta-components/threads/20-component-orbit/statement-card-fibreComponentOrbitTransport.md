# Statement card — `Core.FibreComponentOrbitTransport` (thread 20, task #128/#119, C2(a) RESOLVED)

**Status:** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`. Module built standalone
(3085 jobs); whole library green (3790, module not yet in `DLNFibre.lean` — controller wires it).
Module: `lean/DLNFibre/Core/FibreComponentOrbitTransport.lean`. Codex red-team PASS (soundness).

## Headline — generic smoothness of the reduced DLN fibre is FULLY UNCONDITIONAL

```lean
theorem isSmoothAt_sweepFibre_component [IsAlgClosed k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hImin : I ∈ minimalPrimes (sweepFibreRing k d r hp hq)) :
    haveI : I.IsPrime := hImin.1.1
    Algebra.IsSmoothAt k I
```
English: the reduced fibre coordinate ring `sweepFibreRing` is smooth (over `k`) at the generic point
of **every irreducible component** `I` — no open hypothesis, no orbit iso, no chart. Stronger than
top-dimensionality (works for all minimal primes; Codex noted the name could even drop "top").

- `isSmoothAt_sweepFibre_topComponent` — the top-dim specialisation (`I ∈ TopDimMinPrimes`), the
  precise C2(a) deliverable thread-17's chain consumed as its one open input.
- `exists_isSmoothAt_chartDsig_unconditional` — composes the discharged input with thread-17's
  `isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre`: the source pivot chart `Away (chartDsig …)` is
  smooth on a basic open, fully unconditionally.

## The route (why no variety iso `e` is needed)

The thread-17 reduction asked for `sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M`; thread-20 found that target
dimensionally impossible, and the dimension-correct `≃ MvPolynomial η (orbitRing M)` has cancellation
hazards. **Smoothness needs neither**: a fibre component `sweepFibreRing ⧸ I` is a finitely-presented
`k`-algebra **DOMAIN** (`I` prime), and over the algebraically-closed (⟹ perfect) field `k` any such
domain is generically smooth — the standard "reduced finite type over a perfect field is generically
smooth on every component". So `sweepFibreRing ⧸ I` is `IsSmoothAt k ⊥`; the C1 bridge
(`LocalizationAtComponent.isSmoothAt_minimalPrime_of_isSmoothAt_quotient`, sound because at the
generic point `I` the other components — distinct minimal primes incomparable to `I` — do not meet)
lifts that to `IsSmoothAt k I` of the reducible `sweepFibreRing`.

The reducibility of `sweepFibreRing` was the obstruction thread-16/17 navigated; quotienting to the
component (a domain) FIRST removes it.

## Supporting results (all unconditional, reusable)
- `mem_smoothLocus_iff_isSmoothAt` — the abstract scheme↔ring smooth-point dictionary for any fp
  `k`-algebra (the `OrbitSmooth` dictionary, freed of the orbit ring; only `k` a field used).
  Spin-out candidate.
- `isSmoothAt_bot_of_finitePresentation_domain` — a fp domain over alg-closed `k` is `IsSmoothAt k ⊥`
  (generic smoothness, `dense_smoothLocus_of_perfectField` + `isSmoothAt_bot_of_isSmoothAt`).
- `comap_algebraMap_specHom_eq_bot`, `specHom_localRingHom_formallySmooth_iff` (dictionary internals).

## Soundness (Codex red-team PASS, persisted `codex/redteam-answer.md`)
No flaw. Step 2 (generic smoothness) valid — `PerfectField` does real work (rules out char-p
inseparability), `IsAlgClosed ⟹ PerfectField`, no hidden geometric-reducedness gap. C1 bridge sound &
non-circular. Crux (Q3): at a generic point `I` the ambient reducible scheme does NOT see other
components (`J ≤ I` impossible for distinct minimal primes), so `R_I = (R⧸I)_⊥` — exactly the C1
lemma. Bottom line: orbit/chart machinery was unnecessary FOR SMOOTHNESS; still relevant for
component-orbit labeling, the orbit×affine component description, θ-count transport, and the
non-reduced scheme-theoretic fibre.

## Aggregator import line (for the controller)
`import DLNFibre.Core.FibreComponentOrbitTransport`
(after `DLNFibre.Core.FibreComponentOrbit`; new transitive import: `DLNFibre.Core.OrbitSmooth` —
already in the library).

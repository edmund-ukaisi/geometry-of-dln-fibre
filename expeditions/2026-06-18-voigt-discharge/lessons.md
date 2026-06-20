# lessons.md — voigt-discharge (append-only)

- **`codimRep` is point-set CA, but Mathlib's dimension/irreducibility theory is on `PrimeSpectrum`.**
  `codimRep = Ideal.height (MvPolynomial.vanishingIdeal (point set))`. Every dim/codim/irreducible theorem
  lives on `PrimeSpectrum`/`Spec`. So a Nullstellensatz bridge (point set ↔ radical ideal ↔ closed subscheme)
  is mandatory and **forces `[IsAlgClosed k]`**. (recon 01)
- **`orbitRankLocus` is the rank locus (`rankPattern ≤`), not the orbit closure.** `orbitRankLocus = Ō_M`
  (Thm 3.8) is Cited and therefore *in* the zero-cited target. Don't assume it; it's L6. (recon 01)
- **`IsCatenary` is 0% in Mathlib** (verified zero hits); no `height + coheight = dim`, no `dim = trdeg`, no
  `IsEquidimensional`. The height–dimension formula (L5) is the dominant build risk; the Höhensatz gives only
  `height ≤ #gens`. Size it before committing the build shape. (recon 01 + Codex, independent)
- **Mathlib AG is no longer the 2026-06-17 "desert."** `MvPolynomial.ringKrullDim_of_isNoetherianRing`
  (free `dim Rep`), `RingEquiv.height_comap`/`height_map` (height transport — OrbitCodim docstring now stale),
  `dense_smoothLocus_of_perfectField` (scheme generic smoothness), `smooth_of_grpObj_of_isAlgClosed` (2026
  group-scheme smoothness) all present — but scheme-level, so unusable until `G_d`/orbit are modelled
  compatibly. The schemes-vs-concrete-affine choice (L1–L3) is a real fork. (recon 01)
- **Seat discipline (carried from the c-theta sprawl):** bounded named seats reused across layers, stood down
  explicitly at close. Synchronous subagents don't self-terminate; per-task names pile up.
- **`Order.krullDim_le_of_strictComono_and_surj` is the wrong tool for `dim A ≤ dim S` of an integral
  extension** — its `comap a < comap b → a < b` order-*reflection* hypothesis is FALSE (counterexample
  `k[x] ↪ k[x]×k[x]`: incomparable primes over a comparable pair; Codex-confirmed). Correct route: direct
  going-up chain lift (`RelSeries.inductionOn'` + `exists_ideal_over_prime_of_isIntegral`), injectivity entering
  only at the chain base (`comap ⊥ = ⊥`). This idiom compiles at our v4.29 pin and is reused for L5.6. (thread 03)

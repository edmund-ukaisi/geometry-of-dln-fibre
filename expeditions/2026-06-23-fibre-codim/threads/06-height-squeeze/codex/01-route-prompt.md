# Codex consult — F2 height-squeeze route + reducibility (Lemma 4.6 codim identity)

## Context
Lean 4 + Mathlib v4.29 formalisation. Network-free commutative-algebra engine. Field `K`,
`[IsAlgClosed K] [CharZero K]`.

Objects (all LANDED in Lean):
- `Rep_d` = composable matrix tuples for dim vector `d : Fin (N+1) → ℕ`. Ambient coordinate ring
  `R_total = MvPolynomial (RepCoord d) K`, with `card(RepCoord d) = Σ_i d_{i+1} d_i =: D` (= dim Rep_d).
- `mult : Rep_d → Mat_{d_N, d_0}`, the ordered matrix product. Defined over any CommRing.
- `Σ̄^r = productRankLocusLE d r = {A | rank(mult A) ≤ r}`, a CLOSED subvariety (GL-stable, finite
  union of orbit closures). LANDED: `codimRepCanonical(Σ̄^r) = cCodim d r =: C` (Brick A), via
  `sigmaIdeal = sInf (orbitIdeals)`, minimalPrimes = inclusion-minimal orbit ideals.
- `fibre d B = mult⁻¹(B) = {A | mult A = B}`. For `B` of EXACT rank `r`, `0<N`, `r ≤ d_k' ∀k'`.
- `multComap : R_target → R_total` the K-algebra comorphism of `mult`, where
  `R_target = MvPolynomial (Fin d_N × Fin d_0) K`. LANDED (F1):
  - `vanishingIdeal(canonicalCoord '' fibre) = radical(fibreGenIdeal)`,
  - `fibreGenIdeal = Ideal.map multComap (maxIdealOfPoint B)`, where `maxIdealOfPoint B = span{X_{rc} - B_{rc}}`
    (the maximal ideal of the point B in R_target).
- `codimRepCanonical Z = Ideal.height (vanishingIdeal (canonicalCoord '' Z))` (height = iInf over
  minimal primes).

## The TARGET (the geometric content of Lehalleur–Rimányi Lemma 4.5/4.6)
`codimRepCanonical (fibre d B) = codimRepCanonical (Σ̄^r) + r·(d_0 + d_N − r)`
  i.e. `height(vanishingIdeal(fibre)) = C + r(d_0+d_N−r)`.

The PAPER proves this via differential geometry: `mult : Σ^r → Mat^{rk=r}` (EXACT rank r,
locally closed) is a locally trivial fibre bundle over the smooth orbit `Mat^{rk=r}` (a single
GL_{d_N}×GL_{d_0} orbit), via local sections of the smooth submersion `G_out → Mat^{rk=r}` and
G-equivariance. Hence dim Σ^r = dim(fibre) + dim Mat^{rk=r}, with dim Mat^{rk=r} = r(d_0+d_N−r).
This bundle/Lie-group machinery is ABSENT from Mathlib v4.29 — we must find an ALGEBRAIC route.

## What Mathlib v4.29 HAS (confirmed by rg / reading)
- `Ideal.height_le_card_of_mem_minimalPrimes_span` : Krull height theorem — a minimal prime over a
  span of c elements has height ≤ c. (UPPER bound on height = codim.)
- `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown [IsNoetherianRing S] [Algebra.HasGoingDown R S]`
  (p : Ideal R)[prime] (P : Ideal S)[prime][P.LiesOver p] :
    `P.height = p.height + (P.map (Quotient.mk (p.map algebraMap))).height`
  — fibre-dimension ADDITIVITY along going-down. Going-down holds for FLAT (Module.Flat ⟹ HasGoingDown),
  and for integral ext of integrally-closed domain.
- `Ideal.height_le_height_add_of_liesOver` : the ≤ direction WITHOUT going-down.
- LANDED engine: `affine_domain_height_add_ringKrullDim_quotient_eq` (equidimensionality: for A = R/I a
  finite-type DOMAIN over a field and prime p of A, `height p + dim(A/p) = dim A`), and the catenary
  bridge `height(vanishingIdeal Z) + varietyDim Z = card σ` for `vanishingIdeal Z` PRIME (per-component).
- LANDED: `varietyDim(Mat^{rk≤r}) = r(n+m−r)` (DeterminantalStratumDim, N=1 case).

## The DIFFICULTIES I see (please adjudicate)
1. **mult is NOT flat / NOT going-down globally.** Fibre dim jumps as rank drops, so I cannot apply
   `height_eq_height_add_of_liesOver_of_hasGoingDown` to the comorphism `multComap : R_target → R_total`
   at the closed point `m_B`. The bundle is flat only over the EXACT-rank locus `Mat^{rk=r}` (locally
   closed). Is there a clean algebraic way to capture "restrict to Σ^r where it's flat" WITHOUT
   locally-closed-subscheme machinery (which is heavy in Mathlib v4.29)?
2. **Reducibility.** `Σ̄^r` (and the fibre) is reducible when θ>1. `codimRepCanonical = height = iInf
   over minimal primes`. Brick A pinned Σ̄^r minimal primes = orbit ideals. For the FIBRE, what are the
   minimal primes, and how do their heights relate to (orbit-ideal heights of Σ̄^r) + shift?
   The bundle should match fibre-components ↔ Σ̄^r-components with codim shifted by +r(d_0+d_N−r).
3. **The thread's proposed sandwich** is: lower bound height≥ via "fibre cut by multComap-pullbacks of
   B's coords + Krull, count equations to the shift"; upper bound height≤ via affine-domain
   equidimensionality per component. But Krull gives height ≤ #gens (UPPER), and #gens = d_N·d_0 ≫ shift,
   so a bare Krull count seems far too weak AND the wrong direction for a lower bound. Is the thread's
   sandwich actually coherent, or is there a sign error / better route?

## QUESTIONS
A. Is there a tractable v4.29-algebraic route to the EXACT codim identity (not just an inequality)?
   If yes, give the precise lemma chain (which Mathlib lemmas, which engine lemmas, per-component vs
   global). If the exact identity needs absent machinery (fibre-dimension theorem for non-flat dominant
   morphisms / Chevalley upper-semicontinuity / constant-rank-locus flatness), SAY SO plainly.
B. Specifically: can the going-down additivity be applied per-top-component? E.g. fix a top component
   `V` of `Σ̄^r` (= closure of a single orbit `O_M`, an irreducible variety); is `mult|_V : V →
   Mat^{rk≤r}` flat / going-down onto the determinantal variety, so that
   `height_eq_height_add` gives `codim_V(fibre∩V) = codim_V(...) ...`? Does the orbit structure make
   the restricted map flat?
C. If the full route walls: is the r ≤ 1 case (B rank ≤ 1) genuinely tractable by elementary means
   (the fibre structure is simplest), and what would that proof look like algebraically? Is `r=0`
   (fibre = Σ̄^0, shift=0, ALREADY LANDED) the only fully-clean case, making r≤1 already nontrivial?
D. Honest verdict: GO (viable this run, here's the chain) or NO-GO (wall, here's why + the cleanest
   partial result to land instead). Be skeptical — a wrong route wastes a long formalisation tide.

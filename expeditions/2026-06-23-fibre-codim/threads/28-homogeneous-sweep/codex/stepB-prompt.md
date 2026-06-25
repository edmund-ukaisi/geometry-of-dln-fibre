# Codex consult — Lean realization of the "homogeneous sweep" dimension identity (route c, Step B)

You are a Lean 4 + Mathlib (v4.29) formalisation strategist on a project formalising the
Lehalleur–Rimányi 2024 result on fibres of the multiplication map of deep linear networks. I need a
DESIGN review of how to realize one dimension identity in Lean against an EXISTING engine. Do NOT
write long proofs; give the cleanest decomposition and flag the load-bearing risk. Highest reasoning.

## The math (exact-certified on 9 cases, ground-truth)

Fix a dim vector `d = (d_0,...,d_N)`, `N≥1`, over alg-closed char-0 `k`. `Rep_d = ∏ Mat_{d_i × d_{i-1}}`.
`mult : Rep_d → Mat_{d_N × d_0}`, `A ↦ A_N ⋯ A_1`. `r ≤ min_i d_i`. Let `E` = the rank-`r` normal form
(`![1..1;0]`), `F = fibre d E = mult⁻¹(E)`. Let `δ = r(d_N + d_0 − r) = dim Mat^{=r}` (= dim of the
exact-rank-`r` matrices). Let `C = cCodim d r` (a landed combinatorial codimension).
`Σ^r = mult⁻¹(Mat^{=r})` (exact rank r), `Σ̄^r = productRankLocusLE d r = mult⁻¹(Mat^{≤r})` (rank ≤ r).

The endpoint group `H = GL_{d_N} × GL_{d_0}` acts on `Rep_d` through the two END vertices only (the
engine's `BaseChange.baseChange` with inner units = 1); `mult` is `H`-equivariant:
`mult(P•A) = P_N · mult(A) · (P_0)⁻¹`. `Mat^{=r}` is a single `H`-orbit (`H·E`), so `Σ^r = H·F`.

TARGET (Step B): `varietyDim Σ^r = δ + varietyDim F`.
Then Step C (`varietyDim Σ^r = varietyDim Σ̄^r`, density/closure, LR cited), Step D
(`varietyDim Σ̄^r = card − C`, landed-ish), assembly: `codim F = C + δ`.

## The engine (ALL landed, sorry-free, Mathlib v4.29)

- `varietyDim (Z : Set (σ→k)) : ℕ∞ := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0`.
  KEY: it reads `Z` ONLY through `vanishingIdeal k Z`. So `varietyDim` is closure-invariant: if
  `vanishingIdeal Z = vanishingIdeal Z'` then `varietyDim Z = varietyDim Z'`.
- `codimRepCanonical Z := (vanishingIdeal k (canonicalCoord '' Z)).height` (an `Ideal.height`).
- Catenary bridge (PRIME only): `height_vanishingIdeal_add_varietyDim_eq_card` :
  `(vanishingIdeal k Z).height + varietyDim Z = Nat.card σ` GIVEN `(vanishingIdeal k Z).IsPrime`.
  Also affine-domain equidim: `affine_domain_height_add_ringKrullDim_quotient_eq_fintype` :
  for prime `I` and prime `p` of `R⧸I`, `p.height + ringKrullDim((R⧸I)⧸p) = ringKrullDim(R⧸I)`.
- LANDED: `codimRepCanonical Σ̄^r = C` (`SigmaCodim`, reducible `Σ̄^r` OK — it's a height = min over comps).
- LANDED G1: `codimRepCanonical_fibre_eq_of_rank_eq` : same-rank B,B' ⟹ same `codimRepCanonical(fibre)`.
  Built from `exists_baseChange_of_rank_eq` (equal rank ⟹ ∃ end base-change P with B'=P_N·B·P_0⁻¹) +
  `codimRepCanonical_fibre_baseChange` (the base-change is a LINEAR coord auto ⟹ height-invariant, via
  `vanishingIdeal_image_smul` = comap along a `baseChangeAlgEquiv` ring-equiv + `RingEquiv.height_comap`).
- LANDED: the H-action is `BaseChange.baseChange` (inner units=1); `mult_smul` equivariance;
  `image_smul_fibre` : `(P•·) '' (fibre d B) = fibre d (P_N·B·P_0⁻¹)`.
- LANDED orbit-dim substrate (for the SINGLE `G_d`-orbit only): `OrbitPullbackDim`
  (`varietyDim(orbitRankLocus M) = ringKrullDim((orbitPullback M).range)`), `OrbitImageDim`,
  `JacobianTrdeg`, `VoigtDischarge` (squeeze `varietyDim Z_M = finrank(range δ⁰)`).
- LANDED: `varietyDim_productRankLocusLE_stratum` : `varietyDim Mat^{≤r} = δ` (the base thermometer).

## My questions (DESIGN, not proofs)

**Q1 — Is there a clean Lean route to Step B (`varietyDim Σ^r = δ + varietyDim F`) that AVOIDS building
a general fibration-dimension theorem?** The engine has NO general "dim total = dim base + dim fibre"
theorem; the only dim machinery is the single-`G_d`-orbit pullback-trdeg. Candidate reframings:

(a) **Product-variety route.** `Σ^r` is set-theoretically `⋃_{rank B = r} fibre d B`, each fibre
`≅ F` via a linear coord auto (the base change). Is `Σ^r` ISOMORPHIC (as a variety) to a Zariski-locally-
trivial / actually-trivial bundle `Mat^{=r} × F`? Over char-0 alg-closed, `Mat^{=r} = H·E = H/Stab` and the
bundle `H ×_{Stab} F → Mat^{=r}` — is it Zariski-locally trivial (so `dim = δ + dim F`)? Can I instead
exhibit a global section / a global trivialization on the engine to get `varietyDim Σ^r = varietyDim(Mat^{=r} × F)`
and then `varietyDim(X × Y) = varietyDim X + varietyDim Y` (does Mathlib have product Krull dim over a
field, `ringKrullDim(A ⊗_k B) = ringKrullDim A + ringKrullDim B` for f.g. domains?)?

(b) **Catenary-on-`Σ^r` route.** `Σ^r` may be IRREDUCIBLE (is `mult⁻¹` of an irreducible homogeneous
`Mat^{=r}` irreducible? generally NOT — F itself is reducible). If `Σ^r` is reducible the prime catenary
does not apply directly. BUT: is there a clean radical-ideal catenary `height I + ringKrullDim(R⧸I) = card`
for RADICAL `I` in a polynomial ring (min over minimal primes = height; max over minimal primes = coheight;
both via the landed prime equidim)? That would let me convert `codimRepCanonical Σ̄^r = C` into
`varietyDim Σ̄^r = card − C` (Step D) WITHOUT primality. Worth building as a reusable rung? How hard in
Mathlib v4.29 (is `ringKrullDim(R⧸I) = ⨆_{p ∈ minimalPrimes I} ringKrullDim(R⧸p)` available, and
`I.height = ⨅_{p ∈ minimalPrimes I} p.height`)?

**Q2 — Can Step B be SIDESTEPPED entirely?** The real target is `codim F = C + δ`. The H4 thread already
has a one-sided `codim F ≥ C` (`FibreCodim`, F ⊆ Σ̄^r) and an in-flight easy `codim F ≤ C + δ`. Is there a
slicker identity: since each fibre of `mult|_{Σ̄^r}` over a rank-`r` point `≅ F`, and the rank-`r` points are
an open dense `Mat^{=r} ⊆ Mat^{≤r}` of dim δ, can I get `codim_{Σ̄^r} F = δ` directly (F is a fibre slice of
codim = dim base = δ inside Σ̄^r) and then `codim_{Rep} F = codim_{Σ̄^r} F + codim_{Rep} Σ̄^r = δ + C` by the
NESTED catenary (`affine_domain_height_add_ringKrullDim_quotient_eq_fintype` composition)? What is the
cleanest Lean handle for "the generic fibre of a dominant map to an irreducible base has codim = dim base",
WITHOUT flatness — given the base `Mat^{≤r}` (or `Mat^{=r}`) is HOMOGENEOUS so all fibres over `Mat^{=r}`
are literally isomorphic (H-translates)? Does homogeneity give the fibre-dim WITHOUT a general
upper-semicontinuity/Chevalley theorem (which Mathlib lacks)?

**Q3 — Step C cheapness.** `varietyDim Σ^r = varietyDim Σ̄^r`. Since `varietyDim` reads only
`vanishingIdeal`, this is EXACTLY `vanishingIdeal(canonicalCoord '' Σ^r) = vanishingIdeal(canonicalCoord '' Σ̄^r)`,
i.e. `Σ^r` and `Σ̄^r` have the same Zariski closure. Is that the LR 4.4/4.5 density (`Σ̄^r = closure Σ^r`),
genuinely Cited, or is it cheap in the engine (e.g. `Σ̄^r = ⋃_{s≤r} Σ^s` and the lower strata are in the
closure of the top by an explicit degeneration)? If genuinely Cited, what is the MINIMAL named hypothesis to
carry (the set equation `vanishingIdeal Σ^r = vanishingIdeal Σ̄^r`, or the closure equation)?

**Q4 — RANK the routes** (a)/(b) for Q1, and the Q2 sidestep, by Lean-mechanical reachability against THIS
engine (single-orbit pullback-trdeg machinery, prime/affine-domain catenary, the base-change linear-auto
height-invariance, the δ thermometer). Which gives `codim F = C + δ` with the FEWEST genuinely-new rungs?
Name the new rungs precisely. Flag the single biggest risk of building a subtly-wrong statement.

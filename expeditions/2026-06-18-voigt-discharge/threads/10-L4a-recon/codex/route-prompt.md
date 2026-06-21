<task>
Lean 4 + Mathlib (pin v4.29.0). I am scoping the build sub-ladder for one target theorem and
need an INDEPENDENT read of the cleanest proof route + the load-bearing absent lemma. Do NOT
rubber-stamp; attack it from scratch.

TARGET: for a finite-type algebra `A` over a field `k`, if `A` is smooth at a maximal ideal `m`
(membership `⟨m,_⟩ ∈ Algebra.smoothLocus k A`, equivalently `IsSmoothAt k m`, equivalently
`Algebra.FormallySmooth k (Localization.AtPrime m)` for the f.p. case), then
`IsRegularLocalRing (Localization.AtPrime m)`.

HARD CONSTRAINT — NON-CIRCULARITY. The eventual downstream consumer separately computes
`Module.finrank (ResidueField …) (CotangentSpace (AtPrime m)) = finrank (range δ⁰)` and then wants
`ringKrullDim (AtPrime m) = finrank (range δ⁰)`. Therefore the regularity proof MUST NOT route
through `IsRegularLocalRing.iff_finrank_cotangentSpace` (regular ⟺ finrank cotangent = krull dim)
to ESTABLISH regularity — that identity is exactly what the consumer is trying to get out, so using
it to prove regularity is circular. Regularity must be obtained from an INDEPENDENT computation of
`ringKrullDim (AtPrime m)`, namely an equality `ringKrullDim (AtPrime m) = rank Ω[A⁄k]` (the
relative/smooth dimension), established WITHOUT the cotangent=tangent identity. Then:
  finrank(m/m²) = rank Ω    (smooth ⟹ this, the cotangent–Kähler comparison)
  ringKrullDim  = rank Ω    (the dimension bridge, independent)
  ⟹ finrank(m/m²) = ringKrullDim ⟹ regular (via the iff, used here only at the very end as the
  DEFINITIONAL packaging, not to manufacture the dimension number).

WHAT IS ALREADY BUILT (reusable, landed in our library, treat as given):
- An affine-domain dimension formula: for a finite-type DOMAIN `A` over a field and a prime `p`,
  `height p + ringKrullDim (A/p) = ringKrullDim A`; hence for maximal `m`, `height m = ringKrullDim A`
  and `ringKrullDim (Localization.AtPrime m) = ringKrullDim A` (local↔global). (Built via Noether
  normalization + integral-extension height transport + the polynomial-ring catenary equality.)
- The polynomial-ring dimension formula `height p + ringKrullDim (k[x_1..x_n]/p) = n`.

WHAT MATHLIB PROVIDES (verified by rg at this pin):
- `Algebra.smoothLocus`, `IsSmoothAt`, `Algebra.FormallySmooth`; `Algebra.smoothLocus_eq_compl_support_inter`
  (smooth at p ⟺ H¹Cotangent vanishes at p AND Ω[A⁄k] free at p).
- `IsSmoothAt.exists_notMem_isStandardSmooth`: smooth at prime p (f.p.) ⟹ ∃ f∉p, `IsStandardSmooth k (Localization.Away f)`.
- `SubmersivePresentation.rank_kaehlerDifferential`: `Module.rank S Ω[S⁄R] = P.dimension`
  (= #generators − #relations); `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`/`.iff_of_isStandardSmooth`.
- `Smooth.flat`, `Smooth.flat_of_isNoetherianRing` (smooth ⟹ flat).
- Krull height theorem: `Ideal.height_le_spanRank_toENat`, `Ideal.height_le_card_of_mem_minimalPrimes_span`.
- `RingTheory/KrullDimension/Regular.lean`: regular-element dim drop, e.g.
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson` (quotient by a
  nonzerodivisor in the Jacobson radical drops ringKrullDim by exactly 1);
  `ringKrullDim_le_ringKrullDim_quotient_add_card`.
- `IsRegularLocalRing.iff_finrank_cotangentSpace`; `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`.

WHAT IS ABSENT (verified by rg): zero hits for any `rank Ω ↔ ringKrullDim` link; zero
smoothness/etale → `IsRegularLocalRing`; zero fibre-dimension / flat-local-hom dimension formula
(`dim S_q = dim R_p + dim fibre`); no link from a submersive/standard-smooth presentation's relations
to being a regular sequence / complete intersection of the expected height.
</task>

<output_contract>
1. ROUTE: the cleanest Lean route to `ringKrullDim (Localization.AtPrime m) = rank Ω[A⁄k]` at a smooth
   maximal point, established INDEPENDENTLY of cotangent=tangent. Be concrete about which of these
   you'd take and why:
   (a) standard-smooth presentation locally (A_g = k[x_1..x_N]/(f_1..f_c), Jacobian a unit, relative
       dim = N−c = rank Ω) then ringKrullDim(A_g) = N−c via the affine-domain formula + showing
       height(I)=c; OR
   (b) smooth ⟹ flat + a fibre/relative-dimension formula; OR
   (c) something else.
   For the chosen route, name the exact intermediate equalities and which existing decl discharges each.
2. THE LOAD-BEARING ABSENT LEMMA: state precisely the one new lemma that does the real work
   (the thing Mathlib lacks), with its cleanest provable form. In route (a) this is presumably
   "height of the relation ideal = #relations (the relations are a complete intersection at the smooth
   point)" — is THAT itself a sub-library, or does the Krull-height `≤` + a regular-sequence `≥` from
   `KrullDimension/Regular.lean` close it in a module? Adjudicate.
3. SIZE VERDICT: is L4a now a BOUNDED set of modules (state how many and the 1–2 hardest lemmas), or
   still a genuine multi-week sub-library? Name the single thing most likely to balloon it (the
   kill-condition).
4. TRAPS: localization/finite-presentation transport pitfalls; the `Localization.Away f` vs
   `Localization.AtPrime m` mismatch (the standard-smooth presentation is on a basic open D(f), the
   regularity target is at the local ring); nontriviality/domain hypotheses; whether `rank Ω` over
   `A_g` transports to the rank over `AtPrime m` cleanly.
</output_contract>

<grounding_rules>
- Distinguish Mathlib decls you are CONFIDENT exist (name them) from ones you INFER should exist
  (mark "(inferred — verify)"). Do not invent decl names as fact.
- If the route needs a fact not in the given inventory, say so explicitly and size it.
- The non-circularity constraint is non-negotiable: any route that secretly uses
  finrank-cotangent=krulldim to get the dimension number is wrong; flag it if you find yourself there.
</grounding_rules>

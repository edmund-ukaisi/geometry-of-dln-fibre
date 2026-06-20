Lean 4 + Mathlib v4.29 formalisation sizing. I have VERIFIED the following Mathlib v4.29 status by grep + compiling #check probes. I want you to red-team the cleanest proof route + the honest module count for ONE missing theorem.

CONTEXT (all landed sorry-free in our `DLNFibre.Core`):
- k a field, CharZero k, [IsAlgClosed k]. R = MvPolynomial (RepCoord d) k (a polynomial ring over k in finitely many vars). 
- μ_M^* : R →ₐ[k] 𝒪(G), where 𝒪(G) = Localization.Away (∏ det) (a domain, finite type over k). image(μ_M^*) is a finite-type k-subalgebra of 𝒪(G), and is a DOMAIN.
- van(Z_M) = ker(μ_M^*), PRIME (landed). By first-iso R/ker ≃ₐ image(μ_M^*).
- We have a LANDED engine theorem: for any prime p of R = k[x_1..x_n], ringKrullDim(R/p) = s where s is the Noether-normalization rank (an injective integral k-algebra map k[y_1..y_s] →ₐ R/p exists). [Module: Core.PolynomialDimension `ringKrullDim_quotient_eq_noetherRank`; + Core.AffineDomainDimension `affine_domain_height_add_ringKrullDim_quotient_eq`.]
- δ⁰ : C⁰ → C¹ a k-linear map of finite-dim k-vector spaces; finrank(range δ⁰) is the rank of the differential of μ_M at identity. Numerics verified: the target bound is an EQUALITY in examples, we only need ≤.

TARGET (the one missing theorem, "hVoigt-half ≥" recast on the image ring):
    ringKrullDim(image μ_M^*) ≤ finrank_k(range δ⁰).
Equivalently trdeg_k Frac(image μ_M^*) ≤ finrank(range δ⁰).

VERIFIED MATHLIB STATUS (v4.29):
PRESENT (compiled #check):
- Algebra.trdeg R A : Cardinal; trdeg_lt_aleph0 [IsDomain R][FiniteType R S]; trdeg_le_of_injective/surjective (AlgHom); AlgEquiv.trdeg_eq; trdeg_add_eq (tower, domain); MvPolynomial.trdeg_of_isDomain = #ι; IsTranscendenceBasis + exists_isTranscendenceBasis + cardinalMk_eq_trdeg.
- KaehlerDifferential.mvPolynomialBasis : Ω[k[σ]/k] free with basis {dx}; KaehlerDifferential.finite (Ω finite for EssFiniteType); Ω[S/k] free of rank n for IsStandardSmooth (we use this in Core.SmoothLocalRelativeDimension).
- RingCon.quotientKerEquivRangeₐ (AlgHom first-iso R/ker ≃ₐ range).
ABSENT (no file mentions both krullDim and trdeg; no field-extension Kähler rank theorem):
- ringKrullDim A = trdeg k A for f.g. domain A.  [ABSENT]
- rank Ω[L/k] = trdeg for separable/char-0 field extension L/k.  [ABSENT]
- trdeg ≤ rank-of-Jacobian / generic differential rank = image dimension.  [ABSENT]

QUESTIONS:
1. Cleanest Lean route to `ringKrullDim(image μ_M^*) ≤ finrank(range δ⁰)`. Candidate routes:
   (A) Kähler: trdeg Frac(image) = rank Ω[Frac(image)/k] (char 0, separable), and rank Ω of the image function field ≤ finrank(range δ⁰) via the surjection μ_M^* pulling back differentials (chain rule: dμ has rank = finrank range δ⁰). Needs: (i) ringKrullDim(image) = trdeg Frac(image) [ABSENT — must build]; (ii) trdeg = rank Ω for char-0 field ext [ABSENT — must build]; (iii) rank Ω[Frac image /k] ≤ rank dμ.
   (B) Pure linear-algebra / Noether: reuse the LANDED `ringKrullDim_quotient_eq_noetherRank`: dim(image) = s, the # of algebraically independent generators; bound s ≤ finrank(range δ⁰) directly. Does this avoid Kähler entirely? Where does the differential rank enter if we don't go through Ω?
   Which is fewer Lean modules at v4.29? Be concrete about (i) — is `ringKrullDim(f.g. domain) = trdeg` a 1-module build given our landed Noether engine, or genuinely hard?
2. The single HARDEST must-build lemma. Is it (i) ringKrullDim=trdeg, (ii) trdeg=rankΩ char-0, or (iii) the differential-rank ≤ bound? Rank them by Lean difficulty.
3. HONEST module count for the WHOLE missing theorem via the cheapest route. The thread-30 codex estimate was "route-c = 4 modules". Confirm or revise. A "module" = one Lean file with one substantive theorem family.
4. Does CharZero genuinely buy the separability needed for trdeg=rankΩ, and is that step the char-0 bottleneck, or does char-0 enter elsewhere?

Mark every Mathlib claim KNOWN/INFER/MISSING at v4.29. Keep it tight. End: cheapest route letter + module count.

# Statement card — L4a-M3: smooth point ⟹ regular local ring

> **Claim.** Let `A` be a finite-type algebra over an algebraically closed field `k`, and `m` a
> maximal ideal at which `A` is smooth (`IsSmoothAt k m`). Then `Localization.AtPrime m` is a
> **regular local ring**. The dimension is supplied by M2 (`ringKrullDim (AtPrime m) = n`, computed
> non-circularly via the étale-over-affine route); the new content is the **cotangent comparison**
> `finrank κ(m) (m/m²) = n`, proved here via the conormal exact sequence of the residue surjection
> `R ↠ κ(m)`.
>
> - **Lean:** `DLNFibre.Core.smooth_point_isRegularLocalRing`
>   (`lean/DLNFibre/Core/SmoothPointRegular.lean` @ `a41330f65b068dfb9702332d0756b0d68f825f8e`)
> - **Gloss.** For `{k} [Field k] [IsAlgClosed k] {A} [CommRing A] [Algebra k A]
>   [Algebra.FiniteType k A]` and a maximal `m : Ideal A` with `[IsSmoothAt k m]`,
>   `IsRegularLocalRing (Localization.AtPrime m)`.
> - **Proved.**
>   - `smooth_point_isRegularLocalRing` — the headline. Obtains M2's chart and `n`, derives the
>     Ω-rank at `AtPrime m` and the cotangent bound, then closes regularity via
>     `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` (which needs only `spanFinrank ≤ dim`;
>     the reverse `dim ≤ spanFinrank` is Krull's height bound inside it).
>   - `finrank_cotangentSpace_le_of_isSmoothAt` — `finrank κ(m) (CotangentSpace (AtPrime m)) ≤ n`
>     given `finrank (AtPrime m) Ω[AtPrime m⁄k] = n`. The conormal map
>     `KaehlerDifferential.kerCotangentToTensor k R κ : (ker (R→κ)).Cotangent → κ ⊗_R Ω[R⁄k]` is
>     **injective** (`FormallySmooth.kerCotangentToTensor_injective_iff`, RHS `Subsingleton
>     (H1Cotangent k κ)` from `κ` formally smooth over `k`); its source is `(maximalIdeal R).Cotangent
>     = CotangentSpace R` (since `ker (algebraMap R κ) = maximalIdeal R`); its target has
>     `κ`-dimension `n = rank_R Ω` (base change of the rank-`n` free `Ω[R⁄k]`). So
>     `finrank κ (m/m²) ≤ finrank κ (κ ⊗ Ω) = n`.
>   - `finrank_kaehler_localizationAtPrime_eq` — `finrank (AtPrime m) Ω[AtPrime m⁄k] = n`: the rank-Ω
>     transport **M2 deferred**. `AtPrime m` is a localization of the standard-smooth chart
>     `S = A[1/f]` (`isLocalization_of_submonoid_le`, `powers f ≤ m.primeCompl`); the Kähler comparison
>     map `KaehlerDifferential.map k S (AtPrime m)` is an `IsLocalizedModule`
>     (`KaehlerDifferential.isLocalizedModule_map`), so
>     `Module.finrank_of_isLocalizedModule_of_free` gives `finrank (AtPrime m) Ω = finrank S Ω = n`
>     (the chart's free rank `n`, from M2's `rank Ω[S⁄k] = n`).
>   - `finrank_cotangentSpace_eq_of_isSmoothAt` — companion `finrank κ(m) (m/m²) = n` from the headline
>     via `IsRegularLocalRing.iff_finrank_cotangentSpace` + M2's `ringKrullDim = n`.
>   - `injective_cotangent_cast` — helper: conormal injectivity transports along an ideal equality
>     `I = J` (`subst`), used to rewrite the map's domain `(ker (R→κ)).Cotangent` to
>     `(maximalIdeal R).Cotangent = CotangentSpace R`.
> - **Assumed.** `[Field k]`, `[IsAlgClosed k]`, `[Algebra.FiniteType k A]` (the hypotheses the claim
>   names). `[IsAlgClosed k]` is used **only** to obtain `PerfectField k`
>   (`IsAlgClosed.perfectField`), which with `EssFiniteType k κ` makes the residue field formally
>   smooth over `k` (`FormallySmooth.of_perfectField`) — the argument needs nothing stronger than a
>   **perfect** base field. Smoothness enters as `[IsSmoothAt k m]`, which **unfolds definitionally** to
>   `Algebra.FormallySmooth k (Localization.AtPrime m)` (this is exactly what
>   `kerCotangentToTensor_injective_iff` consumes for `P := R`).
> - **Cited.** none — every step is a named Mathlib lemma applied here, plus the M2 bridge consumed:
>   `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` (gives the chart `S = A[1/f]`,
>   `IsStandardSmoothOfRelativeDimension n k S`, `rank Ω[S⁄k] = n`, and `ringKrullDim (AtPrime m) = n`).
>   Mathlib: `FormallySmooth.kerCotangentToTensor_injective_iff`,
>   `FormallySmooth.subsingleton_h1Cotangent`, `FormallySmooth.of_perfectField`,
>   `FormallySmooth.projective_kaehlerDifferential`, `Module.free_of_flat_of_isLocalRing`,
>   `KaehlerDifferential.{kerCotangentToTensor, isLocalizedModule_map, finite}`,
>   `Module.{finrank_baseChange, finrank_of_isLocalizedModule_of_free, Finite.base_change}`,
>   `IsRegularLocalRing.{of_spanFinrank_maximalIdeal_le, iff_finrank_cotangentSpace}`,
>   `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`,
>   `IsLocalRing.{ker_residue, residue_surjective, ResidueField.algebraMap_eq}`,
>   `IsLocalization.{localizationAlgebraOfSubmonoidLe, localization_isScalarTower_of_submonoid_le,
>   isLocalization_of_submonoid_le, isNoetherianRing}`,
>   `IsStandardSmoothOfRelativeDimension.isStandardSmooth`,
>   `IsStandardSmooth.free_kaehlerDifferential`, `isJacobsonRing_of_finiteType`,
>   `IsLocalization.isMaximal_of_isMaximal_disjoint`, `IsLocalization.Away.finitePresentation`.
> - **Deferred.** none for the smooth⟹regular step. (L2 separately identifies the cotangent space
>   `m/m²` with `range δ⁰` over `k` — the geometric tangent-space content — and may reuse
>   `finrank_cotangentSpace_eq_of_isSmoothAt`; that identification is L2 work, not M3.)
> - **Status.** sorry-free + **reviewed: FAITHFUL**. Axioms `[propext, Classical.choice, Quot.sound]`
>   (all five lemmas). `scripts/sorries` = 0. Whole `DLNFibre` library green. Reviewer verdict
>   (thread 13, decorrelated Codex on Q2/Q3): **FAITHFUL** — headline statement genuine and
>   non-vacuous; the `≤` is the genuinely-smooth (injective conormal) direction, combined with the
>   universal `dim ≤ spanFinrank` to force equality; non-circular (M2's `ringKrullDim = n` consumed as
>   a black box, never re-derived from cotangent=dim); `[IsAlgClosed k]` used only for `PerfectField k`;
>   axioms clean; names = content. **Caveat (transparency, not a defect):**
>   `finrank_cotangentSpace_eq_of_isSmoothAt` takes `ringKrullDim (AtPrime m) = n` as an explicit
>   hypothesis (honest given the `_eq_` name and the L2 reuse point) — a downstream consumer supplies
>   M2's `hdim` (the headline does so internally).

## Route taken (what fought back, what came in bounded)

- **Kill-condition did NOT fire.** The recon (thread 10) flagged the cotangent↔Kähler comparison as
  the last potential scope-balloon: would `finrank(m/m²) = rank Ω` need a genuinely-absent
  conormal-left-exactness sub-library? It does not. The exact left-exact end I needed — injectivity of
  the conormal map — is in Mathlib as a single lemma
  `Algebra.FormallySmooth.kerCotangentToTensor_injective_iff`, built on the `Algebra.Extension`
  cotangent-complex machinery. No new sub-library; ~208 LoC.
- **The decisive correction (Codex, decorrelated xhigh).** My first plan used the conormal
  **surjectivity** `m/m² ↠ κ⊗Ω` (the easy end, `Ω[κ⁄k] = 0`). That bounds the wrong way
  (`finrank(κ⊗Ω) ≤ finrank(m/m²)`). The regularity criterion `of_spanFinrank_maximalIdeal_le` needs
  `finrank(m/m²) ≤ n`, i.e. an **injection** `m/m² ↪ κ⊗Ω` — which is the genuinely smooth content
  (`H1Cotangent k κ` vanishing). Codex caught the direction error and named the exact lemma.
- **`[IsAlgClosed k]` is only for perfectness.** The injection needs `FormallySmooth k κ`, which holds
  for any **perfect** base field via `of_perfectField` + the residue field's `EssFiniteType k κ`. The
  brief allowed `[IsAlgClosed k]`; the proof carries it but uses only `PerfectField k`. (The residue
  field is **not** assumed `= k`.)
- **What fought back: the dependent-type cast.** The conormal map's source is
  `(RingHom.ker (algebraMap R κ)).Cotangent`, which carries only `Module (R ⧸ ker)` — *not*
  syntactically `Module κ = Module (R ⧸ maximalIdeal R)`, even though `ker = maximalIdeal R`. `rw` /
  `simp` / `subst` on the ideal all hit the dependent-motive wall (the `Module κ` instance depends on
  the ideal). Resolution: the helper `injective_cotangent_cast {I J} (h : I = J) …`, where `I, J` are
  **local variables**, so `subst h` *does* fire — transporting injectivity cleanly. The map is then
  `hker ▸`-transported to domain `(maximalIdeal R).Cotangent`, where the canonical `Module κ` lives.
- **Ω-rank transport (the M2-deferred piece).** `AtPrime m` is realized as a localization of the chart
  `S = A[1/f]` via `IsLocalization.isLocalization_of_submonoid_le` (submonoid `powers f ≤
  m.primeCompl`, since `f ∉ m`), with the `k`-scalar tower `k → S → AtPrime m` built by hand. Then
  `KaehlerDifferential.isLocalizedModule_map` (the `map R R S T` instance, base unchanged) +
  `Module.finrank_of_isLocalizedModule_of_free` transports `finrank S Ω = n` to `finrank (AtPrime m)
  Ω = n`. `Ω[S⁄k]` free of rank `n` comes from `IsStandardSmooth.free_kaehlerDifferential` + M2's
  `rank = n`.
- **`Ω[AtPrime m⁄k]` free, used in the base-change finrank.** `Module.finrank_baseChange` needs
  `Module.Free R Ω[R⁄k]`; obtained at the local ring from smoothness:
  `FormallySmooth.projective_kaehlerDifferential` (projective) ⟹ `Module.free_of_flat_of_isLocalRing`.
  `(Module.finrank_baseChange).trans hΩ` is used as a **term** — the `simp`/`rw` forms tripped an
  `OreLocalization` self-module instance diamond.

## Codex consultations (artefacts)

- `codex/cotangent-{prompt,answer}.md` — route sizing; confirmed BOUNDED (~250-400 LoC est.), caught
  the surjective-vs-injective direction error, named `kerCotangentToTensor_injective_iff` and the
  perfect-field route.
- `codex/injection-{prompt,answer}.md` — confirmed Route C (`kerCotangentToTensor_injective_iff`)
  lands at v4.29; ruled out the JZ-`H1`-bridge route (missing comparison lemma) and the
  `Generators.self` split route as dead-as-stated.
- `codex/cotangent-cast-{prompt,answer}.md` — the dependent-type cast (incomplete run; solved
  independently via the `subst`-on-variables helper).

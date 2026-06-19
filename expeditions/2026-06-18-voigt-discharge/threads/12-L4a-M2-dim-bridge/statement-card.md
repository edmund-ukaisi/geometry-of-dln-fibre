# Statement card — L4a-M2: the non-circular dimension bridge

> **Claim.** Let `A` be a finite-type algebra over a field `k`, and `m` a maximal ideal at which `A`
> is smooth (`IsSmoothAt k m`). Then there is a basic-open chart `S = A[1/f]` (`f ∉ m`) on which `A`
> is standard smooth of some relative dimension `n`, with `Ω[S⁄k]` free of rank `n`, and the local
> ring `Localization.AtPrime m` has Krull dimension `n`. The Krull dimension is computed by the
> **étale-over-affine-space route**, *not* via the cotangent/tangent = dimension identity — so the
> result is available to *prove* smooth ⟹ regular (M3) without circularity.
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`
>   (`lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean` @ `1b7eb13455f316e14923c8a56eb89e2e4a2a94d2`)
> - **Gloss.** For `{k} [Field k] {A} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]`, a maximal
>   `m : Ideal A` with `[IsSmoothAt k m]`, there exist `n : ℕ` and `f : A` with `f ∉ m` such that
>   (i) `Localization.Away f` is `IsStandardSmoothOfRelativeDimension n k`,
>   (ii) `Module.rank (Localization.Away f) (Ω[Localization.Away f⁄k]) = (n : Cardinal)`, and
>   (iii) `ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞)`.
>   A single existentially-bound `n` ties all three conjuncts; `n` is the **chart-local**
>   `Module.finrank S (Ω[S⁄k])` for `S = Localization.Away f` (the relative dimension on the chart),
>   *not* the global `finrank A (Ω[A⁄k])`.
> - **Proved.**
>   - `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` — the headline (the three-conjunct
>     existential above), unconditionally within the four typeclass hypotheses.
>   - `ringKrullDim_quotient_comap_etale_eq_zero` — for `g : k[x₁,…,xₙ] → S` étale and `q : Ideal S`
>     maximal, `ringKrullDim (k[x₁,…,xₙ] ⧸ q.comap g) = 0`: the quotient `B/(q.comap g)` is module-finite
>     over `S/q` (a field) by Zariski's lemma, and the integral-injective quotient map carries
>     dimension `0` down.
>   - `height_comap_etale_eq` — `(q.comap g).height = n` for the same data: the zero-dim quotient feeds
>     the L5 affine-space catenary equality `height p + ringKrullDim (B/p) = n`.
>   - `rank_kaehler_eq_finrank`, `isStandardSmoothOfRelativeDimension_finrank` — on a standard-smooth
>     chart `Ω` is free of finite rank, so `Module.rank S Ω = finrank S Ω`; install
>     `IsStandardSmoothOfRelativeDimension (finrank S Ω) k S`.
>   - Non-vacuity (in-file, inside the green build): the hypothesis bundle is satisfiable on
>     `MvPolynomial (Fin 1) ℚ` (smooth-everywhere), and the headline **fires** there
>     (`exact ringKrullDim_localizationAtPrime_eq_of_isSmoothAt m`) — so the conclusion is inhabited.
> - **Assumed.** `[Field k]`, `[Algebra.FiniteType k A]` (the finite-type-over-a-field hypotheses the
>   claim names). Smoothness enters as the per-point typeclass `[IsSmoothAt k m]` (the chart-existence
>   `IsSmoothAt.exists_notMem_isStandardSmooth` needs `FinitePresentation`, discharged from `FiniteType`
>   over the Noetherian field). No `[IsAlgClosed k]` — the result holds for **any field**; closed-point
>   maximality goes through Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`,
>   `IsLocalization.isMaximal_of_isMaximal_disjoint`), not the residue-field-is-`k` Nullstellensatz.
> - **Cited.** none — every step is a named Mathlib lemma applied here, plus the two landed in-repo
>   bricks below; no external analytic interface. Bricks consumed: **M1**
>   `Ideal.height_eq_under_of_etale` (étale ⟹ `q.height = (q.under B).height`); **L5**
>   `height_add_ringKrullDim_quotient_eq` (affine-space catenary equality);
>   `ringKrullDim_eq_of_integral_injective`, `ringKrullDim_eq_zero_of_isField` (IntegralDimension /
>   AffineDomainDimension). Mathlib: `IsSmoothAt.exists_notMem_isStandardSmooth`,
>   `IsStandardSmoothOfRelativeDimension.{iff_of_isStandardSmooth, rank_kaehlerDifferential,
>   exists_etale_mvPolynomial}`, `RingHom.etale_algebraMap`, `IsLocalization.height_map_of_disjoint`,
>   `IsLocalization.AtPrime.ringKrullDim_eq_height`, `IsLocalization.isMaximal_of_isMaximal_disjoint`,
>   `finite_of_finite_type_of_isJacobsonRing`, `isJacobsonRing_of_finiteType`,
>   `Ideal.disjoint_powers_iff_notMem`, `KaehlerDifferential.finite`, `Module.finrank_eq_rank`.
> - **Deferred.** The **rank-Ω transport to `Localization.AtPrime m`** — the rank conjunct is stated on
>   the *chart* `S = A[1/f]` (`rank Ω[S⁄k] = n`), not on `AtPrime m`. Pushing `rank Ω` down the further
>   localization `S → AtPrime m` (via `KaehlerDifferential.isLocalizedModule_map` +
>   `Module.lift_rank_of_isLocalizedModule_of_free`) is **M3 work**, where it joins the cotangent
>   comparison `finrank (m/m²) = rank Ω = n`. M2 delivers the dimension equality without it.
> - **Status.** sorry-free + reviewed. Axioms `[propext, Classical.choice, Quot.sound]` (re-checked on
>   the headline). Whole library green. Reviewer verdict (thread 12, decorrelated Codex): **FAITHFUL** —
>   single `n` tied across all three conjuncts and chart-local (no hidden balloon); the dimension
>   conjunct's proof never routes through cotangent/tangent = dim (non-circular); rank honestly stated
>   on the chart, transport-to-`AtPrime m` legitimately deferred to M3; the any-field generality is
>   genuinely sound; non-vacuity genuine via the headline-firing witness. No critical findings.

## Route taken (what fought back, what came in bounded)

- **Came in bounded.** The route is exactly the recon's étale-over-affine-space chain (thread 10),
  with M1 and L5 as the load-bearing in-repo bricks. No hidden balloon fired — the maximal-contraction
  step (the recon's flagged risk) resolved cleanly through Zariski's lemma rather than needing a new
  general-CA brick.
- **Maximal-contraction route (Step E, the riskiest).** Rather than a direct "finite-type map from a
  Jacobson ring contracts maximals to maximals" lemma (not found), the proof shows the *quotient*
  `B/(q.comap g)` is module-finite over the field `S/q` (Zariski's lemma
  `finite_of_finite_type_of_isJacobsonRing`), so it is a zero-dimensional ring; `ringKrullDim (B/p) = 0`
  then feeds L5 to give `p.height = n`. This avoids needing `p` itself to be maximal as a hypothesis and
  works over any field. The maximality of `q = m·S` in the localization `S = A[1/f]` comes from
  `IsLocalization.isMaximal_of_isMaximal_disjoint` (`m` maximal, `f ∉ m`).
- **Étale API actually used.** `IsSmoothAt.exists_notMem_isStandardSmooth` (smooth-at ⟹ standard-smooth
  chart `A[1/f]`); `IsStandardSmoothOfRelativeDimension.{iff_of_isStandardSmooth,
  exists_etale_mvPolynomial}` (install the relative dimension `n := finrank S Ω`, and get the étale
  presentation `g : k[x₁,…,xₙ] → S`); `RingHom.etale_algebraMap` to turn `g.Etale` into the
  `Algebra.Etale B S` instance M1 consumes. `q.under B = q.comap g` is definitional (`Ideal.under_def`,
  `rfl`) once `g.toAlgebra` is the `Algebra B S` instance.
- **Step B (height transport).** `IsLocalization.height_map_of_disjoint` on the powers-of-`f` submonoid
  (disjoint from `m` by `Ideal.disjoint_powers_iff_notMem`) gives `q.height = m.height`; two uses of
  `IsLocalization.AtPrime.ringKrullDim_eq_height` connect both to `ringKrullDim`. No explicit
  localization-of-localization iso needed.
- **`n` definition (the kill-condition Codex flagged).** Using the **chart-local**
  `n := finrank S Ω[S⁄k]` (not the global `finrank A Ω[A⁄k]`) is load-bearing: the global finrank is not
  determined by smoothness at a single `m`. The module uses the chart-local form throughout.

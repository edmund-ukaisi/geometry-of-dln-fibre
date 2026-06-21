# Statement card — L4d affine-domain dimension formula

Module: `lean/DLNFibre/Core/AffineDomainDimension.lean` (network-free Core engine).
Commit SHA: `74460f0`.

---

> **Claim (headline).** For `R = MvPolynomial (Fin n) k` (`k` a field), a prime `I`, the domain
> `A = R ⧸ I`, and a prime `p` of `A`: `height p + dim (A ⧸ p) = dim A` — `A` is equidimensional.
>
> - **Lean:** `DLNFibre.Core.affine_domain_height_add_ringKrullDim_quotient_eq`
>   (`lean/DLNFibre/Core/AffineDomainDimension.lean` @ `74460f0`)
> - **Signature.** `(k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]`
>   `(p : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [p.IsPrime] :`
>   `(p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)`
>   `= ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I)`
> - **Gloss.** In the quotient domain `A = R/I` of a polynomial ring by a prime ideal, the height of
>   any prime `p` (length of the longest strict chain of primes below `p`) plus the Krull dimension
>   of the further quotient `A/p` equals the Krull dimension of `A`. Heights and coheights are exactly
>   complementary — the geometric statement that an irreducible affine variety is equidimensional.
> - **Proved.** The full equality, unconditionally, for any field `k` (no `IsAlgClosed`, no char-0).
>   Route: Noether-normalize `A` to an integral injective `g : B = k[y₁..y_s] ↪ A`; transport the
>   height of `p` to its contraction `q = p.comap g` in the polynomial base `B`
>   (`height_under_eq_of_isIntegral`); identify `dim(A/p) = dim(B/q)` (integral injective induced
>   quotient map + L5.4 dimension invariance) and `dim A = dim B = s` (L5.4 + L5.0); then apply the L5
>   polynomial-ring catenary equality `height_add_ringKrullDim_quotient_eq` on `B` at `q`. Assembled
>   additively in `WithBot ℕ∞` — no truncated subtraction.
> - **Assumed.** `[Field k]`; `I` prime (so `A` is a domain); `p` prime. (Minimal correct hypotheses;
>   `IsDomain A` is derived, not assumed.)
> - **Cited.** None new. Reuses L5 (`Core.NoetherMonicPositioning`, `Core.IntegralDimension`,
>   `Core.PolynomialDimension`) and Mathlib's classical going-down theorem for integral extensions of
>   an integrally closed domain (`Algebra.HasGoingDown`, `@[stacks 00H8]`) — both already in the
>   dependency closure, not a new cited interface.
> - **Deferred.** None.
> - **Status.** sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`).

---

> **Claim (supporting brick — reusable).** Integral height transport: for an integral injective
> extension `R → S` with `R` an integrally-closed Noetherian domain and `S` a domain, a prime `P` of
> `S` and its contraction `P.under R` have equal height.
>
> - **Lean:** `DLNFibre.Core.height_under_eq_of_isIntegral` (`@ 74460f0`)
> - **Signature.** `{R S} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] [IsDomain S]`
>   `[IsIntegrallyClosed R] [IsNoetherianRing R] [Algebra.IsIntegral R S]`
>   `(hinj : Function.Injective (algebraMap R S)) (P : Ideal S) [P.IsPrime] :`
>   `P.height = (P.under R).height`
> - **Gloss.** Contracting a prime along an integral injective extension of an integrally closed
>   Noetherian domain preserves height. `≤` is going-up (the spectrum `comap` is strictly monotone,
>   `strictMono_comap_of_isIntegral`); `≥` is going-down (`Ideal.exists_ltSeries_of_hasGoingDown`,
>   from Mathlib's `Algebra.HasGoingDown` instance for integral extensions of an integrally closed
>   domain).
> - **Proved.** The height equality, both directions, unconditionally under the stated hypotheses.
> - **Cited.** Mathlib `Algebra.HasGoingDown` (`@[stacks 00H8]`) — in the dependency closure.
> - **Status.** sorry-free, axiom-clean.

---

> **Claim (corollary — equidimensionality at closed points).** For `A = R ⧸ I` a finite-type domain
> over a field and `m` a maximal ideal, `height m = dim A`; hence
> `dim (Localization.AtPrime m) = dim A` (local ↔ global).
>
> - **Lean:** `DLNFibre.Core.height_eq_ringKrullDim_of_isMaximal`,
>   `DLNFibre.Core.ringKrullDim_localizationAtPrime_isMaximal_eq` (`@ 74460f0`)
> - **Gloss.** At a maximal ideal `m` of the affine domain `A`, the height of `m` equals the whole
>   Krull dimension of `A` (because `A/m` is a field, dimension `0`, so the headline collapses). The
>   localization `A_m` (a local ring) has the same Krull dimension as `A` — equidimensionality at the
>   closed point. This is the feed-in to the smooth ⟹ regular bridge (L4a).
> - **Proved.** Both, unconditionally, for `m` maximal (`A/m` is a field via
>   `Ideal.Quotient.maximal_ideal_iff_isField_quotient`; localization dim via
>   `IsLocalization.AtPrime.ringKrullDim_eq_height`).
> - **Assumed.** `[m.IsMaximal]` (so `A/m` is a field, dimension `0`); no Nullstellensatz / Jacobson
>   needed — maximality is taken as hypothesis.
> - **Cited.** None new.
> - **Deferred.** None.
> - **Status.** sorry-free, axiom-clean.

---

## Route note (for the AUDIT / hardener)

Mathlib has **no** catenary / equidimensional theory (`rg IsCatenary` = 0 hits), and no affine-domain
dimension formula. The recon (thread 08) flagged the smooth⟹regular finish as a multi-week
sub-library, but L4d was sized as the **bounded** piece. Codex's first read (route2-answer.md) called
L4d unbounded because it was told "going-down for integral + normal base is absent" — that inventory
claim was **wrong**: Mathlib has `Mathlib/RingTheory/IntegralClosure/GoingDown.lean` providing
`Algebra.HasGoingDown` for integral extensions of an integrally closed domain (`@[stacks 00H8]`). With
that instance (which fires by `inferInstance` for `B = k[y₁..y_s]`, a UFD hence integrally closed, the
`IsIntegrallyClosed` instance needing `import Mathlib.RingTheory.Polynomial.RationalRoot`), the single
new ingredient — the integral height transport — closes in one module, exactly as sized. This mirrors
the L5 sizing where "recon 01 misread Mathlib."

The genuinely-multi-week part remains **L4a** (cotangent ↔ dimension / smooth ⟹ regular via the
Kähler/conormal comparison), untouched here.

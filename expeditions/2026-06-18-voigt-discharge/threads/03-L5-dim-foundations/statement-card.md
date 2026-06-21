# Statement card — L5 dim-foundations (integral-extension dimension invariance)

Module: `lean/DLNFibre/Core/IntegralDimension.lean` @ `4cb0958`.
Status: **sorry-free; fidelity AUDIT SURVIVED** (2026-06-19, reviewer; awaiting hardener). Axioms on
every theorem below: `[propext, Classical.choice, Quot.sound]` (re-verified). Whole `DLNFibre` library
builds green; the target module compiles warning-free; `scripts/sorries` = 0; module is network-free
(Mathlib-only imports, no `DLNFibre.DLN`).

> **Fidelity AUDIT verdict — SURVIVED.** All five headlines denote their standard theorems with
> faithful orientation and honest hypotheses. Decorrelated Codex consult
> (`codex/fidelity-{prompt,answer}.md`) independently confirmed: (i) `dim S = dim A` is the standard
> integral-injective dimension-invariance theorem; (ii) `≤` needs only integrality, `≥` needs the
> injectivity (only at the chain base); (iii) `krullDim_le_of_strictComono_and_surj` is genuinely
> **unsound** for the `≥` direction — its order-reflection hypothesis `comap a < comap b → a < b`
> fails for integral extensions (Codex counterexample: `A = k[x] ↪ S = k[x]×k[x]` diagonal, primes
> `(0)×k[x]` and `k[x]×(x)` comap to `(0) < (x)` but are incomparable in `S`). The going-up chain lift
> (`exists_ltSeries_comap_last_of_isIntegral`) is the correct route; the L5.3 route note is confirmed.
> Two non-blocking notes: (a) L5.2's `_hinj` is a decorative (genuinely-unused) hypothesis, kept for
> interface uniformity and honestly underscored — re-verified by rebuilding L5.2 with the hypothesis
> removed; (b) injectivity is *sufficient* for L5.3, not strictly *minimal* (Codex: `ker ⊆ nilrad`,
> i.e. `Spec S → Spec A` surjective, would suffice) — but `Function.Injective` is the textbook-standard
> hypothesis and is what makes the conclusion `dim A` (rather than `dim (A/ker)`) correct, so the card's
> "genuinely needed" reading is accurate as stated. L5.4 non-vacuity witness is the (degenerate)
> identity hom; substantive non-triviality is honestly deferred downstream.

All statements are network-free `Core` engine, at `RingHom`/`Algebra` generality over commutative
rings. The `≤` direction (L5.2) needs only integrality; the `≥` direction (L5.3) and the headline
(L5.4) additionally need injectivity.

---

## L5.0 — dimension of a polynomial ring over a field

> **Claim.** For a field `k` and finite index `ι`, `dim k[xᵢ : i∈ι] = #ι`; specialised to `Fin n`,
> `dim k[x₁,…,xₙ] = n`.
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_mvPolynomial_field`,
>   `DLNFibre.Core.ringKrullDim_mvPolynomial_fin_field` (`lean/DLNFibre/Core/IntegralDimension.lean` @ `4cb0958`)
> - **Gloss.** `ringKrullDim (MvPolynomial ι k) = Nat.card ι` (field `k`, `Finite ι`); and
>   `ringKrullDim (MvPolynomial (Fin n) k) = n`.
> - **Proved.** Both equalities, unconditionally for any field.
> - **Assumed.** `Field k`, `Finite ι`. (Mathlib's underlying lemma needs only `IsNoetherianRing`;
>   `Field` is used solely to discharge `ringKrullDim k = 0`.)
> - **Cited.** none reproved here — built on `MvPolynomial.ringKrullDim_of_isNoetherianRing` and
>   `ringKrullDim_eq_zero_of_field`, both proved in Mathlib v4.29.
> - **Deferred.** none.
> - **Witness.** `dim ℚ[x] = 1` (in-file `example`).

## L5.1 — `dim (R ⧸ p) = coheight p`

> **Claim.** For a prime `p` of a commutative ring `R`, the Krull dimension of `R⧸p` is the coheight
> of `p` in `Spec R` (the length of the longest chain of primes *above* `p`).
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_quotient_eq_coheight`
>   (helper: `primeSpectrumQuotientOrderIsoIci`)
> - **Gloss.** `ringKrullDim (R ⧸ p.asIdeal) = (coheight p : WithBot ℕ∞)`, for `p : PrimeSpectrum R`,
>   `R` a `CommRing`.
> - **Proved.** The equality, for any commutative ring and any prime (no Noetherian/field/domain
>   hypothesis).
> - **Assumed.** `CommRing R` only.
> - **Cited.** none reproved — assembles `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`,
>   `Order.krullDim_eq_of_orderIso`, `Order.coheight_eq_krullDim_Ici`, all Mathlib v4.29.
> - **Deferred.** none. (The `zeroLocus p = Ici p` step is proved in-file via `mem_zeroLocus` +
>   `asIdeal_le_asIdeal`.)

## L5.2 — `dim S ≤ dim A` for an integral extension

> **Claim.** An integral ring extension does not increase Krull dimension.
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_le_of_integral_injective`
>   (helper: `strictMono_comap_of_isIntegral`)
> - **Gloss.** For `f : A →+* S` with `f.IsIntegral`, `ringKrullDim S ≤ ringKrullDim A`.
> - **Proved.** The inequality. Injectivity is **not** used (the hypothesis `_hinj` is carried only
>   for uniform interface with L5.3/L5.4 and is underscored as unused).
> - **Assumed.** `CommRing A`, `CommRing S`, `f.IsIntegral`.
> - **Cited.** none reproved — `Ideal.comap_lt_comap_of_integral_mem_sdiff` +
>   `Order.krullDim_le_of_strictMono`, Mathlib v4.29.
> - **Deferred.** none.

## L5.3 — `dim A ≤ dim S` for an integral injective extension

> **Claim.** An integral injective ring extension does not decrease Krull dimension (lying-over +
> going-up lift any prime chain in `A` to one of equal length in `S`).
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_ge_of_integral_injective`
>   (helper: `exists_ltSeries_comap_last_of_isIntegral`)
> - **Gloss.** For `f : A →+* S` with `f.IsIntegral` and `Function.Injective f`,
>   `ringKrullDim A ≤ ringKrullDim S`. The helper: every `LTSeries (PrimeSpectrum A)` lifts to an
>   `LTSeries (PrimeSpectrum S)` of equal length whose last element comaps to the original last.
> - **Proved.** The inequality and the chain-lift.
> - **Assumed.** `CommRing A`, `CommRing S`, `f.IsIntegral`, `Function.Injective f`. (Injectivity is
>   genuinely needed — only the base of the chain, via `comap ⊥ = ⊥`.)
> - **Cited.** none reproved — going-up `Ideal.exists_ideal_over_prime_of_isIntegral`,
>   `Ideal.comap_bot_of_injective`, `RelSeries.inductionOn'`, `LTSeries.length_le_krullDim`,
>   Mathlib v4.29.
> - **Deferred.** none.
> - **Route note.** `Order.krullDim_le_of_strictComono_and_surj` (the route the sizing thread
>   suggested) is **not** usable here: it requires `comap a < comap b → a < b` globally, which is
>   false for integral extensions (incomparable primes can lie over a comparable pair). The proof
>   instead lifts chains directly by going-up. This is the load-bearing finding of the tide.

## L5.4 — headline: dimension invariance

> **Claim.** Krull dimension is invariant under an integral injective ring extension.
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_eq_of_integral_injective`
> - **Gloss.** For `f : A →+* S` with `f.IsIntegral` and `Function.Injective f`,
>   `ringKrullDim S = ringKrullDim A`.
> - **Proved.** The equality, by `le_antisymm` of L5.2 and L5.3.
> - **Assumed.** `CommRing A`, `CommRing S`, `f.IsIntegral`, `Function.Injective f`.
> - **Cited.** none new.
> - **Deferred.** none.
> - **Witness.** identity ring hom `dim R = dim R` (in-file `example`, hypotheses inhabited).

---

## Kill-condition check (instance propagation)

The expedition was watching whether `IsIntegrallyClosed` / `LiesOver` / `FaithfulSMul` fail to
propagate. **They did not arise**: the integral-extension route here uses only `Algebra.IsIntegral`
(via `algebraize [f]`), plain going-up (`exists_ideal_over_prime_of_isIntegral`), and lying-over —
no going-down, no integrally-closed-domain hypothesis. The order-transport machinery
`Order.krullDim_le_of_strictMono` went through cleanly; `krullDim_le_of_strictComono_and_surj` was
the wrong tool and was replaced by a direct chain lift (see L5.3 route note).

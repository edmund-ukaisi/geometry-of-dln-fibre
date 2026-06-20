## Route — which of (a)/(b), and why it is cheaper in Lean

Pick **(a), Noether normalization / trdeg**, but not because it is already short. It is cheaper only because Mathlib already has Noether normalization and substantial trdeg/integrality API; **route (b) is basically not present** as catenary/Cohen-Macaulay infrastructure.

Route (b) would require building `IsCatenary`-style theory, proving polynomial rings are catenary or Cohen-Macaulay, then deriving height/coheight additivity. I found no usable `IsCatenary`/`Catenary` infrastructure.

Caveat: route (a) still does **not** reduce to a handful of lemmas. The missing bridge is exactly dimension theory: integral finite dimension invariance plus the codimension/trdeg formula for primes in polynomial rings.

## Inventory — present vs absent

- **Present: Krull dimension of polynomial rings.**
  - `ringKrullDim`
  - `ringKrullDim_eq_zero_of_field`
  - `Polynomial.ringKrullDim_of_isNoetherianRing`
  - `MvPolynomial.ringKrullDim_of_isNoetherianRing`
  - For `[Field k]`, this gives `ringKrullDim (MvPolynomial (Fin n) k) = n` after `simp`/`Nat.card_fin`.

- **Present: Noether normalization.**
  - `NoetherNormalization.exists_integral_inj_algHom_of_quotient`
  - `NoetherNormalization.exists_integral_inj_algHom_of_fg`
  - `NoetherNormalization.exists_finite_inj_algHom_of_fg`
  - These give an injective finite/integral map `MvPolynomial (Fin s) k →ₐ[k] A`, but they do **not** package `s = trdeg k A` or the final dimension formula.

- **Present: trdeg / algebraic independence.**
  - `Algebra.trdeg`
  - `AlgebraicIndependent`
  - `IsTranscendenceBasis`
  - `exists_isTranscendenceBasis`
  - `IsTranscendenceBasis.mvPolynomial`
  - `MvPolynomial.trdeg_of_isDomain`
  - `IsTranscendenceBasis.cardinalMk_eq_trdeg`
  - `Algebra.IsIntegral.isTranscendenceBasis_iff`
  - No direct bridge found from `ringKrullDim` to `trdeg`.

- **Present: going-up / going-down ingredients.**
  - Integral lying-over/going-up API in `RingTheory/Ideal/GoingUp.lean`, e.g. `exists_ideal_over_prime_of_isIntegral`, `exists_ideal_over_maximal_of_isIntegral`.
  - `Algebra.HasGoingDown`
  - `Algebra.HasGoingDown.of_flat`
  - Going-down for integral extensions of integrally closed domains is present as an instance in `RingTheory/IntegralClosure/GoingDown.lean`.

- **Present: height API.**
  - `Ideal.height`, `Ideal.primeHeight`
  - `Ideal.height_eq_primeHeight`
  - `Ideal.height_le_ringKrullDim_of_ne_top`
  - `IsLocalization.AtPrime.ringKrullDim_eq_height`
  - `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
  - `Polynomial.height_eq_height_add_one`

- **Absent: dimension invariance under finite/integral extension.**
  - I found no theorem like `ringKrullDim_eq_of_integral`, `ringKrullDim_eq_of_finite_injective`, or “dim S = dim R for S integral over R”.

- **Absent: target additivity.**
  - No direct theorem of the form `p.height + ringKrullDim (R ⧸ p) = ringKrullDim R`.

- **Absent: catenary route.**
  - No usable `IsCatenary` / `Catenary` infrastructure found.
  - No general “height + coheight = dimension” theorem found.

## Sub-ladder — the lemmas to prove, in dependency order, each one line

1. `ringKrullDim_le_of_integral_injective`: strict comap of prime chains along an injective integral map.

2. `ringKrullDim_ge_of_integral_injective`: lift prime chains by lying-over/going-up.

3. `ringKrullDim_eq_of_integral_injective` / finite variant: combine the previous two.

4. `ringKrullDim_fg_domain_eq_trdeg`: use Noether normalization plus polynomial-ring dimension.

5. `height_eq_natCard_sub_trdeg_mvPolynomial_quotient`: for prime `p ⊂ k[x₁,…,xₙ]`, prove `p.height = n - trdeg k Frac(R ⧸ p)`.

6. Final target: combine `ringKrullDim_fg_domain_eq_trdeg`, `height_eq_natCard_sub_trdeg_mvPolynomial_quotient`, and `MvPolynomial.ringKrullDim_of_isNoetherianRing`.

## Size verdict — module / few-modules / sub-library, + the 1–2 hardest lemmas + effort read

This is a **genuine small sub-library**, not a single module.

Hardest lemmas:

- `ringKrullDim_eq_of_integral_injective`: probably manageable because Mathlib has lying-over, strict comap, and going-down/height pieces. Still nontrivial due chain/order APIs.

- `height_eq_natCard_sub_trdeg_mvPolynomial_quotient`: the real bottleneck. This is the codimension theorem for prime ideals in polynomial rings, and is essentially the missing dimension-formula content.

Effort read: **weeks, not hours**. Route (a) is the only sane route, but still likely several modules. Route (b) would be larger: building catenary/CM theory first is substantially more expensive.
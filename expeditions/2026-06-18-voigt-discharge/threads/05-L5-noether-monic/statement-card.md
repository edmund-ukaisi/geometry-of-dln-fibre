# Statement card — L5.7 full equality (catenary `≥` → `height p + dim(R/p) = n`)

Module: `lean/DLNFibre/Core/NoetherMonicPositioning.lean` @ `b7a4955`.
Status: **sorry-free; axiom-clean; pending fidelity AUDIT.** All headline theorems depend on axioms
`[propext, Classical.choice, Quot.sound]` (verified by `#print axioms`). Whole `DLNFibre` library
builds green; the target module compiles warning-free; `scripts/sorries` = 0; module is network-free
(Mathlib + the proved `Core.IntegralDimension` / `Core.PolynomialDimension`, no `DLNFibre.DLN`).

All statements over `R = MvPolynomial (Fin n) k` with `k` an arbitrary `Field` — **`IsAlgClosed` /
`Infinite k` are NOT required**. The monic-positioning substitution uses powers of one variable, so
it is valid over any field, including finite fields.

> **Closes the gap reported by thread 04.** Thread 04 delivered L5.7-`≤`
> (`primeHeight_add_ringKrullDim_quotient_le`) and named the missing piece as the monic-positioning
> lemma (Mathlib's `private` Noether-normalization `T`). This thread re-derives that lemma and runs
> the `≥` induction, landing the full equality.

---

## Monic-coordinate positioning brick

> **Claim.** A nonzero `f : k[x₀,…,xₙ]` can be moved by a `k`-algebra automorphism so that it becomes
> monic in `x₀` over `k[x₁,…,xₙ]` (up to a unit scalar).
>
> - **Lean:** `DLNFibre.Core.exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`
> - **Gloss.** For `f ≠ 0` in `MvPolynomial (Fin (n+1)) k`, there is `ψ : MvPolynomial (Fin (n+1)) k
>   ≃ₐ[k] MvPolynomial (Fin (n+1)) k` with `IsUnit (finSuccEquiv k n (ψ f)).leadingCoeff` — the image
>   of `ψ f` under the isomorphism isolating `x₀` has a unit `x₀`-leading coefficient.
> - **Proved.** Existence of `ψ` and the unit-leading-coefficient property.
> - **Assumed.** `Field k`, `f ≠ 0`.
> - **Cited.** none reproved. The substitution `T : xᵢ ↦ xᵢ + x₀^(N^i)` (`N = 2 + f.totalDegree`)
>   and its degree bookkeeping (`T_leadingcoeff_isUnit`) are **copied verbatim** from
>   `Mathlib.RingTheory.NoetherNormalization` (Brasca–Su–Lin–Su, `@[stacks 00OW]`), where they are
>   `private`; only the visibility changes. This is a re-derivation, not a new mathematical claim.
> - **Deferred.** none.

## Supporting bricks

> - `exists_monic_mem_of_isUnit_leadingCoeff_mem` — an ideal of `A[X]` containing an element of unit
>   leading coefficient contains a monic (scale by the unit inverse). Any `CommRing A`.
> - `ringKrullDim_quotient_eq_under_of_monic` — for a prime `P ⊆ A[X]` containing a monic,
>   `ringKrullDim (A[X] ⧸ P) = ringKrullDim (A ⧸ P.under A)`. Via `Monic.quotient_isIntegral`
>   (`A → A[X]/P` integral) → `isIntegral_quotientMap_iff` + `quotientMap_injective` (descend to the
>   injective integral `A/(P.under A) → A[X]/P`) → L5.4 `ringKrullDim_eq_of_integral_injective`. Any
>   `CommRing A`.
> - `one_le_height_map_quotient_of_monic` — for a prime `P ⊆ A[X]` containing a monic, the fiber
>   `P.map (mk ((P.under A)·A[X]))` has height `≥ 1`: the monic's leading coefficient `1 ∉ P.under A`
>   keeps the fiber off `⊥`, and `⊥` is prime in the domain `A[X] ⧸ ((P.under A)·A[X])`. Any
>   `CommRing A`.
> - `height_map_algEquiv`, `ringKrullDim_quotient_map_algEquiv` — a `k`-algebra equivalence preserves
>   prime height and quotient Krull dimension (transfer across the coordinate change).

## L5.7 (`≥` induction core)

> **Claim.** For a prime `p` of `k[x₁,…,xₙ]`, `n ≤ height p + coheight p`.
>
> - **Lean:** `DLNFibre.Core.nat_le_height_add_coheight` (ideal form);
>   `DLNFibre.Core.nat_le_height_add_coheight_spectrum` (`PrimeSpectrum` form).
> - **Gloss.** `(n : ℕ∞) ≤ p.height + Order.coheight ⟨p, _⟩`. Induction on `n`: `n = 0` trivial;
>   `p = ⊥` gives `coheight = dim R = n` via `coheight_bot_eq_krullDim`; otherwise pick `0 ≠ f ∈ p`,
>   position it monic, peel `x₀` through `finSuccEquiv`, and combine the additive height brick
>   (`P.height = q.height + fiber.height`, `fiber.height ≥ 1`) with dim preservation and the IH on
>   `q = P.under A`.
> - **Proved.** the inequality, for any field `k` and any prime.
> - **Assumed.** `Field k`, `p.IsPrime`.
> - **Cited.** none reproved — assembles the proved bricks above + the additive brick
>   `height_eq_height_under_add_height_map_quotient` (thread 04) + L5.0/L5.1/L5.4.
> - **Deferred.** none.

## L5.7 equality (headline)

> **Claim.** For a prime `p` of `R = k[x₁,…,xₙ]` (`k` any field),
> `Ideal.height p + ringKrullDim (R ⧸ p) = n` — affine `n`-space is equidimensional / catenary, so
> height and coheight are exactly complementary.
>
> - **Lean:** `DLNFibre.Core.height_add_ringKrullDim_quotient_eq` (`Ideal.height` form);
>   `DLNFibre.Core.primeHeight_add_ringKrullDim_quotient_eq` (`Ideal.primeHeight` form, the companion
>   to the landed `≤` `primeHeight_add_ringKrullDim_quotient_le`);
>   `DLNFibre.Core.height_add_coheight_eq` (order form on `PrimeSpectrum`).
> - **Gloss.** ideal form: `(p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = (n : WithBot ℕ∞)`.
>   order form: `(Order.height p : ℕ∞) + Order.coheight p = n`.
> - **Proved.** the exact equality, for any field `k` and any prime. `le_antisymm` of the `≤` half
>   (thread 04) and the `≥` induction core.
> - **Assumed.** `Field k`, `p.IsPrime`.
> - **Cited.** none reproved beyond the copied Noether-normalization substitution (see the
>   positioning brick) — every dimension/height step is a proved Mathlib lemma or a brick proved in
>   this expedition.
> - **Deferred.** none. (This is the catenary dimension identity itself; no analytic interface is
>   invoked — contrast the downstream RLCT reading, which is `Cited`.)
> - **Witness.** in-file `example`s: at `p = ⊥` in `ℚ[x,y]` (`n = 2`) the equality reads `0 + 2 = 2`,
>   with `ringKrullDim (R ⧸ ⊥) = 2` shown nonzero — the dimension term genuinely carries the sum.

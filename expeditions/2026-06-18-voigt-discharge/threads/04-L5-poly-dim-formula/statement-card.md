# Statement card — L5.5 / L5.7-≤ (polynomial-ring prime dimension data)

Module: `lean/DLNFibre/Core/PolynomialDimension.lean` @ `3851c9c`.
Status: **sorry-free; axiom-clean; pending fidelity AUDIT.** All theorems below depend on axioms
`[propext, Classical.choice, Quot.sound]` (verified). Whole `DLNFibre` library builds green; the
target module compiles warning-free; `scripts/sorries` = 0; module is network-free (Mathlib + the
proved `Core.IntegralDimension`, no `DLNFibre.DLN`).

All statements over `R = MvPolynomial (Fin n) k` with `k` an arbitrary `Field` — **`IsAlgClosed` is
NOT required** for these pure dimension facts (it is forced only by the downstream point-space ↔
`PrimeSpectrum` Nullstellensatz bridge, which these lemmas do not touch).

> **Hypothesis adjustment vs the tide brief.** The brief framed L5.7 as the full equality
> `height p + ringKrullDim (R ⧸ p) = n`. The **`≤` half is delivered unconditionally**; the **`≥`
> half (the catenary content) is NOT delivered** — it is the reported gap (see bottom). The headline
> equality is therefore deliberately **not** stated as a theorem here: gating it on a hypothesis that
> is itself the catenary `≥` would be an overclaiming (`ugly`) statement. The `≥`'s load-bearing
> *additive* half is delivered as a clean reusable brick (`height_eq_height_under_add_height_map_quotient`).

---

## L5.5 — `dim (R ⧸ p)` equals the Noether-normalization rank

> **Claim.** For a prime `p` of `R = k[x₁,…,xₙ]` (`k` a field), `dim (R ⧸ p)` equals the rank `s ≤ n`
> of the polynomial subring `k[y₁,…,y_s]` over which `R ⧸ p` is integral by Noether normalization.
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_quotient_eq_noetherRank`
>   (`lean/DLNFibre/Core/PolynomialDimension.lean` @ `3851c9c`)
> - **Gloss.** `∃ s ≤ n, (∃ g : k[Fin s] →ₐ[k] (R ⧸ p), Function.Injective g ∧ g.IsIntegral) ∧
>   ringKrullDim (R ⧸ p) = (s : WithBot ℕ∞)`. There is an injective integral `k`-algebra map from
>   a polynomial ring on `s ≤ n` variables into `R ⧸ p`, and the dimension of `R ⧸ p` is that `s`.
> - **Proved.** The existence of `s`, the witnessing integral injective `g`, and `dim (R ⧸ p) = s`.
> - **Assumed.** `Field k`, `p.IsPrime`. (The prime hypothesis is used only via `p ≠ ⊤` to feed
>   Noether normalization.)
> - **Cited.** none reproved — assembles `exists_integral_inj_algHom_of_quotient`
>   (Mathlib Noether normalization, `@[stacks 00OW]`), the proved L5.4
>   `ringKrullDim_eq_of_integral_injective`, and the proved L5.0 `ringKrullDim_mvPolynomial_fin_field`.
> - **Deferred.** none. (The bundled `g` is `s` as a *Noether rank*, equal to the transcendence
>   degree of `Frac(R/p)/k`; the `= trdeg` reading is a downstream corollary, not claimed here.)
> - **Witness.** for `p = ⊥` in `k[x]`, the produced `s` satisfies `(s : WithBot ℕ∞) = 1`
>   (`dim (k[x] ⧸ ⊥) = dim k[x] = 1`) — in-file `example`, so the rank read is non-degenerate.

## L5.7 (`≤` direction) — `height p + coheight p ≤ n`

> **Claim.** For a prime `p` of `k[x₁,…,xₙ]`, the height of `p` plus the dimension of `R ⧸ p` is at
> most `n` (a chain below `p` spliced with one above `p` is a chain in `Spec R`, of length ≤ `n`).
>
> - **Lean:** `DLNFibre.Core.height_add_coheight_le` (order form);
>   `DLNFibre.Core.primeHeight_add_ringKrullDim_quotient_le` (ideal form).
> - **Gloss.** order form: for `p : PrimeSpectrum R`, `(Order.height p : ℕ∞) + Order.coheight p ≤ n`.
>   ideal form: for `p : Ideal R` prime, `(Ideal.primeHeight p : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ n`.
> - **Proved.** Both inequalities, for any field `k` and any prime.
> - **Assumed.** `Field k` (order form); `Field k`, `p.IsPrime` (ideal form).
> - **Cited.** none reproved — `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`,
>   `ringKrullDim_mvPolynomial_fin_field` (L5.0), `ringKrullDim_quotient_eq_coheight` (L5.1), all
>   Mathlib v4.29 / proved upstream in this expedition.
> - **Deferred.** the matching `≥` (equality) — see the reported gap.

## Polynomial-tower additive brick — the `≥`/catenary *additive* half

> **Claim.** For `A` Noetherian and a prime `P` of `A[X]` over `q = P.under A`,
> `height P = height q + height (image of P in (A ⧸ q)[X])`.
>
> - **Lean:** `DLNFibre.Core.height_eq_height_under_add_height_map_quotient`
> - **Gloss.** `P.height = (P.under A).height + (P.map (Quotient.mk ((P.under A).map (algebraMap A A[X])))).height`.
> - **Proved.** The exact additive equality, unconditionally for any Noetherian `A`.
> - **Assumed.** `CommRing A`, `IsNoetherianRing A`, `P.IsPrime`.
> - **Cited.** none reproved — `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
>   (`@[stacks 00ON]`, Matsumura 13.B), with the `Algebra.HasGoingDown A A[X]` instance from
>   `Algebra.HasGoingDown.of_flat` (`A[X]` free hence flat over `A`) and `P.LiesOver (P.under A)`
>   automatic. All by `inferInstance`.
> - **Deferred.** none for this brick. (It is one of the two ingredients of the catenary `≥`; the
>   missing ingredient is dimension preservation under the variable peel — the monic positioning.)

---

## Reported gap — the catenary `≥` direction (NOT delivered)

The full headline `height p + dim (R ⧸ p) = n` requires the `≥` direction `height p ≥ n − dim(R/p)`.
The standard proof inducts on `n`, peeling one variable with the additive brick above; each peel
step needs a **monic-coordinate-positioning** lemma: after a `k`-algebra coordinate change, a chosen
nonzero element of `p` becomes **monic in the top variable**, so the induced `(A[X] ⧸ P)` is integral
over `(A ⧸ q)` (`Polynomial.Monic.quotient_isIntegral`) and the quotient dimension is preserved
(via L5.4). This positioning is Mathlib's Noether-normalization `T` argument, which is **`private`**
in `RingTheory.NoetherNormalization` (`T`, `T_leadingcoeff_isUnit`, `hom1_isIntegral`,
`hom2_isIntegral`); re-deriving it is a separate ~150–200-line module. `IsCatenary` /
`IsEquidimensional` / `ringKrullDim = trdeg` are all **absent** at the v4.29 pin (grep = 0).

**Kill-condition outcome (controller-watched): CLEAN on instance propagation.** Every instance the
going-down route needs fires by `inferInstance`: `Module.Flat A A[X]`, `Algebra.HasGoingDown A A[X]`
(via `of_flat`), `P.LiesOver (P.under A)`, `IsIntegrallyClosed (k[y₁..y_s])` (via the UFM chain),
`Polynomial.Monic.quotient_isIntegral`, and L5.5 (`exists_integral_inj_algHom_of_quotient` +
`ringKrullDim_eq_of_integral_injective` + `ringKrullDim_mvPolynomial_fin_field`) all probed green.
The blocker is the *positioning lemma*, not instance propagation. Decorrelated Codex consult (xhigh)
independently reached the same diagnosis and named the same single biggest missing piece
(`exists_monic_mem_after_algEquiv`): `codex/ge-route-{prompt,answer}.md`.

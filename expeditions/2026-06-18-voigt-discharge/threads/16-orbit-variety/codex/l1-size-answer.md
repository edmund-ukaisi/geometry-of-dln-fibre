All lemma names below are verified against the local Mathlib v4.29 checkout unless marked otherwise. I am not using any GUESS names.

**Route Verdict**
Your localization-pullback route is the right route. I do not see a materially cheaper Mathlib v4.29 route to the exact headline
`(MvPolynomial.vanishingIdeal k O_M).IsPrime`.

The tempting Spec/topology route has real lemmas:

- `PrimeSpectrum.irreducibleSpace` for `[IsDomain R]`
- `PrimeSpectrum.continuous_comap`
- `IsIrreducible.image`
- `isIrreducible_iff_closure` / `IsIrreducible.closure`
- `PrimeSpectrum.vanishingIdeal_range_comap`
- `PrimeSpectrum.closure_range_comap`

But it only proves the scheme-theoretic image closure of `Spec 𝒪(G_d)` is irreducible. You still must identify that closure with the closure of the concrete `k`-point orbit, i.e. bridge `PrimeSpectrum.comap μ_M^*` to `MvPolynomial.pointToPoint '' O_M`. That bridge is essentially the same density/evaluation argument as `vanishingIdeal O_M = RingHom.ker μ_M^*`.

So: use `RingHom.ker_isPrime` into a domain after proving the kernel/vanishing-ideal equality. Reusing `isZariskiIrreducible_iff_isPrime_vanishingIdeal` directly does not save work; it just repackages the same equality as irreducibility of the point image.

**Hardest Sub-Step**
The hardest single sub-step is not Sigma indexing. It is the forward implication

```lean
g ∈ MvPolynomial.vanishingIdeal k (Set.range μ_M)
  → μ_M^* g = 0
```

more precisely the compatibility/density lemma:

> a localization element over `D(Δ)` that evaluates to zero at every `k`-point with `Δ ≠ 0` is zero.

This combines:

- `IsLocalization.Away.surj`
- `IsLocalization.mk'_eq_zero_iff`
- `MvPolynomial.funext`
- building `GL` elements from arbitrary coordinates with `Δ ≠ 0`
- evaluating the localization via `IsLocalization.Away.lift` / `Localization.awayLift`
- proving the adjugate expression evaluates to the actual unit inverse.

No genuinely absent sub-library is required. What is absent is a convenience API like “regular functions on a principal open are determined by algebraically closed field points”. You will prove that locally.

**LoC / Module Shape**
Expect **600+ LoC** for a robust sorry-free file. With aggressive local lemmas and the global-denominator trick below, maybe **400-600**, but I would budget 600+.

It can be one Lean module, but internally it wants a sub-ladder:

1. generic group-coordinate matrices and determinant product `Δ`;
2. coordinate ring/domain of `D(Δ)`;
3. generic inverse matrix and evaluation lemmas;
4. pullback `μ_M^*`;
5. `vanishingIdeal_range_mu_eq_ker`;
6. final prime theorem.

For maintainability, I would split this in real development, but “one module” is feasible.

**Dodging Friction**
Best dodge: use **one global denominator**.

Let

```lean
GroupCoord d := Σ v : Fin (N+1), Fin (d v) × Fin (d v)
R := MvPolynomial (GroupCoord d) k
Pgen v : Matrix (Fin (d v)) (Fin (d v)) R
detGen v := (Pgen v).det
Δ := ∏ v, detGen v
OG := Localization.Away Δ
```

Then define inverse matrices in `OG` using `IsLocalization.Away.invSelf Δ`, not per-vertex `mk'` denominators:

```lean
detCompl v := ∏ w in Finset.univ.erase v, detGen w

PgenInv v :=
  (algebraMap R OG (detCompl v) * IsLocalization.Away.invSelf Δ) •
    (algebraMap R OG).mapMatrix (Matrix.adjugate (Pgen v))
```

Use:

- `Matrix.mul_adjugate`
- `Matrix.adjugate_mul`
- `IsLocalization.Away.mul_invSelf`
- `Finset.prod_eq_mul_prod_diff_singleton_of_mem`

This avoids per-vertex localization inverses and most explicit `mk'` work. You still need adjugate, but only matrix-level, not entry-by-entry.

Do **not** switch to separate inverse matrix variables `Q_v` with relations `P_v Q_v = 1`, `Q_v P_v = 1` unless you want more work: proving that quotient ring is a domain forces you back to the adjugate/localization isomorphism anyway. A scalar inverse variable `T` for `Δ` is fine:

```lean
(MvPolynomial Unit R) ⧸ Ideal.span { MvPolynomial.C Δ * MvPolynomial.X () - 1 }
```

and Mathlib has `IsLocalization.Away.mvPolynomialQuotientEquiv`. This is a syntax alternative to `Localization.Away Δ`, not a fundamentally cheaper proof.

For (d), make `μ_M` definitionally close to `O_M`; then

```lean
Set.range μ_M = O_M
```

is a small `ext`/`rintro` proof, not a serious step.
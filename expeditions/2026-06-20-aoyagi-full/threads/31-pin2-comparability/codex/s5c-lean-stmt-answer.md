1. **Verdict: A**

Use (A). The atom should not deliver (d)/(e) directly, because the cert gives real counterexamples to uniform multiplicative comparability.

The bridge is:

Let `x q = ‖R q‖_F^2`, `y q = ‖S0 q * S1 q‖_F^2`, and suppose the atom gives
`|x q - y q| ≤ C * sumE2 q`.

To recover (d)/(e), the consumer must additionally prove a **relative error** bound on the actual germ region:
`C * sumE2 q ≤ θ * y q` with `0 ≤ θ < 1`.

Then:
`x ≤ (1 + θ) * y`, so take `gamma2 = 1 + θ`.

Also:
`y ≤ x + θ y`, hence `(1 - θ) * y ≤ x`, so take
`gamma1 = (1 - θ)⁻¹`.

A hypothesis like `y ≤ K * sumE2` goes the wrong way. You need `sumE2 ≤ K * y`, or directly `C * sumE2 ≤ θ * y`.

2. **Lean-Flavoured Atom**

Yes: factor the atom into pure matrix algebra plus a separate analytic/germ charge.

Sketch:

```lean
def frobSq {m n} (X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (X i j)^2

theorem schur_core_remainder_bound
    {r M : ℕ}
    (S0 S1 K R : Matrix (Fin M) (Fin M) ℝ)
    (hR : R = S0 * (1 - K) * S1) :
    R - S0 * S1 = - S0 * K * S1 ∧
    frobSq (R - S0 * S1)
      ≤ frobSq S0 * frobSq K * frobSq S1 := ...
```

Then instantiate

```lean
K = Z1 * ⅟ A * Y0
```

or Mathlib’s `⅟ A`/`invOf`/`Invertible.invOf` form, depending on your local convention.

This is the right split. The matrix atom proves only the ring identity and Frobenius submultiplicativity. The `sumE2` charge belongs downstream, where the hypotheses controlling `Y0`, `Z1`, `S0`, `S1`, and boundedness of `A⁻¹` live.

3. **Non-Vacuity Guard**

State the germ bound with a fixed, externally meaningful control function:

```lean
∃ C > 0, ∃ U ∈ 𝓝 0,
  ∀ q ∈ U,
    |frobSq (R q) - frobSq (PiS q)| ≤ C * sumE2 q
```

and require:

```lean
∀ᶠ q in 𝓝 0, 0 ≤ sumE2 q
```

The constant `C` must be chosen once for the neighborhood, independent of `q`, and `sumE2` must be the concrete regular energy used later, not an existentially chosen error gauge. That prevents the statement from becoming a tautological “some function bounds the error” lemma.

It is still a weak additive estimate by design; non-vacuity comes from tying it to the consumer’s fixed `sumE2`.

4. **Germ Arithmetic**

Yes.

`R - PiS = -S0 * (Z1 * A⁻¹ * Y0) * S1` is `O(eps^4)`, while `PiS` is `O(eps^2)`, so

```text
|‖R‖² - ‖PiS‖²|
≤ 2 ‖PiS‖ ‖R - PiS‖ + ‖R - PiS‖²
= O(eps^6),
```

and `O(eps^6) ≤ C * O(eps^2)` uniformly on a small neighborhood, assuming the usual boundedness of `A⁻¹`.

BOTTOM LINE: make `schur_core_germ_comparability` deliver the exact remainder identity plus an additive Frobenius-square germ bound against the fixed `sumE2`; recover multiplicative (d)/(e) only after proving a separate relative-error hypothesis `C * sumE2 ≤ θ * coreF` with `θ < 1`.
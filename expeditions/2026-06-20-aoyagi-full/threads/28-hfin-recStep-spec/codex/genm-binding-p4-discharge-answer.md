1. **Predicate**

Use a **concrete family**, not broad `IsBindingP4`, for the theorem to build now:

```lean
def IsDirectSchurP4 (M : Fin 3 → ℕ) : Prop :=
  ∃ r : ℕ, M = (![r, r, 4] : Fin 3 → ℕ)
```

Derived: this is exactly the shape of `SchurCore 4 r`: a two-layer product `Δ · S` with `Δ : r×r`, `S : r×4`.

Do **not** define `IsBindingP4 M := M (Fin.last L) = 4`. That is too broad and false for the bridge.

2. **Threshold Arithmetic**

The front-peel + SchurCore bridge does **not** compose in general. `fibre_lintegral_mul_le` preserves the same exponent and imposes caps `c' < M_s / 2`; these caps combine by `min`, not by addition.

For the direct case `M = (4,4,4)`:

```text
minAdm(4,4,4) = min_t (4-t)^2 + 4t = 12
½ minAdm = 6
schurLambda 4 = 2*4 - 2 = 6
```

So direct `SchurCore 4 4` reaches the target.

For a deeper case like `M = (3,3,4,4)`:

```text
minAdm(3,3,4,4) = 8
½ minAdm = 4
front peel cap = 3/2
```

So the peel undershoots before Schur even starts. This is a real threshold wall for the proposed broad route.

3. **Shape Mismatch**

Yes, there is a genuine shape mismatch.

After front-peeling a general depth `L` vector, the residual core is

```text
A_{L-2} · A_{L-1}
: (M_{L-2} × M_{L-1}) · (M_{L-1} × M_L).
```

To match `SchurCore 4 r`, one needs specifically

```text
M_{L-2} = r,
M_{L-1} = r,
M_L = 4.
```

So only a narrow tail shape is directly massageable. Example `M = (3,3,4,4)` leaves `3×4 · 4×4`, not `r×r · r×4`. Transposing gives `4×4 · 4×3`, i.e. a `p=3` Schur shape, not the available `p=4` carve.

4. **Recommendation**

Pick **C**, but make it narrower than “all depth-2 output-4”: require the square left factor.

Build:

```lean
theorem routeMBoxThresholdFinite_rr4_of_schurRecStep
    (hstep : SchurRecStep 4 schurLambda) (r : ℕ) :
    RouteMBoxThresholdFinite (![r, r, 4] : Fin 3 → ℕ)
```

This is bedrock-correct: it directly consumes `schurGen_lt_top_modulo_recStep hstep r`, plus the arithmetic lemma

```lean
(minAdm (![r, r, 4] : Fin 3 → ℕ) : ℝ) / 2 = schurLambda r
```

The broad `(A)` statement is a research wall unless a new, banked bridge proves both the rectangular/tail-shape conversion and the missing threshold composition.
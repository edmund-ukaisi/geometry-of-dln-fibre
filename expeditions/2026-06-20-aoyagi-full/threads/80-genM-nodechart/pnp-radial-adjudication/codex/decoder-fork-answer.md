1. **Verdict: sound, with the stated nonvanishing hypotheses.**

The fixed `E(0,0)` anchor is not a radial target because it is not a free coordinate. Its contribution is `u · 1 = u`, so it should be represented in `B` as an affine dependence on the pivot coordinate `wu`. In the derivative, that affine term contributes an ordinary linear derivative `∂/∂wu = 1` in the relevant output row. It does not by itself cause rank loss.

Given the exact symbolic fact:

```text
det DB = engine ≠ 0
```

`B` is a genuine local isomorphism wherever the engine product is nonzero. The additive `wu` term is harmless; rank collapse would only occur if the full determinant vanished, for example at special parameter values where some `K` or `q` factor in the engine is zero.

Status: **proof-level**, assuming the Lean proof establishes `det DB = engine` and the engine nonvanishing hypotheses.

2. **Verdict: yes, the correct contract is chart-level factorization.**

The false contract is:

```text
smulRmatRfin u (decoder x) = decoder (pivotBlowupOn x)
```

because the decoder contains a literal fixed `1`, and blowup does not turn that literal into `u`.

The right contract is instead:

```text
phi = B ∘ pivotBlowupOn(active, p)
```

where `B` is not merely `decoder` applied after blowup. It is the de-radialized chart map: it reads multiplicative coordinates directly, and reads the fixed-anchor output additively from the pivot coordinate `wu`.

Then the obstruction disappears:

```text
phi_E00(x) = ... + u
B_E00(pivotBlowupOn x) = ... + wu = ... + u
```

while for free active coordinates:

```text
B_i(pivotBlowupOn x) = ... + (u x_i)
```

So the factorization matches both the additive fixed anchor and the multiplicative free coordinates.

Status: **proof-level**, provided the Lean identity is stated for `phi` and this explicitly defined `B`, not for decoder commutation.

3. **Verdict: correct count and exponent.**

The active set should be:

```text
{pivot} ∪ {free E-coords excluding fixed E(0,0)} ∪ {leaf coords}
```

The fixed `E(0,0)` anchor is not active because it has no coordinate to scale. It contributes through the pivot coordinate additively inside `B`.

For `pivotBlowupOn(active, p)`, the derivative determinant contributes:

```text
u ^ (card(active) - 1)
```

because the pivot coordinate `p` maps to itself, while every other active coordinate is multiplied by `u`.

Since:

```text
card(active) = minAdm
```

the blowup exponent is:

```text
minAdm - 1 = #E-free + #leaf
```

That matches the exact symbolic determinant:

```text
det Dphi = det DB · u^(minAdm - 1)
```

Status: **proof-level**, assuming `p ∈ active`, the pivot coordinate is distinct from every free/leaf coordinate, and the active-cardinality lemma excludes the fixed anchor exactly once.

Residual soundness risks:

- `B` is a local iso only on the locus where `engine ≠ 0`.
- The pivot coordinate used by `B` must be a genuine coordinate distinct from the free `E` and leaf coordinates.
- The Lean proof should avoid any decoder-level smul commutation lemma involving the fixed literal `1`; the only safe identity is the chart-level factorization.
**Recommended Shape**

Use a **generator-carrier intermediate predicate**, not a separable weight times the original reduced-chain loss.

For a route/profile `π`, the load-bearing object should be:

```text
CarrierFinite(π) :=
  for all c ≥ 0 with c < Θ(π),
    ∫_{Ω_π}
      (∏ exceptional coordinates u_ℓ^{h_π,ℓ})
      · SJLinGenState.loss(E_π)(u, x)^{-c}
    d(u, x)
    < ∞.
```

Where:

- `Ω_π` is the bounded chart domain after the first `k` peels: exceptional coordinates, active residual coordinates, and remaining layer/coupling coordinates.
- `h_π` is the accumulated Jacobian exponent vector.
- `E_π` is the generator carrier state. Its generators remember, generator by generator, the monomial exceptional support times a linear residual.
- `SJLinGenState.loss(E_π) = ∑ᵢ bᵢ²`.
- `Θ(π)` should be the current combinatorial budget, intended as  
  `Θ(π) = ½ · minAdm(remChain π)`, provided the terminal bridge below is available.

The top corollary is the specialization at `π = ∅`, where there are no exceptional coordinates and the carrier loss is the original DLN Frobenius loss.

**Q1 Verdict**

The faithful intermediate predicate is the **generator-carrier loss** predicate.

The separable form

```text
(accumulated Jacobian monomial) · frobSq(prod(remaining chain))^{-c}
```

is not faithful in the middle of the recursion. It hides exactly the data you said is load-bearing:

- the anisotropic term `Γ · Q_b`;
- which generators share the same exceptional divisor;
- the fact that front coupling and deeper rank loci must be resolved using the same divisor bookkeeping.

That separable form becomes legitimate only at the terminal monomialized stage, where the banked terminal factorization says

```text
sjLoss = (∏ |u_ℓ|^{2k_ℓ}) · residual_unit
```

with a residual unit bounded below.

This conclusion follows directly from your fidelity facts; the exact formal packaging of `Ω_π`, `E_π`, and `h_π` is inferential.

**Peel-Step Shape**

The step should be a backward induction theorem:

```text
CarrierFinite(π extended by cut u)
  ⇒ CarrierFinite(π)
```

for the high-exponent regime, plus a terminal/block discharge for the low-exponent regime.

At profile `π` and cut with block dimension

```text
pq = peelCharge(remChain π, u),
```

do:

1. **Clear first.** Perform scalar Schur elimination while all relevant generators still have constant shared support. This is where `gen_rowMix_const` is essential: the row mix factors the shared monomial unconditionally.

2. **Then attach the radial divisor.** Apply `radialStep`, which prepends one fresh divisor shared by all generators in the current state.

3. **Split the loss.** Use the generator-level block split:

```text
loss(E_π after clear/radial)
  = frobSq(block variables) + W_π'
```

up to the chart/unit conventions already banked.

4. **Apply the corank-block lemma.**

If `c > pq/2`, use regime `(2a)`:

```text
∫∫ (frobSq D + W_π')^{-c}
  ≤ C · ∫ W_π'^{-(c - pq/2)}.
```

Then apply the inductive predicate at `π'` with shifted exponent

```text
c_next = c - pq/2.
```

The soundness gate gives the budget:

```text
c < ½ minAdm(remChain π)
and
minAdm(remChain π) ≤ pq + minAdm(remChain π')
⇒
c - pq/2 < ½ minAdm(remChain π').
```

If `c < pq/2`, use regime `(2b)` as the local terminal/block Morse-dominance case.

The equality case `c = pq/2` is not covered by the two stated regime lemmas. You need either a monotonicity/epsilon argument or an explicit borderline lemma. That is a small but real missing proof obligation.

**Where Anisotropy And Shared Divisors Enter**

They enter before the analytic block estimate, at the generator-carrier transformation level.

The Schur elimination removes the visible anisotropy only because it is performed while supports are still constant. After that, the radial divisor is attached to the whole generator state, so the front coupling generators and deeper generators share the same divisor record.

That is precisely why the carrier predicate is non-circular on the rank-deficient deeper-factor locus: the proof never integrates the front block pointwise against a possibly rank-deficient `Q`. Instead, `W_π'` is itself the next carrier loss, with its divisor-sharing structure preserved.

**Threshold Bridge**

For the terminal base case, the banked terminal theorem gives finiteness for

```text
c < monomialThreshold(E_π, h_π)
  = min_ℓ (h_ℓ + 1) / (2 k_ℓ).
```

So to discharge

```text
CarrierFinite(π)
```

with threshold

```text
Θ(π) = ½ minAdm(remChain π),
```

you need the comparison

```text
½ minAdm(remChain π)
  ≤ monomialThreshold(E_π, h_π)
```

at every terminal profile.

The soundness gate alone does not prove this. It only proves that the high-regime exponent shift lands below the next combinatorial threshold. The terminal comparison is a separate bridge between the combinatorial `minAdm` budget and the actual monomial exponents produced by the route.

So: carrying `carrierThreshold(π) = ½ minAdm(remChain π)` is sound **conditional on** that terminal bridge. Without it, the predicate shape is still right, but the proof is not closed.

**π = ∅ Corollary**

At the empty profile:

```text
E_∅.loss = frobSq(prod M A),
h_∅ = empty,
Ω_∅ = original box,
Θ(∅) = ½ minAdm(M).
```

Thus `CarrierFinite(∅)` is exactly the desired `RouteMBoxThresholdFinite M`.

**Confidence**

High on Q1 and the step shape: the generator carrier is forced by the anisotropy and shared-divisor facts.

Moderate on the exact threshold convention `Θ(π)=½ minAdm(remChain π)`: it is the right budget for the shift theorem, but it depends on a separate terminal comparison theorem.

Most likely failure: the profile data may need a threshold depending not only on `remChain π` but also on the accumulated divisor vector `(E_π, h_π)`, if the terminal bridge is not uniformly true for all route terminals.
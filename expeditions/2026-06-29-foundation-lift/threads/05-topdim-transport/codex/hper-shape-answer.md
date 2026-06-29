1. **Yes: `hper` is independent of `hdim ∧ havoid`.**

Take a field `k`, let `R = k[t]_(t)` be the DVR with uniformizer `t`, and let `B = k[u]`. Set

```text
A = R × B,    f = (t, 1).
```

The minimal primes are

```text
p = (0) × B,      q = R × (0).
```

Both are top-dimensional, since

```text
A ⧸ p ≅ R,   dim R = 1,
A ⧸ q ≅ B,   dim B = 1,
dim A = max(dim R, dim B) = 1.
```

Also `f ∉ p` because `t ≠ 0` in `R`, and `f ∉ q` because `1 ≠ 0` in `B`, so `havoid` holds.

Now localize:

```text
A[1/f] ≅ R[1/t] × B[1/1] ≅ k(t) × B.
```

Thus

```text
dim A[1/f] = max(0, 1) = 1 = dim A,
```

so `hdim` holds.

But for the top minimal prime `p = (0) × B`,

```text
(A ⧸ p)[1/f̄] ≅ R[1/t] ≅ k(t),
```

so

```text
dim (A ⧸ p)[1/f̄] = 0 ≠ 1 = dim (A ⧸ p).
```

Thus `hper` fails. The DVR-alone example has the right per-component drop and `havoid` does allow a uniformizer, since in a domain `p = 0` and `t ∉ 0`; but the DVR alone does not satisfy `hdim`.

2. **`hper + havoid` implies `hdim` if there is at least one top-dimensional minimal prime.**

If `p ∈ TopDimMinPrimes A`, then `havoid` says `f ∉ p`, so `p` survives in `S = A[1/f]`. The quotient is

```text
S ⧸ pS ≅ (A ⧸ p)[1/f̄].
```

By `hper`,

```text
dim(S ⧸ pS) = dim(A ⧸ p) = dim A.
```

Since quotient dimension is at most ambient dimension and localization does not increase dimension,

```text
dim A ≤ dim S ≤ dim A,
```

so `dim S = dim A`.

So in the inhabited-top case, `hdim` is redundant.

But in the stated full generality, `hdim` is not derivable because `TopDimMinPrimes A` can be empty. Example: let

```text
A = k[x_{n,i} : n ≥ 1, 1 ≤ i ≤ n] /
    (x_{n,i} x_{m,j} : n ≠ m).
```

Its minimal primes are the ideals killing all variables outside one block `n`, and the corresponding quotient has dimension `n`. Hence `dim A = ∞`, but no minimal quotient has dimension `∞`, so `TopDimMinPrimes A = ∅`. Taking `f = x_{1,1}`, localization kills every other block and gives

```text
A[1/f] ≅ k[x_{1,1}, x_{1,1}^{-1}],
```

of dimension `1`. Thus `havoid` and `hper` are vacuous, while `hdim` fails.

3. **The shape of `hper` is correct for the proof, but slightly stronger than the bare local use.**

For a fixed `p ∈ TopDimMinPrimes A`, the proof only needs

```text
dim (A ⧸ p)[1/f̄] = dim S,
```

or, using `hdim` and `dim(A ⧸ p) = dim A`, equivalently the stated no-drop condition

```text
dim (A ⧸ p)[1/f̄] = dim(A ⧸ p).
```

Since `havoid` already says every top `p` satisfies `f ∉ p`, quantifying over all `p ∈ TopDimMinPrimes A` is effectively the same as quantifying over all surviving top primes. Without `havoid`, the cleaner combined hypothesis would be per-prime:

```text
∀ p ∈ TopDimMinPrimes A, f ∉ p ∧ dim (A ⧸ p)[1/f̄] = dim(A ⧸ p).
```

So the current `hper` is not mathematically too weak. It is only syntactically broader than necessary because survival is handled separately by `havoid`.

4. **With all three hypotheses, the conclusion should not fail mathematically.**

Localization gives a bijection between primes of `S` and primes of `A` avoiding `f`; it restricts to minimal primes. Forward direction uses `havoid + hper + hdim`. Reverse direction uses only `hdim` and dimension monotonicity:

```text
dim S/q = dim S = dim A,
dim S/q ≅ dim (A/p)[1/f̄] ≤ dim(A/p) ≤ dim A,
```

so `p` was already top-dimensional in `A`.

Thus no Noetherian hypothesis is needed for this basic mechanism. For `⊥`/`⊤` dimensions, the argument is convention-dependent but should still be order-theoretic if localization is monotone and `hdim` is literal equality.

Convention-dependent Lean warning: if `ncard` sends infinite sets to `0`, then the theorem’s “count” is lossy for infinite top-prime sets. A conclusion `0 = 0` may mean both sides are infinite, not that there are no top primes. But under the three hypotheses this is an interpretive issue, not a counterexample.

Verdict: per-prime `hper` necessary: **YES**; `hdim` separately necessary: **YES in full generality** (**NO** if `TopDimMinPrimes A` is known nonempty).
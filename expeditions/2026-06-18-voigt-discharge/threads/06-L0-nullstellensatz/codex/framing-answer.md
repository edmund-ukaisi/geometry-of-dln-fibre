**1. Recommendation**

Use a hybrid, with (A) as the main theorem. State the bridge algebraically with an explicit hypothesis
`hprime : (MvPolynomial.vanishingIdeal k Z).IsPrime`, and keep `IsZariskiClosed Z := Z = MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Z)` as a separate, topology-free predicate for faithful geometric wording. Do not build a global topology on `σ → k` at this layer; it adds API and typeclass cost without helping the `codimRep` consumer. If you want a reader-facing irreducibility predicate, define it through the `PrimeSpectrum` image, not by installing point-space topology.

**2. Cheap Dictionary**

Cheap if the predicate is:

```lean
def IsZariskiIrreducible (V : Set (σ → k)) : Prop :=
  IsIrreducible (MvPolynomial.pointToPoint (k := k) (K := k) '' V)
```

Proof outline:

1. Unfold `IsZariskiIrreducible`.
2. Apply confirmed lemma `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`.
3. Rewrite with confirmed lemma `MvPolynomial.vanishingIdeal_pointToPoint`.
4. Conclude:
   ```lean
   IsZariskiIrreducible V ↔ (MvPolynomial.vanishingIdeal k V).IsPrime
   ```

If instead you mean honest `IsClosed V` / `IsIrreducible V` on a newly installed topology on `σ → k`, that is not cheap at this pin. You would need to prove the induced topology has the intended closed sets and that irreducibility transports through `pointToPoint`; I would omit that from the bridge.

**3. Soundness Traps**

`ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)` is the dimension of the coordinate ring of the closed set defined by `I(Z)`, i.e. of the Zariski closure of `Z`. To call it “the variety dimension of `Z`” itself, require `IsZariskiClosed Z`.

No extra reducedness hypothesis is needed: vanishing ideals are radical, and prime implies radical anyway. No separate nonemptiness hypothesis is needed if you assume `(vanishingIdeal k Z).IsPrime`, since `⊤` is not prime and `vanishingIdeal k ∅ = ⊤`. Minimal faithful “irreducible closed variety” hypotheses are therefore:

```lean
hclosed : IsZariskiClosed Z
hprime  : (MvPolynomial.vanishingIdeal k Z).IsPrime
```

The algebraic equality itself only uses `hprime`; `hclosed` is for the geometric reading.

**4. Headline Form**

Do not make subtraction the headline. `ℕ∞` truncated subtraction is lossy, and `ringKrullDim` lives naturally in `WithBot ℕ∞`, so subtraction creates avoidable coercion and finiteness bookkeeping.

Recommended theorem shape:

```lean
theorem vanishingIdeal_height_add_dim_eq_card
    {Z : Set (σ → k)}
    (hprime : (MvPolynomial.vanishingIdeal k Z).IsPrime) :
    ((MvPolynomial.vanishingIdeal k Z).height : WithBot ℕ∞) +
      ringKrullDim
        (MvPolynomial σ k ⧸ MvPolynomial.vanishingIdeal k Z)
      =
    (Nat.card σ : WithBot ℕ∞)
```

Then specialize to `Z := coord '' Z` for `codimRep`. Add a subtraction corollary only later if a downstream statement really needs it.
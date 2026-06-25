**Verdict**

Do **not** expect Step B to fall out of the landed single-orbit engine. The identity

```lean
varietyDim (canonicalCoord d '' productRankLocus d r)
  = δ + varietyDim (canonicalCoord d '' fibre d E)
```

is a new homogeneous-family dimension theorem. It is much smaller than a fully general fibration theorem only if you state it as a specialized endpoint-sweep rung, but proving it still needs quotient/local-trivial/product-dimension content that the current engine does not have.

**Q1**

(a) **Product-variety route:** mathematically right, Lean-heavy.

`Σ^r` is not globally `Mat^{=r} × F`. It is the associated bundle

```text
H ×_{Stab(E)} F
```

over `H/Stab(E) = Mat^{=r}`. There are Zariski local sections on pivot charts, not a global regular section. A set-theoretic choice of normalizing matrices is useless for `varietyDim`.

The Lean blockers are:

```text
rank chart local triviality as an AlgEquiv/localized ring statement
product dimension: dim(U × F) = dim U + dim F
finite open cover/localization dimension bookkeeping
```

Mathlib v4.29 does not appear to have the needed general tensor-product Krull-dimension theorem for arbitrary f.g. domains, and `F` is reducible anyway. So this route is honest but not “clean” against the current engine.

(b) **Radical catenary route:** worth building, but it does **not** prove Step B.

A reusable good rung is:

```lean
height_vanishingIdeal_add_varietyDim_eq_card_of_nonempty
  [IsAlgClosed k] [Finite σ] {Z : Set (σ → k)} (hZ : Z.Nonempty) :
  (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞)
```

or the `codimRepCanonical` specialization. This should be true because `vanishingIdeal` is radical and proper, height is already `iInf` over minimal primes, and prime catenary is landed.

But Mathlib does not seem to already provide the other half:

```lean
ringKrullDim (R ⧸ I)
  = sup over p ∈ I.minimalPrimes of ringKrullDim (R ⧸ p)
```

You would need to build that. It is a good medium reusable rung and will simplify Step D and final dimension-to-codim conversion for reducible sets. It will not supply the sweep identity.

**Q2**

No clean sidestep. The statement

```text
codim_{Σ̄^r}(F) = δ
```

is just Step B/nofibre-jump in height language. Homogeneity tells you all exact-rank fibres are isomorphic, but to convert that into a codimension inside `Σ̄^r` you still need that the exact-rank part is an associated bundle over the rank orbit, or an equivalent flat/local-trivial argument.

The hidden wrong move is: “generic fibre dimension over irreducible base gives the closed fibre over `E`.” That needs no-jump/flatness/local triviality. Homogeneity can provide it only after formalizing the associated-bundle/local-chart mechanism.

**Q3**

Carry Step C as the **vanishing-ideal equality**, not as topology:

```lean
vanishingIdeal_productRankLocus_eq_productRankLocusLE :
  vanishingIdeal k (canonicalCoord d '' productRankLocus d r)
    =
  vanishingIdeal k (canonicalCoord d '' productRankLocusLE d r)
```

Then `varietyDim` rewrites by `rw [varietyDim, this]`.

This is the minimal Lean hypothesis. A closure equation is more geometric but less directly useful. I would cite LR 4.4/4.5 here unless you deliberately open a separate degeneration build. Proving it cheaply is not obvious: preimage of a dense base stratum is not automatically dense without an openness/dominance argument.

**Q4 Ranking**

1. **Auxiliary radical catenary:** highest mechanical value. It does not prove Step B, but it cleans Step D and the final `dim ↔ codim` passage for reducible sets. Build this if continuing the dimension route.

2. **Specialized homogeneous-sweep theorem:** mathematically the right Step B, but it is the hard new rung. State it narrowly, not as a general fibration theorem:

```lean
endpointSweep_varietyDim
  (E rank r normal form) :
  varietyDim (canonicalCoord d '' productRankLocus d r)
    = δ + varietyDim (canonicalCoord d '' fibre d E)
```

Internally it needs: sweep set equality, stabilizer-coset fibres, and local-trivial/product-dimension machinery.

3. **Product-variety/local-trivial bundle route:** same substance as 2, but more exposed to missing tensor/localization dimension APIs. Use it only as the proof plan for the specialized theorem, not as a broad library theorem.

4. **Nested catenary sidestep:** lowest. It looks algebraic, but the missing hypothesis is exactly no-jump/flatness/local triviality over the exact-rank stratum.

**Biggest Risk**

The dangerous subtly-wrong statement is:

```text
Σ^r is dimension-equivalent to Mat^{=r} × F because all exact-rank fibres are isomorphic.
```

Fibrewise isomorphism plus transitive base action is not by itself a Lean dimension theorem. You need a regular associated-bundle/local-trivial structure, or you have only a set-theoretic parametrization.
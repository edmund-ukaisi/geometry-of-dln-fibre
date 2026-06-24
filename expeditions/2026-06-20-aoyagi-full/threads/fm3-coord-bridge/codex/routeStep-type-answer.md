Yes: **split + codim alone is too weak**. It gives a syntactic recursion, not a mathematical resolution. The per-cell datum, or an equivalent validity certificate, must be threaded somewhere the reconstruction theorem can see.

**1. The Type**

`RouteStep.branch` should bundle the per-cell factorisation datum, or bundle a per-cell certificate from which the transport lemmas can be applied.

A corrected shape is roughly:

```lean
inductive RouteStep (M : Fin (L+1) → ℕ) : Type 1
  | leaf
      (md : MonoData)
      -- ideally also a proof/certificate that md represents dlnLoss M 0 locally
  | branch
      (cells : Type)
      (cellsFin : Fintype cells)
      (split : cells → ChainDimSplit M)
      (codim : cells → ℕ)

      -- data consumed by the crux2 transport theorem:
      (flatCore : (c : cells) → ...)
      (G : (c : cells) → ...)
      (redEmbed : (c : cells) → ...)
      (c₁ c₂ : (c : cells) → ...)
      (squeeze :
        (c : cells) →
          IsSchurStraightenSqueeze
            M
            (split c)
            (flatCore c)
            (G c)
            (redEmbed c)
            (c₁ c)
            (c₂ c))

      -- if not already contained in `squeeze`, also:
      (reduced :
        (c : cells) →
          /* G c is germ/equal/transport-equivalent to dlnLoss (split c).red 0 */)

      -- if not already implied by the chart construction:
      (cover :
        /* these cells cover the germ/neighbourhood whose rlct is being computed */)
```

I cannot name the exact Lean types for `flatCore`, `G`, `redEmbed`, or `cover` without the files, but structurally those are the missing fields.

The minimum invariant is:

```lean
(c : cells) →
  PerCellTransportDatum M (split c) (codim c)
```

where `PerCellTransportDatum` packages exactly the hypotheses needed to prove

```lean
rlctAtOn (dlnLoss M 0) 0
  = nodeContribution (codim c)
    + rlctAtOn (dlnLoss (split c).red 0) 0
```

locally/on that cell, plus the finite-cover/gluing statement that takes the infimum over cells.

So: **yes, the datum existence is what makes the produced `(d,k,h)` meaningful.** It does not have to live literally inside `RouteStep.branch`; it could live in a separate `ValidRouteStep M step` predicate. But then `routeAtlas` alone is only combinatorics, and every serious theorem must assume/use `ValidRouteStep`.

**2. Separability**

The dispatcher and the final identity are separable, but only after enriching the interface.

Clean architecture:

```lean
routeStep : (M : Fin (L+1) → ℕ) → RouteStep M
routeStep_valid : (M : Fin (L+1) → ℕ) → ValidRouteStep M (routeStep M)
```

or equivalently:

```lean
routeStep : (M : Fin (L+1) → ℕ) → CertifiedRouteStep M
```

Then you can prove a generic fold theorem:

```lean
routeAtlas_correct :
  ∀ M,
    rlctAtOn (dlnLoss M 0) 0
      =
    ⨅ i : (routeAtlas M).ι,
      monomialThreshold
        ((routeAtlas M).d i)
        ((routeAtlas M).k i)
        ((routeAtlas M).h i)
```

using only the certified branch fields and recursive hypotheses.

So the identity proof does **not** have to be interleaved manually into the dispatcher construction. But the recursive correctness proof must be interleaved with the same well-founded recursion or proved by well-founded induction matching `routeAtlas`. That is normal.

What is not separable is this pair:

```lean
routeStep : M → RouteStep M  -- raw arbitrary split
```

and

```lean
routeAtlas_correct : ...
```

There is no honest theorem from raw `RouteStep` alone to the loss identity. The theorem needs the per-node transport/cell-cover certificates.

**3. Minimal Honest Next Step**

Ranking:

1. **Best next step: enrich `RouteStep` or add `ValidRouteStep`, then re-green the skeleton.**

   I would prefer a separate certificate first:

   ```lean
   def ValidRouteStep (M) : RouteStep M → Prop := ...
   ```

   because it lets you keep the computational dispatcher shape visible while making correctness impossible to state without the certificate. Once stable, you can collapse to `CertifiedRouteStep` if that is ergonomically better.

2. **Then prove the generic fold theorem.**

   Prove:

   ```lean
   routeAtlas_correct_given_valid_steps
   ```

   assuming every branch carries the squeeze/reduced/cover data. This validates that the recursion architecture is mathematically connected to `dlnLoss`.

3. **Only after that fill the actual dispatcher.**

   The dispatcher’s real obligation is not “choose smaller reds”; it is “construct finite cells, decreasing splits, and the per-cell transport datum proving these cells really factorise the loss.”

So the smallest non-vacuous milestone is:

```lean
RouteStep + ValidRouteStep + routeAtlas skeleton + statement of generic correctness
```

and ideally the first real proof should be the per-node fold:

```lean
node_correct :
  ValidRouteStep M step →
  (∀ c, recursive correctness for (split c).red) →
  correctness for M
```

That theorem is the guardrail.

**4. Vacuity Trap**

Confirmed.

Filling `routeStep` with arbitrary splits is worse than leaving it `sorry` if downstream code treats `routeAtlas` as a resolution of `dlnLoss M 0`. It creates a misleading object: Lean will happily build some atlas indexed by decreasing widths, but there is no mathematical connection to the original loss.

The guard is: never expose/use

```lean
routeAtlas M
```

as a resolution object unless paired with a proof like

```lean
RouteAtlasCorrect M (routeAtlas M)
```

or built from certified steps.

In short:

```lean
raw routeAtlas      -- okay as recursion plumbing
certified routeAtlas -- needed for mathematics
```

A raw dispatcher proves termination. A certified dispatcher proves resolution. Those should be different layers, or one bundled type.
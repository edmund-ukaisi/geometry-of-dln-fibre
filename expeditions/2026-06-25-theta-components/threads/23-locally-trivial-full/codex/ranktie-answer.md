**1. Honest Rank-Tie**

(A) is the honest low-cost rank-tie:

```lean
rank ≤ r  ⟹  (some r×r deep minor is nonzero/unit ↔ rank = r)
```

It genuinely says: on the rank-≤r closure, the `r×r` minors cut out the complement of rank `< r`, on `k`-points.

But it is not the prime-level statement. A careful algebraic geometer would accept (A) as the expected `k`-point description of the open. They would not accept it as a formal equality with `rankROpen : Set (PrimeSpectrum ...)` unless you add a scheme/prime bridge.

The better scheme-level bridge is not necessarily Nullstellensatz; it is:

```lean
P ∈ rankROpen ↔ rank of the universal matrix over κ(P) is r
```

Nullstellensatz/maximal ideals is only needed if you specifically want to identify closed `k`-points of `Spec` with your `RepCoord d → k` points.

**2. Does (A) Earn `locallyTrivial`?**

No, not by itself.

(A) proves the open has the expected `k`-points. It does not compose with the atlas cover

```lean
⨆ basicOpen(chartDsigAt) = rankROpen
```

because that cover is a statement about primes.

So:

- `locallyTrivialOnRankROpen` is honest if your actual theorem is over `rankROpen : Set (PrimeSpectrum sweepSigmaRing)` and the basic-open trivializations cover it.
- `locallyTrivialOnRankLocus` meaning “over `sweepSigma` / rank-=r `k`-points” is not licensed by (A).
- If the only new thing you prove is (A), keep the headline closer to `pivotLocalProductAtlas` plus a separate `kPoint_rankTie` theorem.

**3. Exact Lean Shape**

Cleanest honest target, independent of `sweepSigma` image-definition baggage:

```lean
def chartCoverKPoint (k d r) : Set (RepCoord d → k) :=
  {x | ∃ s t,
      Function.Injective s ∧ Function.Injective t ∧
      IsUnit (MvPolynomial.eval x (ΔPdeepAt d r s t))}

def rankLeKPoint (k d r) : Set (RepCoord d → k) :=
  {x | Matrix.rank (multAt d x) ≤ r}

def rankEqKPoint (k d r) : Set (RepCoord d → k) :=
  {x | Matrix.rank (multAt d x) = r}

theorem chartCoverKPoint_iff_rankEq_of_rankLe
    [Field k] {x : RepCoord d → k}
    (hx : x ∈ rankLeKPoint k d r) :
    x ∈ chartCoverKPoint k d r ↔ x ∈ rankEqKPoint k d r
```

Then the set form:

```lean
theorem rankEqKPoint_eq_chartCoverKPoint_inter_rankLe
    [Field k] :
    rankEqKPoint k d r =
      chartCoverKPoint k d r ∩ rankLeKPoint k d r
```

If you also have or prove

```lean
x ∈ sweepSigma k d r ↔ x ∈ rankEqKPoint k d r
```

then add:

```lean
theorem sweepSigma_eq_chartCoverKPoint_inter_rankLe
    [Field k] :
    sweepSigma k d r =
      chartCoverKPoint k d r ∩ rankLeKPoint k d r
```

(A) needs a field, not algebraic closedness. Algebraic closedness enters only for the closed-point/maximal-ideal bridge.

**4. Naming Verdict**

After only (A): do not rename the main object as `locallyTrivialOnRankLocus`.

Maximally honest names:

```lean
chartCoverKPoint_iff_rankEq_of_rankLe
rankEqKPoint_eq_chartCoverKPoint_inter_rankLe
pivotLocalProductAtlas_rankTieKPoint
```

Use a `locallyTrivial...` name only if the theorem itself is over the prime open:

```lean
reducedFibre_locallyTrivialOnRankROpen
```

and the statement mentions `rankROpen`, not `sweepSigma`. Otherwise the genuine residual is the prime/scheme bridge, not more k-point rank algebra.
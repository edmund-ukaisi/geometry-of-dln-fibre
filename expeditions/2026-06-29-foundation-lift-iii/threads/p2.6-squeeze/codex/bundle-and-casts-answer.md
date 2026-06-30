**(Q1) HYPOTHESIS-BUNDLE HONESTY — CLEAN**

(a) `δAdj+L+hMC+hRank`: genuine inputs for B1. `hRank` is an explicit rank-tie input, not silently concluded here.

(b) `hcrit+[CharZero]`: `hcrit` is genuinely used for the trdeg bound. `[CharZero k]` is not visibly used once `hcrit` is assumed; likely provenance/redundant at this abstraction, but not dishonest.

(c) `H+[FiniteDimensional Cotangent]`: genuine inputs for B3; no smuggled equality.

(d) `[IsSmoothAt]+hrat+[PerfectField]+[IsMaximal]`: genuine B4 bundle. `[PerfectField]`, smoothness, maximality, and rational residue field are explicit, not hidden in the conclusion.

(e) `hZ+hIker`: genuine alignment hypotheses. `hZ` feeds B4; `hZ.trans hIker` feeds A4.1. No direction issue.

Conclusion is exactly an object equality in `ℕ∞`:

```lean
varietyDim Z = (finrank k (LinearMap.range G.δ) : ℕ∞)
```

It is not a codimension statement and not an rlct statement. Only nonminimal-looking item from the displayed composition is `[CharZero k]`, since `hcrit` is already explicit.

**(Q2) COMPOSITION + CASTS — SOUND**

`hge`: after `rw [← hB4]`, the goal is

```lean
(r : ℕ∞) ≤ (finrank k (m.Cotangent) : ℕ∞)
```

and `hB3 : r ≤ finrank k (m.Cotangent)` is an `ℕ` inequality. `exact_mod_cast hB3` is honest: it applies the monotone `ℕ → ℕ∞` coercion in the same direction.

`hle`: `htrdeg : trdeg.toNat ≤ genericDifferentialRank ...` and `hB1 : genericDifferentialRank ... ≤ r` are both `ℕ` inequalities, so

```lean
htrdeg.trans hB1 : trdeg.toNat ≤ r
```

is an `ℕ` chain. After `rw [hA41]`, the goal is the casted `ℕ∞` version, and `exact_mod_cast` is directionally correct.

`le_antisymm hle hge` closes exactly

```lean
varietyDim Z = (r : ℕ∞)
```

with `r` definitionally `finrank k (LinearMap.range G.δ)`.

Single most likely hiding place, if any, is not the squeeze or casts; it would be A4.1’s finite-dimensional/trdeg `.toNat` bridge. But given A4.1’s stated conclusion as a brick, the headline composes it correctly.
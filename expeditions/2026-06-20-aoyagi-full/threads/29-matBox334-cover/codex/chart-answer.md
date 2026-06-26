**VET-1**

SOUND. On `chartDomOn univ p`, `flatBox334 (pivotBlowupOn univ p y)` is equivalent to `|y p| ≤ 1`.

Reason: the `p` coordinate is exactly `y p`, so box membership forces `|y p| ≤ 1`. For `k ≠ p`, the blown-up coordinate is `y p * y k`, and the chart hypothesis gives `|y k| ≤ 1`, so `|y p| ≤ 1` forces `|y p * y k| ≤ 1`. No hidden converse dependence on the ratios. Excluding `pivotZeroOn p` is not needed for this equivalence, only for the chart decomposition / radial singular handling.

**VET-2**

right-object, assuming the displayed theorem is exactly the `recStep` summand after rewriting the determinant. It is not vacuous: the domain is `chartDomOn univ p \ pivotZeroOn p`, the weight is `|y p|^8`, and the box indicator correctly restricts the radial coordinate to `|y p| ≤ 1`.

The `K = 3` choice is sound from the given bounds. If after the normal-form change variables the shifted `Δ` entries lie in `[-2,2]` and the `T` entries lie in `[-3,3]`, then a single `resolved334_box_lt_top 3` covers both because `[-2,2] ⊆ [-3,3]`. Different radii per block are not mathematically necessary unless the banked theorem’s `box22 K`, `box24 K`, or `morseBox 4 K` have asymmetric definitions not described here.

**VET-3**

sound, with one consistency condition. Row/column permutations are measure-preserving on symmetric boxes like `matBox 3 3 1` and `matBox 3 4 1`, because they only reorder coordinates. The induced A1 row permutation is also measure-preserving on `matBox 3 4 1`.

The algebra is sound if applied consistently: for row permutation `P` on A0 and column permutation `Q` on A0, replace `A0` by `P A0 Q` and `A1` by `Q⁻¹ A1`. Then `(P A0 Q)(Q⁻¹ A1) = P(A0 A1)`, and `frobSq` is invariant under the final row permutation `P`. The likely subtlety is using the inverse row permutation on `A1`, not the same permutation with the wrong orientation.

**Most Likely Failure Point**

The proof is most likely to go wrong at the change-of-variables/permutation bookkeeping: applying the A1 row permutation in the wrong direction or proving the normal-form bound for a permuted `R` while feeding the unpermuted `A1`.

Cheapest guard: state a small standalone lemma with the exact permutation convention:
`frobSq ((rowPerm i (colPerm j R)) · rowPermA1 j A1) = frobSq (R · A1)`,
then use that lemma everywhere before invoking the `(0,0)` pivot bound.
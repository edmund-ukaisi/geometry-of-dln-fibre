**Verdict:** faithful. I do not see an off-by-one or overclaim in the theorem statement itself.

1. **Hypotheses.** Yes: `a < c`, `c ≤ b.castSucc`, `b.succ ≤ e` encode exactly
`a < c ≤ b < e`, with `b.castSucc` the vertex `b` and `b.succ` the vertex `b+1`. The overlap `[c, b.castSucc]` is nonempty because `c ≤ b.castSucc`, and it is a genuine two-strand overlap for the two upstairs intervals. Non-vacuous: the witness `N = 2`, `a=0`, `c=1`, `b=1`, `e=2` satisfies it. No off-by-one problem, provided readers remember `b : Fin N` is an edge and `b.castSucc` is the vertex endpoint called `b`.

2. **Downstairs.** Yes. The downstairs list `(a, b.castSucc) :: (c, e) :: rest` is exactly
`M_[a,b] ⊕ M_[c,e] ⊕ rest`. This is the correct recombination
`[a,e] & [c,b] ↦ [a,b] & [c,e]`. Dimension-vector preservation is the right invariant: pointwise,
both sides have dimensions `1,2,1` across the regions `[a,c)`, `[c,b]`, `(b,e]`.

3. **Left association.** Faithful, but with a Lean-level caution. Mathematically,
`(M_[a,e] ⊕ M_[c,b]) ⊕ rest` is the same direct sum as the unparenthesized upstairs object, up to canonical block reindexing/base change. So this does not understate or misstate the informal orbit-closure claim.
The caution is that in raw Lean this is not definitionally the same as the right-nested
`intervalDirectSum ((a,e)::(c,b)::rest)`: the ambient dimension expression and `Fin` block indices differ. Thus the theorem names the left-associated orbit literally. Any later use requiring the right-nested list orbit needs an explicit associativity/reindexing/orbit-equivalence bridge.

4. **Closure only.** Correct. The statement is one point membership:
`canonicalCoord downstairs ∈ zeroLocus(vanishingIdeal(orbitSet upstairs))`. This is the `k`-point Zariski closure of the orbit point-set, in the polynomial-zero-set sense. It does not claim rank-locus equality, fibre equality, or Theorem 3.8 as a global closure/rank-locus statement.

5. **Crossing-rank indicator.** The boolean is correct:
`j ≤ e ∧ ((λ ≠ 0 ∧ a ≤ i) ∨ c ≤ i)`.
In the crossing regime, the short target is dead past `b`, so there is at most one live target row, namely the long strand, and only if `j ≤ e`. The source reaches the recombination row through the short strand iff `c ≤ i`, with entry `1`; through the long strand iff `a ≤ i`, with entry `λ`.

At `λ ≠ 0`, the condition becomes
`j ≤ e ∧ (a ≤ i ∨ c ≤ i)`, which is equivalent to `j ≤ e ∧ a ≤ i` because `a < c`. That is the upstairs crossing rank of `M_[a,e] ⊕ M_[c,b]`.

At `λ = 0`, it becomes
`j ≤ e ∧ c ≤ i`, which is the downstairs crossing rank of `M_[a,b] ⊕ M_[c,e]`. No off-by-one issue there.

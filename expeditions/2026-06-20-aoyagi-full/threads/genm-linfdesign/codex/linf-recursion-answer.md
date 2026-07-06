**Verdict**

Bounded, but large. I do **not** see a research-level obstruction for the finiteness direction if you formalize it as a finite tree of **explicit monomial charts with one-sided bounds**, rather than trying to formalize the full ideal-equality/multiplicity proof. Once a chart gives `frobSq(P) ∘ φ = monomial^2 * unit * residual` and the Jacobian is `monomial * unit`, leaf finiteness is the standard normal-crossing calculation by reducing to `∫_0^1 x^α dx`. Aoyagi’s 2025 paper explicitly cites the 2024 deep-linear result, recalls exactly this monomialization-to-threshold mechanism, and mathlib has had a general change-of-variables formalization for integrals since 2022. ([arxiv.org](https://arxiv.org/pdf/2501.12747.pdf))

1. **Q1. Feasibility.**  
For **finiteness only**, I would classify this as a bounded “large-but-mechanical” Lean build. The likely wall is not missing analysis; it is proof engineering: finite chart bookkeeping, index arithmetic, and setting up a recursion that remembers the accumulated exceptional-divisor weight. If you instead try to formalize the full Aoyagi theorem literally, including exact ideal equality and `θ`, that becomes much closer to a wall.

2. **Q2. Recursion structure.**  
Use a recursion on a **state**, not on arity `L` alone. The right state is essentially “current carried diagonal block + where you are inside it”, i.e. Aoyagi’s `(S,J)` plus one small combinatorial complexity parameter for the unresolved equal-order run. I would separate it into two layers:  
`(i)` a **combinatorial chart-tree builder** on a lex well-founded state such as `(S, J, K)`;  
`(ii)` an **analytic induction on that finite tree** proving finiteness.

The induction statement should be strengthened to a **weighted integral**, not just the raw box integral:
```text
Iσ(c) := ∫_{Uσ} wσ(u) * Fσ(u)^(-c) du < ∞,
```
where `Fσ` is the current residual product-norm expression and `wσ` is the accumulated Jacobian monomial from previous blow-ups. On each child chart you want a statement of the shape
```text
Fσ ∘ φ = m(u)^2 * Fτ(v) * U(u,v),   a ≤ U ≤ b,
|Jac φ| ≤ C * n(u),
```
so that Tonelli plus the substitution gives
```text
Iσ(c) ≤ C * (∏new vars ∫_0^1 t^(αi - 2c βi) dt) * Iτ(c).
```
That is exactly where the “sum across boundaries” enters: each step contributes a new monomial power from the current boundary, while the child carries the previous ones. The two-matrix corank recursion fails because its induction statement forgets that accumulated weight.

3. **Q3. What can be avoided.**  
`(a)` You do **not** need the full total-order invariant on the `T_{s,k}` as a standalone end theorem. You only need enough of it to certify, on each chart, that a chosen monomial divides the active terms and that the residual problem is a valid child state. In Lean, I would store that as a **chart certificate**, not as a global algebraic theorem.  

`(b)` You do **not** need exact leaf exponents if your value lane is already banked. For finiteness, one-sided bounds are enough: a lower bound on `frobSq(P) ∘ φ` by `const * monomial^2 * residual`, and an upper bound on `|Jac φ|` by `const * monomial`. Exact equality is only needed for the exact threshold/multiplicity story.  

`(c)` Yes: organize the global argument as a **finite sum over a finite chart family** on the box. You do not even need a disjoint partition; for a nonnegative integrand, a finite overlapping cover gives `∫_union ≤ Σ ∫_chart`. Outside a neighborhood of the singular set, the integrand is bounded.

4. **Q4. Main risks.**  
First, **globalization from a germ to the whole box**. The origin proof is not enough by itself; you need a finite family of local models covering all singular points in `B`, with unit factors uniformly bounded away from `0` on each chosen chart domain. I think this is true and finite, but it is the biggest bookkeeping burden.

Second, **using the wrong change-of-variables interface**. Mathlib does have change-of-variables formalized, so this is not a missing-theorem problem. But for these explicit blow-ups I would avoid a fully general diffeomorphism API where possible and instead prove custom **fiberwise scaling lemmas** via Tonelli/Fubini; the maps are triangular enough that this is usually much cleaner. ([arxiv.org](https://arxiv.org/abs/2207.12742?utm_source=openai))

Third, **case-split/index explosion**. I expect Case 1 / Case 2 to be genuinely exhaustive and uniform, but Lean will punish ad hoc `Fin` arithmetic. Package the cases as a small inductive datatype of local configurations and keep the index transport lemmas separate from the measure-theory lemmas.

5. **Q5. Alternative.**  
I do not see a fundamentally simpler route that still reaches the **sharp** threshold `½·minAdm(M)`. A plain induction on `L` or a Hölder/Brascamp-Lieb style estimate is too coarse: it does not remember how vanishing orders accumulate across successive rank-drop boundaries. The only plausible simplification is to replace the full Aoyagi ideal proof by a weaker induction on a “carried diagonal-block state” with weighted integrals. That is a bit more Lean-tractable than formalizing the paper literally, but mathematically it is still the same monomial-blow-up mechanism in disguise.

If I were planning the development, I would aim for: **finite chart tree + weighted integral induction + fiberwise monomial substitutions**, and I would explicitly avoid formalizing exact ideal equality, multiplicity `θ`, or a general blow-up framework.
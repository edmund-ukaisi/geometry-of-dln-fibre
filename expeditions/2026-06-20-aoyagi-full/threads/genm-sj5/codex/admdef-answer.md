## Q1 — `d = 0`

**Verdict: SOUND-BUT-PROVABILITY-BURDEN.**

[DERIVED] Since exceptional divisors are indexed by `Fin d`, `d = 0` means there are none. Thus a condition quantified over critical exceptional divisors is genuinely vacuous. The explicit disjunct is necessary because the alternative formula still begins with `∃ i₀ : ι`; it is false when `ι` is empty even though there are no divisors to test.

[DERIVED] The predicate is nevertheless loose with respect to `coeff`: `genuineCarrier` constrains `ctx`, `Z`, and `dom`, but not the linear residual. Hence a `d = 0` decoration can satisfy `adm` while its loss is a degenerate projection of the product—or even identically zero.

Such an admitted decoration can have a divergent integral. For example, zero `coeff` gives zero loss everywhere, so its negative power is infinite for `c' > 0`. More precisely, rank deficiency alone does not always imply divergence: a rank-one quadratic has local threshold `c' < 1/2`; it diverges only when the requested range reaches or exceeds that threshold.

[DERIVED] This does **not** make the specialization at the trivial decoration wrong. Enlarging `adm` only strengthens the universal obligations:

- A divergent admitted two-node decoration makes `DecoratedBaseHyp` unprovable.
- Other extra decorations may likewise make an induction step unprovable.
- But if the universal decorated theorem has actually been proved, applying it to the admitted trivial decoration remains valid.

Thus the looseness threatens only discharge of the base/step hypotheses, not the conclusion. If `DecoratedBaseHyp` were simply postulated despite a counterexample, the resulting theorem would depend on a false assumption; that is a hypothesis gap, not an invalid specialization.

## Q2 — transport along `hν`

**Verdict: SOUND, not a DODGE; potentially TOO-RIGID as an induction invariant.**

[DERIVED] For fixed `hν : ν = I`, where `I = Fin(M₀) × Fin(M_last)`, transport gives an invertible identification

\[
(\nu\to\mathbb R)\;\longleftrightarrow\;(I\to\mathbb R).
\]

Therefore the displayed equality is equivalent, after transporting back, to saying that `(ctx z).2` is exactly the product function expressed in the original `ν` type. The cast cannot turn an arbitrary function into the product. The freedom in `e` permits measure-preserving reparametrization of `Z`, but does not make the equation vacuous.

[DERIVED] Requiring type equality is rigid. A genuinely smaller row-eliminated index type cannot satisfy `hν`; even an merely equivalent presentation of the same index set may not provide type equality in Lean.

[INFERRED] Whether this is a gap depends on the peel implementation:

- If the peel keeps `ν` fixed and records elimination in `coeff`, `supp`, or reconstruction data, this is a legitimate design constraint.
- If the peel actually replaces `ν` by a smaller type, preservation of `genuineCarrier` fails. That is a real proof-design gap requiring either a fixed-index reformulation or a suitably controlled equivalence/reconstruction-based predicate.

Overall, `adm` is sound for the stated specialization: the trivial decoration yields the intended plain loss and goal. The main risk is that the admitted class is analytically too broad for the base/step, while the fixed-`ν` constraint must be explicitly preserved by every peel.
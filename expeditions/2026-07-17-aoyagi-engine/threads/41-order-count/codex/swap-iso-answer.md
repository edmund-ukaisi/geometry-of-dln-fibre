## 1. `swapProfile`

Use the repository’s zero-based width index. Put `r := k.val`.

- If `r = 0`, the swap is `M 0 ↔ M 1`; define `swapProfile M k T := T`.
- If `r > 0`, set
  \[
  i=\langle r-1,\_\rangle:\mathrm{Fin}\,L,
  \quad
  P=\begin{cases}M\,0&r=1,\\T\langle r-2,\_\rangle&r>1,\end{cases}
  \]
  \[
  X=T\,i,\qquad Q=T\,k,\qquad
  A=M(k.\mathrm{castSucc}),\qquad B=M(k.\mathrm{succ}).
  \]
  Then
  \[
  \operatorname{swapProfile}(M,k,T)
  =\operatorname{Function.update}\ T\ i\ (\operatorname{swapR}P X Q A B).
  \]

The proof obligations for the `Fin` constructors are all `omega`: from `r>0` and `k.isLt`.

Establish accessor lemmas immediately:

- value at `i` is `swapR P X Q A B`;
- every `j ≠ i` is unchanged;
- in particular `P` and `Q` are unchanged.

The inverse is
\[
\operatorname{swapProfile}(\operatorname{swapWidths}kM,k,-).
\]
After the width swap its parameters are `P,Q,B,A`. Prove the pure lemma
\[
Q\le X\le P\Longrightarrow
 R_{B,A}(P,R_{A,B}(P,X,Q),Q)=X
\]
by splitting on `A ≤ B` and the translation/reflection tests; `omega` closes the natural-subtraction bookkeeping. Together with `swapWidths_swapWidths`, this gives both profile round trips.

For `r=0`, everything is identity on profiles.

## 2. `Mval` invariance

First fix the indexing: the Lean definition is
\[
Mval(M,T)=\sum_{j:\mathrm{Fin}\,L}
(tPrev_j-T_j)(M_{j+1}-T_j),
\]
whose first term is `(M 0 - T 0)(M 1 - T 0)`. The prompt’s displayed `M¹,M²` is compatible only if those are the paper’s one-based names for Lean’s `M 0,M 1`.

For `r>0`, only the summands at `i=r-1` and `k=r` change. Their original total is
\[
F_{A,B}(P,X,Q)
=(P-X)(A-X)+(X-Q)(B-Q).
\]
Writing \(Y=R_{A,B}(P,X,Q)\), the new total is
\[
F_{B,A}(P,Y,Q)
=(P-Y)(B-Y)+(Y-Q)(A-Q).
\]

Over `ℤ`, define
\[
\Phi_{A,B}(P,X,Q)
=(P-X+A)^2+(X-Q+B)^2.
\]
A ring calculation gives
\[
\Phi_{A,B}
=2F_{A,B}+P^2+A^2+B^2-Q^2.
\]
The constant is symmetric in `A,B`.

There are two algebraic possibilities:

- Translation: \(Y=X+B-A\). Then
  \[
  P-Y+B=P-X+A,\qquad Y-Q+A=X-Q+B.
  \]
- Reflection: \(Y=P+Q-X\). Then
  \[
  P-Y+B=X-Q+B,\qquad Y-Q+A=P-X+A.
  \]

Thus translation preserves the two squares and reflection exchanges them, proving
\[
F_{B,A}(P,Y,Q)=F_{A,B}(P,X,Q).
\]
The reflection branch does not break invariance.

For Lean, split the `swapR` branches, use the branch inequalities plus `Q ≤ X ≤ P` to rewrite casts of truncated subtraction, and finish the integer identities with `ring`. Decompose the `Finset.univ` sum by erasing `i` and `k`; every remaining summand is definitionally unchanged.

For `r=0`, `T` is unchanged and the first summand merely exchanges its two factors.

Value preservation needs `T ∈ Adm M` only for `Q ≤ X ≤ P` and exact interpretation of the natural subtractions. It does not require that `T` be binding.

## 3. Admissibility preservation

Important: `swapProfile` does not preserve all admissible profiles. For example,
\[
(P,X,Q,A,B)=(2,0,0,2,1)
\]
takes the reflection branch and produces \(Y=2>B\). Binding/local minimality is essential.

If `T ∈ bindingSet M`, varying only `X` through
\[
Q\le Z\le\min(P,A)
\]
produces another admissible profile. Hence global minimality implies that `X` minimizes \(F_{A,B}(P,-,Q)\) on this interval.

Put \(d=|A-B|\). The two crucial endpoint lemmas are:

- If `A ≤ B` and the translation test fails, so `P-X < d`, then `X=Q`. Otherwise `X-1` is feasible and
  \[
  F(X-1)-F(X)=P+Q-d-2X+1<0,
  \]
  contradicting minimality. Consequently the reflection gives `Y=P`; moreover `P-X<d` and `X≤A` imply `P≤B`.

- If `B < A` and the translation test fails, so `X-Q<d`, then `X=P`. First, if `X<min(P,A)`, then
  \[
  F(X+1)-F(X)=2X+1-(P+Q+d)<0.
  \]
  Thus `X=min(P,A)`. Since admissibility gives `Q≤B`, the alternative `X=A` contradicts
  \(X-Q< A-B\). Hence `X=P`, and reflection gives `Y=Q≤B`.

The `Adm` clauses then follow:

- Weak decrease: only the adjacent inequalities around `i` change; prove `Q ≤ Y ≤ P`.
- Central bound: prove `Y ≤ B`; when `r=1`, also `Y≤P=M 0`, giving `Y≤min(M 0,B)`.
- The bound on unchanged `Q` becomes `Q≤A`, following from `Q≤X≤A`.
- Other bounds are unchanged.
- The last coordinate is unchanged because `i=r-1` is never the last index.

To prove equality of minimum values without importing permutation invariance, choose a minimizer on each side. Mapping a source minimizer gives
\(\min_{\mathrm{swap}}\le\min_M\); applying the inverse construction to a swapped minimizer gives the reverse inequality. Hence the minima agree, and value invariance upgrades admissibility preservation to
\[
T\in bindingSet(M)\Longrightarrow
swapProfile(M,k,T)\in bindingSet(swapWidths\,k\,M).
\]

Positivity of widths is not used by this atomic argument.

## 4. Monotonicity and assembly

Let `T ≤ S` be binding profiles. Their local data satisfy
\[
P\le P',\qquad X\le X',\qquad Q\le Q'.
\]
Atomic `swapR` is not monotone on arbitrary triples; use the endpoint lemmas above.

If `A ≤ B`, write `d=B-A`. Translation outputs `X+d`; reflection outputs `P`.

- translation/translation: use `X≤X'`;
- translation/reflection: `X+d≤P≤P'`;
- reflection/translation: `P<X+d≤X'+d`;
- reflection/reflection: use `P≤P'`.

If `B<A`, write `d=A-B`. Translation outputs `X-d`; reflection outputs `Q`.

- translation/translation: use `X≤X'`;
- translation/reflection: `X'-Q'<d` implies `X-d≤Q'`;
- reflection/translation: `Q≤Q'≤X'-d`;
- reflection/reflection: use `Q≤Q'`.

This proves forward monotonicity on `bindingSet`. For order reflection, apply the same monotonicity theorem to swapped widths and then simplify both round trips:
\[
swapProfile(T)\le swapProfile(S)\Longrightarrow T\le S.
\]

The clean Lean assembly is `OrderIso.ofHomInv`:

1. forward `OrderHom` from `swapProfile M k`;
2. inverse `OrderHom` from `swapProfile (swapWidths k M) k`;
3. the two round-trip lemmas.

Then return the resulting order isomorphism inside `Nonempty`.

The hazard is proving only forward monotonicity and bijectivity: that does not give an order isomorphism. It bites at `map_rel_iff'`. Using two `OrderHom`s makes the required inverse monotonicity explicit.
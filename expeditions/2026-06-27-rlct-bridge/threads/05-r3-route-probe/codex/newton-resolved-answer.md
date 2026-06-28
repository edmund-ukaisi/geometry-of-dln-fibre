**Q1: VIABLE-as-uniform-monomial-tower.**

For the all-width-2 chain, after the SVD/rank and Morse reductions, the deepest residual is

```text
w1^2 + w2^2 + delta^2 s^2 + delta^2 v^2.
```

This is a sum of squares of monomials. Every compact Newton face is again a positive sum of monomial squares, so on the real torus `(R*)^n` the face polynomial never vanishes. Hence there is no torus critical point. That is exactly the Newton-nondegeneracy check. So the width-2 case does not force the full Aoyagi recursive divisor bookkeeping, provided we are already in the rank/incidence coordinates. It is not solvable by Newton theory in the original entries, but it is solvable by the clean monomial incidence tower.

**Q2: the uniform scheme does not survive in general widths.**

The obstruction is the genuine corank >= 2 residual

```text
F(Delta,S) = ||Delta S||^2,
Delta in Mat(2,2), S in Mat(2,4).
```

In entry coordinates this is Newton-degenerate. The homogeneous face is `F` itself, and there are real torus points with `Delta S = 0`; for example take `Delta` rank one with all entries nonzero and take every column of `S` to be a nonzero vector in `ker Delta`, also with all entries nonzero. Then `F = 0`, and all derivatives vanish because every derivative is linear in `Delta S`.

Even after the radial chart

```text
Delta = a [[1,u],[v,w]],
```

the unsheared residual has degenerate faces. Writing each column of `S` as `(x_j,y_j)`, one face is

```text
sum_j (x_j + u y_j)^2.
```

On the real torus, set `x_j = -u y_j`; then the face polynomial and its gradient vanish. Thus a pure monomial/radial chart has not resolved the Newton degeneracy.

The fix is the nonlinear shear

```text
P_j = x_j + u y_j,
e = w - v u,
```

after which the model becomes equivalent to

```text
||P||^2 + e^2 ||Q||^2.
```

That shear is chart-dependent: it depends on the chosen pivot minor, and with accumulated exceptional factors it also depends on which divisor multiplies which row/column generator. This is the “diag(b)” obstruction.

**Q3: NET verdict.**

For general DLN widths, the lower bound cannot be discharged by one Kushnirenko/Varchenko-style theorem in a single uniform Newton chart, nor by a clean per-layer monomial induction. It genuinely needs Aoyagi’s bespoke recursive real blow-up, with case splits over rank-drop patterns and accumulated divisor exponents.

The load-bearing reason is: partial corank >= 2 drops leave determinantal residuals whose Newton faces contain real torus critical loci; resolving them requires pivot-dependent nonlinear shears, and the resulting monomial exponents are coupled to previously accumulated exceptional divisors.

The lower-bound proof has the usual divisor inequality form: in each resolved chart, for each exceptional divisor `E_j`, with multiplicity data `(k_j,h_j)`,

```text
h_j + 1 >= c k_j
```

up to the chosen convention for whether `k_j` is the order of `K` itself or of the square-root ideal. But the verification is not uniform per layer; it reduces to a combinatorial minimum over admissible rank profiles / rank-drop patterns, with `(k_j,h_j)` accumulated recursively.

Confidence: high. The most likely way this verdict is wrong is if one cites a more abstract determinantal principalization theorem that packages Aoyagi’s recursion into a single black-box resolution theorem. That would change the citation strategy, not the algebraic obstruction to the proposed uniform Newton/monomial tower.
tokens used
21,317
**Q1: VIABLE-as-uniform-monomial-tower.**

For the all-width-2 chain, after the SVD/rank and Morse reductions, the deepest residual is

```text
w1^2 + w2^2 + delta^2 s^2 + delta^2 v^2.
```

This is a sum of squares of monomials. Every compact Newton face is again a positive sum of monomial squares, so on the real torus `(R*)^n` the face polynomial never vanishes. Hence there is no torus critical point. That is exactly the Newton-nondegeneracy check. So the width-2 case does not force the full Aoyagi recursive divisor bookkeeping, provided we are already in the rank/incidence coordinates. It is not solvable by Newton theory in the original entries, but it is solvable by the clean monomial incidence tower.

**Q2: the uniform scheme does not survive in general widths.**

The obstruction is the genuine corank >= 2 residual

```text
F(Delta,S) = ||Delta S||^2,
Delta in Mat(2,2), S in Mat(2,4).
```

In entry coordinates this is Newton-degenerate. The homogeneous face is `F` itself, and there are real torus points with `Delta S = 0`; for example take `Delta` rank one with all entries nonzero and take every column of `S` to be a nonzero vector in `ker Delta`, also with all entries nonzero. Then `F = 0`, and all derivatives vanish because every derivative is linear in `Delta S`.

Even after the radial chart

```text
Delta = a [[1,u],[v,w]],
```

the unsheared residual has degenerate faces. Writing each column of `S` as `(x_j,y_j)`, one face is

```text
sum_j (x_j + u y_j)^2.
```

On the real torus, set `x_j = -u y_j`; then the face polynomial and its gradient vanish. Thus a pure monomial/radial chart has not resolved the Newton degeneracy.

The fix is the nonlinear shear

```text
P_j = x_j + u y_j,
e = w - v u,
```

after which the model becomes equivalent to

```text
||P||^2 + e^2 ||Q||^2.
```

That shear is chart-dependent: it depends on the chosen pivot minor, and with accumulated exceptional factors it also depends on which divisor multiplies which row/column generator. This is the “diag(b)” obstruction.

**Q3: NET verdict.**

For general DLN widths, the lower bound cannot be discharged by one Kushnirenko/Varchenko-style theorem in a single uniform Newton chart, nor by a clean per-layer monomial induction. It genuinely needs Aoyagi’s bespoke recursive real blow-up, with case splits over rank-drop patterns and accumulated divisor exponents.

The load-bearing reason is: partial corank >= 2 drops leave determinantal residuals whose Newton faces contain real torus critical loci; resolving them requires pivot-dependent nonlinear shears, and the resulting monomial exponents are coupled to previously accumulated exceptional divisors.

The lower-bound proof has the usual divisor inequality form: in each resolved chart, for each exceptional divisor `E_j`, with multiplicity data `(k_j,h_j)`,

```text
h_j + 1 >= c k_j
```

up to the chosen convention for whether `k_j` is the order of `K` itself or of the square-root ideal. But the verification is not uniform per layer; it reduces to a combinatorial minimum over admissible rank profiles / rank-drop patterns, with `(k_j,h_j)` accumulated recursively.

Confidence: high. The most likely way this verdict is wrong is if one cites a more abstract determinantal principalization theorem that packages Aoyagi’s recursion into a single black-box resolution theorem. That would change the citation strategy, not the algebraic obstruction to the proposed uniform Newton/monomial tower.

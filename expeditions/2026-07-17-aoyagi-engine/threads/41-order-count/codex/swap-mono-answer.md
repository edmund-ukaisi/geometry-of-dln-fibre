## 1. Verdict

**Recommended:** split on the width order, then exploit an asymmetric endpoint-collapse fact. This is cleaner than proving a full clamp formula.

This strategy was **verified algebraically and in a Lean 4.29 scratch proof**. The judgment that it is “cleanest” is strategic.

Use `le_or_gt A B`; at this pin, literal `le_or_lt A B` did not elaborate.

Write:

- If \(A\le B\), let \(d=B-A\). Split the **primed** condition \(d\le P'-X'\) first.
- If \(B<A\), let \(e=A-B\). Split the **unprimed** condition \(e\le X-Q\) first.

The key facts are:

- \(A\le B\): a reflected primed minimiser satisfies \(X'=Q'\).
- \(B<A\): a reflected unprimed minimiser satisfies \(X=P\).

Consequently:

- In the \(A\le B\) regime, only `hmin'` is needed.
- In the \(B<A\) regime, only `hmin` is needed.
- No case needs both minimalities.

A clamp characterization is true:
\[
A\le B:\quad \operatorname{swapR}=\min(P,X+d),\qquad
B<A:\quad \operatorname{swapR}=\max(Q,X-e),
\]
on minimisers. But proving it for both tuples invokes more minimality facts than the direct asymmetric proof.

## 2. Case grid and competitors

### Regime \(A\le B\), \(d=B-A\)

Branches are:

- `T`: \(d\le P-X\), output \(X+d\);
- `R`: its negation, output \(P+Q-X\).

First prove the primed endpoint collapse in the primed `R` branch:

- Split \(X'=Q'\) versus \(Q'<X'\).
- In the strict case instantiate
  `hmin'` at **\(Y=X'-1\)**.
- Admissibility follows from \(Q'<X'\), \(X'\le P'\), and \(X'\le A\).
- After finite-difference normalization:
  \[
  2X'+d\le P'+Q'+1.
  \]
- The primed reflection condition gives
  \[
  P'+1\le X'+d.
  \]
- `omega` then obtains \(X'\le Q'\), contradiction.

Thus primed `R` forces \(X'=Q'\), and its output is \(P'\).

| Unprimed | Primed | Minimality | Closing arithmetic |
|---|---|---|---|
| `T` | `T` | none | \(X+d\le X'+d\) |
| `R` | `T` | none | \(P+Q-X\le P<X+d\le X'+d\) |
| `T` | `R` | `hmin'` at \(X'-1\) only in \(Q'<X'\) | Endpoint gives \(X+d\le P\le P'\) |
| `R` | `R` | same | Endpoint gives \(P+Q-X\le P\le P'\) |

So the efficient tactic tree is: split primed `T/R`; if primed `R`, prove the endpoint once without splitting the unprimed branch until the final `omega`.

### Regime \(B<A\), \(e=A-B\)

Branches are:

- `T`: \(e\le X-Q\), output \(X-e\);
- `R`: its negation, output \(P+Q-X\).

First prove the unprimed endpoint collapse in the unprimed `R` branch:

- Split \(X=P\) versus \(X<P\).
- Reflection failure and \(Q\le B\) imply \(X<A\).
- In the strict case instantiate `hmin` at **\(Y=X+1\)**.
- It is admissible because \(X<P\) and \(X<A\).
- After normalization:
  \[
  P+Q+e\le 2X+1.
  \]
- But \(X<P\) and reflection failure give
  \[
  X+1\le P,\qquad X+1\le Q+e,
  \]
  hence \(2X+2\le P+Q+e\), contradiction.

Thus unprimed `R` forces \(X=P\), and its output is \(Q\).

| Unprimed | Primed | Minimality | Closing arithmetic |
|---|---|---|---|
| `T` | `T` | none | \(X-e\le X'-e\) |
| `T` | `R` | none | \(X-e\le Q'\le P'+Q'-X'\) |
| `R` | `T` | `hmin` at \(X+1\) only in \(X<P\) | Endpoint gives \(Q\le Q'\le X'-e\) |
| `R` | `R` | same | Endpoint gives \(Q\le Q'\le P'+Q'-X'\) |

## 3. Pitfalls

- `swapFℤ` subtraction is integer subtraction, not truncated subtraction. Only the competitor `X'-1 : ℕ` is truncated before casting.
- For \(X'-1\), explicitly establish
  \[
  ((X'-1:\mathbb N):\mathbb Z)=(X':\mathbb Z)-1
  \]
  before normalization. `push_cast` alone may not discharge this.
- Raw `hmin` contains quadratic products that `omega` treats as opaque. A verified pipeline is:
  `simp only [swapFℤ] at hm`, fix the predecessor cast, then `ring_nf at hm`, then `omega`.
  For \(X+1\), `push_cast` followed by `ring_nf` works.
- Simplify the width regime before splitting branches. In the \(A\le B\) case, explicitly keep `¬ B < A`; `simp [hAB]` can otherwise leave the dead inner `if`.
- Translate failed truncated-subtraction tests only with their range hypotheses present:
  \[
  \neg(d\le P-X)\Rightarrow P<X+d,\qquad
  \neg(e\le X-Q)\Rightarrow X<Q+e.
  \]
  `omega` handles these once \(X\le P\) and \(Q\le X\) are in context.
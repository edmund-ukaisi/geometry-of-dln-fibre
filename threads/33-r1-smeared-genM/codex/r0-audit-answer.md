1. **Argument sound.**

Step (i) is correct, and the exact statement is:

\[
1 \le \minAdm(M) \iff M_0\ge 1 \wedge M_1\ge 1 \wedge M_2\ge 1.
\]

Proof-level reason:

- If \(M_0=0\), only/allow \(T_0=0\), and \(Mval(0)=0\).
- If \(M_1=0\), same: \(Mval(0)=0\).
- If \(M_2=0\), choose \(T_0=\min(M_0,M_1)\); then \((M_0-T_0)(M_1-T_0)=0\), so \(Mval(T_0)=0\).
- Conversely, if all \(M_i\ge1\), then \(T_0=0\) gives \(M_0M_1\ge1\), and \(T_0\ge1\) gives \(T_0M_2\ge1\), so every admissible value is \(\ge1\).

Step (ii) is also sound, given your stated Lean-derived condition:

\[
InteriorDrop(M) \iff M_2>0 \wedge r<M_0 \wedge r<M_1.
\]

Thus if \(r=0\) and \(M_0,M_1,M_2\ge1\), then \(InteriorDrop\) holds. Therefore `BoundarySmeared`, which includes `¬InteriorDrop`, excludes \(r=0\).

2. **No hidden large-width r=0 smeared case.**

There is no width regime, large or asymmetric, with chosen \(r=0\), `minAdm ≥ 1`, and `BoundarySmeared`. The proof above is uniform.

However, there **is** a minimizer-nonuniqueness subtlety for minimizer-independence of the branch predicate itself. Example:

\[
M=(1,2,2).
\]

Then

\[
Mval(0)=2,\qquad Mval(1)=2,
\]

so both \(0\) and \(1\) are argmins.

- If Lean’s arbitrary `tStar` chooses \(r=0\), then `InteriorDrop` holds.
- If it chooses \(r=1\), then `InteriorDrop` fails and \(r<M_1\), so this is `BoundarySmeared`.

So this is **not** a counterexample to “`BoundarySmeared ∧ minAdm≥1 → r≥1`”. It is a counterexample to any stronger claim that the **classification is independent of the chosen minimizer**, unless an extra canonical-choice or branch-invariance lemma is proved.

3. **Verdict.**

- Obligation **(b)**: `r ≥ 1` in the smeared branch under `minAdm ≥ 1` is **BOUNDED**. Short lemma; no wall for this obligation.

  Even stronger proof route:

  \[
  1\le \minAdm,\ BoundarySmeared
  \Rightarrow M_0,M_1,M_2\ge1,\ \neg InteriorDrop,\ r<M_1.
  \]

  If \(r=0\), then `InteriorDrop`, contradiction. Hence \(r\ge1\).

- Obligation **(a)**: `deepRank ≤ M0` is **BOUNDED**. Since \(r\) is an admissible \(T_0\),

  \[
  r \le \min(M_0,M_1) \le M_0.
  \]

Separate warning: minimizer-independence of the **branch classification** looks like a potential **WALL** unless already handled elsewhere.
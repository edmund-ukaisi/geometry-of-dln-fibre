Yes: Q1 is true, `hpiv` at `t★` suffices for Q2, and full `hgood` is unnecessary.

## Q1. Unconditional increment bound

For a nonempty fixed tail \(C=(c,C')\), write
\[
V_C(u)=\minAdm(u,c,C').
\]
Then, for every \(u\),
\[
V_C(u+1)\le V_C(u)+\min C.
\]
This addition-form inequality is preferable in Lean and implies
\[
V_C(u+1)-V_C(u)\le \min C.
\]

Induct on the length of \(C\).

The base case is
\[
V_{(c)}(u)=uc,
\]
so the increment is exactly \(c\).

For the inductive step, let \(s\) attain
\[
V_C(u)=(u-s)(c-s)+V_{C'}(s).
\]
Put \(d=\min C=\min(c,\min C')\) and \(q=c-s\).

- If \(q\le d\), reuse \(s\) at \(u+1\):
  \[
  V_C(u+1)\le V_C(u)+q\le V_C(u)+d.
  \]

- If \(d<q\), then \(c>d\), hence \(d=\min C'\). Use \(s+1\), which is admissible because \(s<c\):
  \[
  \begin{aligned}
  V_C(u+1)
  &\le (u-s)(q-1)+V_{C'}(s+1)\\
  &\le (u-s)q+V_{C'}(s)+d\\
  &=V_C(u)+d.
  \end{aligned}
  \]

Thus
\[
G(u+1)\le G(u)+\deepRank(M).
\]

The proposed minimizer bound \(s\ge M_2-\deepRank\) is false. For the tail \((7,1)\) and \(u=1\), the unique minimizer is \(s=1\), whereas \(7-1=6\).

## Q2. The sharp tail-width bound from `hpiv`

The useful general helper is:

> If \(u\ge1\) and \(V_C(u)\le uw\), then
> \[
> V_C(u+1)\le V_C(u)+w.
> \]

Its proof uses the same induction. With \(s,q\) as above:

- If \(q\le w\), reuse \(s\).
- If \(q>w\), then \(s>0\); otherwise
  \[
  V_C(u)\ge uq>uw.
  \]
  Moreover,
  \[
  (u-s)q+V_{C'}(s)\le uw
  \]
  and \(q\ge w\) imply
  \[
  V_{C'}(s)\le sw.
  \]
  Apply the induction hypothesis to \(V_{C'}\) at \(s\), then use \(s+1\) as the competitor.

Apply this with \(u=t^\star\) and \(w=\tailMinWidth(M)\). The proof then separates cleanly:

1. **`hpiv` + conditional increment lemma**
   \[
   G(t^\star+1)\le G(t^\star)+w.
   \]

2. **Binding optimality**, using \(t^\star+1\) as a competitor:
   \[
   a^\star b^\star+G(t^\star)
   \le (a^\star-1)(b^\star-1)+G(t^\star+1).
   \]
   Since \(a^\star,b^\star\ge1\),
   \[
   G(t^\star)+(a^\star+b^\star-1)\le G(t^\star+1).
   \]

3. **Nat cancellation**
   \[
   a^\star+b^\star-1\le w,
   \]
   hence
   \[
   a^\star+b^\star\le w+1.
   \]

Only `hpiv` at \(t^\star\) is needed; full `hgood` is strictly stronger. Leastness of the binding cut is unused—only minimizer optimality matters.

The assumptions are genuinely needed:

- Without `hpiv`: \(M=(4,3,5)\) has \(t^\star=1\), \(a^\star+b^\star=5>4=\tailMinWidth+1\).
- Without \(t^\star\ge1\): \(M=(2,2,100)\) has \(t^\star=0\), satisfies the vacuous `hpiv`, and violates the conclusion.
- Without \(t^\star+1\le\min(M_0,M_1)\): boundary examples such as \(M=(10,1,1)\) fail.

The increment bound is stronger than the corank conclusion; they are not logically equivalent.

## Q3. Full goodness excludes the waist

For every positive tail,
\[
G(1)=\deepRank(M).
\]
Indeed, at every recursive layer a rank-one pivot is either \(0\) or \(1\), so induction gives the minimum of all tail widths.

Consequently, `hgood` at \(u=1\) gives
\[
\deepRank=G(1)\le\tailMinWidth.
\]
The reverse inequality holds by definition, so
\[
\deepRank=\tailMinWidth.
\]

Only the single hypothesis \(G(1)\le\tailMinWidth\) is needed here.

Under full `hgood`, the decomposition
\[
a^\star+b^\star\le\deepRank+1
\quad+\quad
\deepRank=\tailMinWidth
\]
is probably the shortest Lean proof once Q1 is available. It cannot prove the sharper `hpiv` theorem: for
\[
M=(5,4,5,5,5),
\]
one has \(t^\star=3\), \(G(3)=12=3\cdot4\), but \(\deepRank=5>\tailMinWidth=4\). Thus pointwise `hpiv` does not exclude the waist.

## Q4. Recommended theorem

```lean
theorem bindingCut_residual_sum_le_tailMinWidth_add_one
    (M : Chain)
    (hlen : 3 ≤ M.length)
    (ht : 1 ≤ bindingCut M)
    (hnext :
      bindingCut M + 1 ≤ min (M 0) (M 1))
    (hpiv :
      minAdm (redChain (bindingCut M) M)
        ≤ bindingCut M * tailMinWidth M) :
    (M 0 - bindingCut M) + (M 1 - bindingCut M)
      ≤ tailMinWidth M + 1
```

Internally, prove the arbitrary-\(w\) conditional increment helper first. It avoids subtraction of successive `minAdm` values and keeps the final proof to two inequalities plus cancellation.
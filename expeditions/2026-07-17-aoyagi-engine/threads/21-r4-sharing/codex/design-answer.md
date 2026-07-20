Verdict: for the normalized Aoyagi generators, `genDivExp` is derived, not independent. Derive it from `divTilde` and the generator’s row. However, Lean must also encode the exact \(b\)-chain specification and the absence of hidden exceptional factors in the residual block; `bChain : Monotone bExp` alone is insufficient.

1. Solving the recursion

Write \(q_k=\widetilde t_{s,k}\). Iterating
\[
b_i=\left(\prod_{q_k=i-1}u_k\right)b_{i-1}
\]
gives
\[
\boxed{b_i=\prod_{q_k<i}u_k}.
\]

Hence
\[
\nu_{u_k}(b_i)=
\begin{cases}
1,&q_k<i,\\
0,&q_k\ge i.
\end{cases}
\]

Every divisor is squarefree in every \(b_i\); Case 1(1) increases its Jacobian exponent `divExp`, not its exponent in \(b_i\).

2. Generator content

Put
\[
H=\begin{pmatrix}E_J&O\\O&D_J\end{pmatrix}\prod_{s>S}C^{(s)}.
\]
Then the generator in row \(i\), column \(c\), is
\[
G_{ic}=b_iH_{ic}.
\]

Exactly,
\[
\nu_{u_k}(G_{ic})
=\mathbf 1_{\{q_k<i\}}+\nu_{u_k}(H_{ic}).
\]

In Aoyagi’s normalized ratio/strict-transform coordinates, \(H_{ic}\) carries no extracted exceptional factor, so
\[
\boxed{\nu_{u_k}(G_{ic})=\mathbf 1_{\{q_k<i\}}.}
\]
Thus the divisor content depends only on the row, not the column.

3. Is `genDivExp` independent?

No—provided it denotes the canonical extracted exceptional monomial. If `genRow g` is the zero-based global row of generator \(g\), define
```lean
genDivExp g k :=
  if divTilde k ≤ (genRow g).val then 1 else 0
```
because Lean row \(r\) represents mathematical \(b_{r+1}\).

Equivalently,
```lean
genDivExp g = bExp (genRow g)
```
with the required coherence theorem
```lean
bExp i k = if divTilde k ≤ i.val then 1 else 0
```

For a residual-block local row \(a\), whose global one-based row is
\[
i=J+1+a,
\]
the incidence condition is
\[
u_k\mid G_{a,c}\iff q_k\le J+a.
\]

Consequently:

- \(q_k\le J\): \(u_k\) divides every generator in the residual block.
- \(q_k=J+r\): it begins in local row \(r\) and divides every later row.
- Columns never affect the canonical support.

No `Finset` transport is mathematically needed.

4. Exact support and the sharing witness

For a residual generator \(g=(a,c)\),
\[
\boxed{\operatorname{support}(g)
=\{k:\min_p\operatorname{divProfile}(k)(p)\le J+a\}.}
\]

The identity of a shared variable is retained: the same index \(k\) occurs in several supports. Two divisor variables remain two distinct indices.

There is one qualification about the comparison
\[
\langle\delta x,\delta y\rangle
\quad\text{versus}\quad
\langle\delta_1x,\delta_2y\rangle.
\]
A single Aoyagi \(b\)-chain has nested row supports. For two rows, two levels \(0,1\) give
\[
b_1=\delta_1,\qquad b_2=\delta_1\delta_2,
\]
not the incomparable supports \(\{\delta_1\}\) and \(\{\delta_2\}\). Thus the literal “one divisor per row” ideal lies outside this normalized row-chain form. The witness proves that arbitrary support-flattening is dangerous; it does not prove that support is independent once the Aoyagi \(b\)-chain theorem is enforced.

5. The \((3,3,4)\), \(t=(1,0)\) branch

After layer 1, name its three divisors
\[
a=u_{1,1},\qquad \delta=u_{1,2},\qquad c=u_{1,3}.
\]
Their initial levels are \(0,1,2\), so
\[
(b_1,b_2,b_3)=(a,\;a\delta,\;a\delta c).
\]

The divisor \(\delta\) is born by blowing up the \(2\times2\) block \(D_1\); it divides both residual rows. This is the decisive sharing.

At layer 2, the Case 1(1) \(u\)-pivot changes
\[
T_\delta:(1,1)\longmapsto(1,0),
\qquad
M_\delta:4+1(4-0)=8.
\]

One all-\(u\)-pivot terminal continuation has divisors
\[
\begin{aligned}
a &: (0,0),& M&=9,\\
\delta &: (1,0),& M&=8,\\
c &: (2,0),& M&=9,\\
p=u_{2,1}&:(3,0),&M&=12,\\
q=u_{2,2}&:(3,1),&M&=6,\\
r=u_{2,3}&:(3,2),&M&=2.
\end{aligned}
\]
Therefore
\[
\boxed{
b_1=a\delta cp,\qquad
b_2=a\delta cpq,\qquad
b_3=a\delta cpqr.
}
\]
Hence
\[
F=a^2\delta^2c^2p^2\bigl(1+q^2+q^2r^2\bigr).
\]

For the binding divisor,
\[
\operatorname{Mval}(1,0)
=(3-1)^2+(1-0)(4-0)=4+4=8.
\]
Its Jacobian power is \(8-1=7\), while its loss order is \(2\), giving
\[
\frac{7+1}{2}=4.
\]
Thus
\[
\boxed{\operatorname{rlct}=4.}
\]
The other \(t_1\)-values give \(9,9,12\), all larger than \(8\).

6. Kill-condition

Inside the normalized Aoyagi invariant, no kill configuration exists. If two states have the same indexed `divProfile` ledger and the same row map, then their `divTilde` values agree, hence
\[
\mathbf1_{\{\operatorname{divTilde}(k)<i\}}
\]
agrees for every generator and divisor. Their sharing is identical, up to harmless renaming of divisor indices.

But the displayed ideal identity alone does not enforce normalization. For example, take \(q_u=1\), hence \(b=(1,u)\):
\[
I_1=\langle x,uy\rangle,\qquad
I_2=\langle ux,uy\rangle.
\]
Both can be written with the same \(b\)-chain and profile ledger, using residual columns
\[
H_1=(x,y),\qquad H_2=(ux,y),
\]
yet
\[
\operatorname{rlct}(I_1)=1,\qquad
\operatorname{rlct}(I_2)=\tfrac12.
\]
The second representation hides an extra \(u\)-factor in the residual and is not an Aoyagi-normalized state.

Therefore the Lean design should:

- derive `genDivExp`/`support`;
- carry or derive a structural `genRow`;
- strengthen `bChain` to the exact `bExp_spec` above;
- prove the residual is strict-transform/divisor-free for the intended meaning of “exact exponent.”

Do not transport an independent `genDivExp`: it would duplicate determined data and could disagree with `divProfile`.
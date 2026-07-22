## 1. Explicit `enc(T)`

First sort the widths, transporting the profile through adjacent swaps.

For an adjacent swap of width positions `k,k+1`:

- If `k = 0`, leave `T` unchanged.
- If `1 ≤ k < L`, put
  \[
  P=\begin{cases}M_0,&k=1,\\T_{k-2},&k>1,\end{cases}\quad
  X=T_{k-1},\quad Q=T_k,\quad A=M_k,\quad B=M_{k+1}.
  \]
  Replace only `X` by
  \[
  R_{A,B}(P,X,Q)=
  \begin{cases}
  X+(B-A),&A\le B\ \land\ B-A\le P-X,\\
  X-(A-B),&B<A\ \land\ A-B\le X-Q,\\
  P+Q-X,&\text{otherwise}.
  \end{cases}
  \]
  Simultaneously swap `M_k,M_{k+1}`.

Run a fixed bubble-sort schedule until the widths become
\[
D_0\le D_1\le\cdots\le D_L.
\]
Call the transported profile \(U\).

Now define
\[
e_i^\uparrow=
\begin{cases}
D_0-U_0,&i=0,\\
U_{i-1}-U_i,&i>0,
\end{cases}
\qquad
C=\left\lceil\frac{\sum_{j=0}^{\ell}D_j}{\ell}\right\rceil .
\]
The actual active steps are
\[
x_i=e_i^\uparrow+D_{i+1}\qquad(0\le i<\ell).
\]
For a binding profile,
\[
x_i\in\{C-1,C\},\qquad e_i^\uparrow=0\ (i\ge\ell),
\]
with exactly
\[
a=\sum_{j=0}^{\ell}D_j-(C-1)\ell
\]
indices satisfying \(x_i=C\). Thus
\[
A(T)=\{i<\ell:x_i=C\}.
\]

This is not literally a regrouping of consecutive original increments: it is an adjacent-swap transport followed by the shifted increments \(e_i^\uparrow+D_{i+1}\).

Enumerate
\[
A(T)=\{p_0<\cdots<p_{a-1}\}.
\]
The gaps \(g_r=p_r-r\) are nondecreasing. Since `BoxPart` expects an antitone function, reverse them:
\[
\boxed{\operatorname{enc}(T)(i)=p_{a-1-i}-(a-1-i).}
\]
In Lean, use `Fin.rev i`.

Checks:

- `[2,2,2,2,2]`: already sorted, \(C=3\), and \(x_i=e_i+2\). Hence \(A(T)\) is exactly the support of the displayed `e`.
- `[1,1,2,1]`: bubble-sort swaps positions `2,3`.
  - `(0,0,0)` transports to `(0,0,0)`, giving \(x=(2,1)\), hence \(A=\{0\}\).
  - `(1,1,0)` transports to `(1,0,0)`, giving \(x=(1,2)\), hence \(A=\{1\}\).

Epistemic status: the sorted-width part follows from the existing QIP characterization. The adjacent-swap formula is a new derived proposal, not present in Aoyagi or currently proved in Lean. The complete `enc/dec/order` contract passed all 1,360 positive vectors with `L ≤ 4`, widths `≤ 4`. Also, repository `ell = qipM` is a value-equivalent surrogate, not always Aoyagi’s literal Definition-3 `paperEll`; these are QIP water-filling slots, not literally Lemma-4 branch steps.

## 2. Explicit inverse `dec(f)`

Let \(D\) be the sorted widths and retain the bubble-sort swap trace.

Given antitone \(f:\operatorname{Fin}a\to\mathbb N\), define
\[
g_r=f(a-1-r),\qquad p_r=r+g_r,
\]
and \(A_f=\{p_0,\ldots,p_{a-1}\}\).

Define sorted increments
\[
e_i^\uparrow=
\begin{cases}
C-D_{i+1},&i<\ell,\ i\in A_f,\\
C-1-D_{i+1},&i<\ell,\ i\notin A_f,\\
0,&i\ge\ell.
\end{cases}
\]
Then define
\[
U_c=D_0-\sum_{i=0}^{c}e_i^\uparrow.
\]
Finally traverse the bubble-sort trace backwards, applying the same adjacent-swap operation \(R\); it is involutive. The resulting profile is
\[
\boxed{\operatorname{dec}(f)=T.}
\]

For Lean, `Int.toNat` can avoid awkward truncated-subtraction terms until the active-width inequalities prove nonnegativity.

## 3. Both-directions monotonicity

For sorted widths, if \(T_A\) denotes the profile associated to \(A\), then
\[
(T_A)_c
 =D_0-\text{(fixed base prefix)}
   -|A\cap\{0,\ldots,c\}|.
\]
Consequently,
\[
T_A\le T_B
\iff
\forall c,\ |A\cap[0,c]|\ge|B\cap[0,c]|
\iff
\forall r,\ p_r(A)\le p_r(B)
\iff
\operatorname{enc}(T_A)\le\operatorname{enc}(T_B).
\]

For an adjacent width swap, the two value-preserving candidates are precisely

- translation \(X-A+B\);
- reflection \(P+Q-X\).

This follows by writing the local square-completed objective as
\[
(P-X+A)^2+(X-Q+B)^2.
\]
Translation preserves the two shifted terms; reflection exchanges them. A binding \(X\) locally minimizes this quadratic on
\[
Q\le X\le\min(P,A).
\]
A finite case split on `A ≤ B`, the two branches, and the one-unit optimality inequalities proves that \(R\) is monotone on binding profiles. Applying the same lemma with `A,B` reversed, together with involutivity, gives order reflection.

The hazardous direction is
\[
\operatorname{enc}(T)\le\operatorname{enc}(T')\Longrightarrow T\le T'.
\]
Bijective plus monotone is insufficient for partial orders. Prove `map_rel_iff` directly, or prove monotonicity of both `enc` and `dec`.

## 4. Lean recommendation

Build three explicit order isomorphisms and compose them:

1. `swapBindingOrderIso` for one adjacent swap, using `R`.
2. `sortBindingOrderIso` by composing the bubble-sort swaps.
3. `sortedBindingOrderIsoBoxPart` using \(A\), ordered positions, and reversed gaps.

`OrderIso.ofHomInv` is a good fit: define forward and inverse `OrderHom`s, prove the two round trips, then compose with `.trans`. A direct structure with `toEquiv` and `map_rel_iff'` is equally reasonable. Avoid a `Finset.card_bij`; cardinal bijectivity does not supply order reflection and adds subtype/coercion work.

Reuse [`MinAdmCCodim.lean`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/E/lean/DLNFibre/DLN/RLCT/Validate/MinAdmCCodim.lean) for `eOfT/tOfE`, and [`CThetaValue.lean`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/E/lean/DLNFibre/Core/CThetaValue.lean) for the sorted minimizer characterization.

The painful new lemmas are:

- the adjacent-swap map preserves `bindingSet`;
- its local monotonicity on binding profiles;
- bubble-sort transport agrees with `shiftedSorted`;
- translating `qipRound/qipDelta` into `ceilingM/residueA`.

The existing permutation-invariance theorem proves only equality of minimum values; it cannot replace the adjacent-swap profile transport. No additional finite example determines that transport—the minimal missing datum is precisely the adjacent-swap `OrderIso` theorem above.
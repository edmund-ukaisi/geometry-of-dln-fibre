## Q1 — A vs B

**Direct answer:** Architecture **(A)** is primitive, but with a restricted decoration class. Route (B) is standalone only for a fixed short chain; in general it either fails as an unstratified atom estimate or hides the same recursive resolution as (A).

At level \(k\),
\[
\det(Q_bQ_b^{\mathsf T})^{-a/2}
\]
is the induced-volume Jacobian of \(\Gamma\mapsto\Gamma Q_b\). Since \(Q_b\) is itself built from the deeper product, its singular divisor is precisely what the next peel resolves. On a deeper pivot chart, the old determinant weight becomes an exceptional monomial times a unit, while the next peel may emit another Gram/Jacobian factor. Thus the closed recursive object is not a plain loss but a loss together with accumulated divisor valuations and generator support: a decoration.

The level-\(k\) determinant and the level-\((k+1)\) coupling are therefore the same **species** of object—singular volume data coupled to a residual product loss—but not literally the same scalar formula. Their dimensions and exponents differ; the earlier determinant becomes `jac`/support data when the deeper coupling is resolved.

There is an additional warning about literal (B). The displayed determinant formula comes from integrating \(\Gamma\) over the full space. When \(\operatorname{rank}Q_b<b\), that full-space atom is infinite along kernel directions, whereas the original bounded-\(\Gamma\) integral may remain finite. Hence a global lemma for the raw determinant majorant is not automatically a theorem about the true box integral. It needs rank stratification or a uniformly truncated atom. Once repaired that way, its proof is the decorated recursion in specialized form.

**FACT:** A subsequent peel principalizes the rank-drop divisor of the preceding \(Q_b\); the resulting weights must remain coupled to the residual loss. The full-space atom and the true bounded-box integral differ essentially near rank drop.

**INFERENCE:** Use (A) as the general architecture. A fixed-chain version of (B) is useful as a base case or validation lemma, not as the primitive all-length recursion.

## Q2 — The universal decoration quantifier

**Direct answer:** \(\forall\delta\) over the present `SJDecoration` structure is false. The theorem must quantify over an admissible/reachable class.

A concrete counterexample already exists using only the banked constructors. Take the two-node chain \(M=(1,2)\), for which
\[
\frac12\minAdm(M)=1.
\]
Let
\[
D=(\operatorname{trivial}M).\operatorname{radialAttach}(0).
\]
Then
\[
D.\operatorname{integral}(c)
=
\left(\int_0^1 u^{-2c}\,du\right)
(\operatorname{trivial}M).\operatorname{integral}(c).
\]
At \(c=3/4<1\), the first factor diverges. Thus not every decoration on the free-matrix base is finite below the chain threshold.

The correct statement has the form
\[
\forall D,\quad \operatorname{Admissible}(M,D)
   \Longrightarrow \operatorname{DecoratedFinite}(M,D).
\]
`Admissible` may be defined inductively as reachability from a trivial product carrier through the permitted chart operations. It must enforce:

- `jac` is the actual Jacobian valuation of the composite chart, not an arbitrary vector;
- fresh \(p\)-dimensional radial variables initially contribute \(p-1\);
- later corner substitutions increment the existing shared-divisor exponent by the correct additional dimensions;
- the carrier support is obtained by permitted block splits, unit row-mixes and corank steps, preserving the nested/shared support relations;
- chart domains and measures come from the parameter box through valid changes of variables;
- unit coefficients are bounded above and below on the relevant rank sector;
- rank-drop complements are routed to explicit deeper strata;
- the accumulated charge and remaining chain satisfy the binding-budget relation.

The induction should therefore be
\[
\bigl[\forall M'<M,\ \forall D',\
  \operatorname{Admissible}(M',D')\Rightarrow\operatorname{Finite}(D')\bigr]
\Rightarrow
\forall D,\
  \operatorname{Admissible}(M,D)\Rightarrow\operatorname{Finite}(D).
\]

**FACT:** The current `SJDecoration` fields allow arbitrary `jac`, carrier, measure space and domain. Even `radialAttach 0` gives a divergent base decoration below the free-matrix threshold.

**INFERENCE:** Replace unrestricted \(\forall\delta\) by an inductively closed `Reachable`/`Admissible` predicate. The base theorem concerns every admissible decoration reaching a two-node chain, not every inhabitant of `SJDecoration`.

## Q3 — Do the charges really add?

**Direct answer:** They do **not** add in the terminal product monomial written in the question.

Indeed,
\[
\prod_{k=1}^m |u_k|^{h_k}
\left(\prod_{k=1}^m u_k^2\right)^{-c'}
=
\prod_{k=1}^m |u_k|^{h_k-2c'}.
\]
Its box integral is finite exactly when
\[
h_k-2c'>-1\quad\text{for every }k,
\]
hence its threshold is
\[
\boxed{\frac12\min_k(h_k+1)}.
\]
With \(h_k=p_k-1\), this is \(\frac12\min_kp_k\), not
\(\frac12\sum_kp_k\). Repeated `radialAttach` produces precisely this product behavior; its banked integral factorization confirms the minimum threshold.

Charge addition comes from a different local model:
\[
\prod_k |u_k|^{h_k}
\left(\sum_k u_k^2U_k\right)^{-c'},
\qquad U_k\asymp1.
\]
Here the loss vanishes only at the common corner. Blowing up that corner, for example
\[
u_k=u\,\tau_k\quad(k>1),
\]
gives a single exceptional coordinate \(u\) with Jacobian exponent
\[
H=\sum_k h_k+(m-1).
\]
The transformed loss has order \(u^2\), so the threshold is
\[
\frac{H+1}{2}
=
\frac{\sum_k(h_k+1)}2.
\]
For \(h_k=p_k-1\), this is
\[
\boxed{\frac12\sum_kp_k=\frac12\minAdm(M)}.
\]
For the \(p=(4,3)\) example, \(H=3+2+1=6\), giving \(7/2\).

Equivalently, the regime-A Morse reductions add exponent shifts:
\[
c'\longmapsto c'-\frac{p_1}{2}
\longmapsto c'-\frac{p_1+p_2}{2}
\longmapsto\cdots.
\]
But this works only while each step retains the additive coupled loss. It cannot be replaced by repeatedly factoring a multiplicative `radialAttach`.

The \(A_2\)-rank-drop must be an explicit stratum. The exact rank-deficient set may be null, but near it the units \(U_k\) cease to have uniform positive lower bounds. One must cover a generic minor sector where \(U_k\ge a>0\), and send its complement to a deeper/higher-\(M\)-value resolution. An a.e. deletion does not control the surrounding singular tube.

**FACT:** Product losses give the minimum threshold. Additive corner losses, after a common-corner blow-up, give the sum threshold. The generic corner lemma requires uniform lower bounds on its units.

**INFERENCE:** The charge-addition principle is sound only after an explicit joint corner resolution or equivalent coupled Morse recursion. “One `radialAttach` per level” by itself is insufficient.

## VERDICT

Architecture **(A)** is the right primitive, corrected to a **reachable/admissible-decoration induction**. Unrestricted \(\forall\)-decoration finiteness is false.

The target \(\tfrac12\minAdm\) is attainable through additive exponent shifts or a common-corner blow-up, but not through the multiplicative terminal monomial generated by repeated `radialAttach`.

The remaining genuine obstruction is precise: construct the peel map on admissible carriers and prove its joint corner/truncated estimate on every deep-rank stratum, especially the \(A_2\)-rank-drop complement where the residual units are not bounded below.
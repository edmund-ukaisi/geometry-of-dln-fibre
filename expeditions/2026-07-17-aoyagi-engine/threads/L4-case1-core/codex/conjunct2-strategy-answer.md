### 1. VERDICT

**False as stated.** A free `ed.nextState` breaks conjunct (A). `hgrade` does not encode any transition law: with `shearφ = 0`, `blockShear = id` satisfies `ShearGrades` for every choice of \(S'\).

Write
\[
\operatorname{Supp}(s)=\operatorname{supportAt}(d,s.layer,s.cleared),\qquad
\operatorname{Thr}(s)=\operatorname{supportLayerOf}(s).
\]

The weakest observable state relation needed is

\[
\operatorname{DescendView}(s,s') :=
\begin{cases}
\operatorname{Supp}(s')=\operatorname{blockCoords}(d,s.layer+1)
\ \land\ \operatorname{Thr}(s')=s.layer+1,
& s.cleared=0,\\[2mm]
\operatorname{Supp}(s')=\operatorname{Supp}(s)
\ \land\ \operatorname{Thr}(s')=\operatorname{Thr}(s),
& s.cleared\ne0.
\end{cases}
\]

The construction’s stronger relation
\[
s'.layer=s.layer,\qquad s'.cleared=s.cleared+1
\]
implies this.

However, **no state-only link suffices for the full theorem**. Two further functional facts are missing:

- In the \(\delta=1\) branch, \(F=\operatorname{foldResid}_p(j)\) needs a support decomposition on the next block \(S'\), not merely on the parent block.
- For conjunct (B), `qm`/`stepMap` must preserve layerwise affinity from the new threshold.

The stated `hgrade` does not imply the second fact. For \(s,r\in S'\), the triangular shear
\[
\sigma_s(u)=u_s+u_r^2,\qquad \sigma_r(u)=u_r
\]
satisfies `hgrade (a)` using \(\gamma_{ss}=1,\gamma_{sr}=u_r\); these coefficients are per-layer degree \(1\), and `hgrade (b)` holds outside \(S'\). Nevertheless \(u_s+u_r^2\) is not affine on that layer.

### 2. Algebraic decomposition after the missing repairs

Let \(F=\operatorname{foldResid}_p(j)\), \(P=\operatorname{Supp}(p.conState)\), \(C=S'\), and \(\sigma=\operatorname{edgeShear}(ed)\).

#### \(\delta=0\)

`DescendView` gives \(C=P\). Since `hcenter` places the center in layer \(L\), while \(C\) lies in layer \(L+1\),
\[
i\in C\Longrightarrow \operatorname{stepMap}(u)_i=\sigma(u)_i.
\]
Thus `⊆` is sufficient; equality of the center is unnecessary.

From `hinv-2 (A)`,
\[
F(v)=\sum_{i\in C}a_i(v)v_i.
\]

For `case12`, `hgrade (a)` gives
\[
\sigma(u)_i=\sum_{k\in C}\gamma_{ik}(u)u_k,
\]
hence
\[
F(\operatorname{stepMap}u)
=
\sum_{k\in C}
\underbrace{\left(\sum_{i\in C}
a_i(\operatorname{stepMap}u)\gamma_{ik}(u)\right)}_{c'_k(u)}
u_k.
\]

For `case11`,
\[
c'_k(u)=a_k(\operatorname{stepMap}u).
\]

Suggested lemma chain:

1. `childSupport_disjoint_center` — `DescendView`, `hcenter`.
2. `stepMap_eq_edgeShear_on_childSupport`.
3. `graded_sum_substitution` — `hinv-2 (A)`, `hgrade (a)`.
4. `continuous_child_coeff` — continuity witnesses.

For (B), one needs a lemma of the form
\[
\operatorname{PerLayerDeg1From}(F,t')
\land \operatorname{LayerwiseAffineMapFrom}(g,t')
\Rightarrow
\operatorname{PerLayerDeg1From}(F\circ g,t'),
\]
with \(g=\operatorname{stepMap}\). Here `hinv-2 (B)` supplies the first premise. Current `hgrade (a,b)` does not supply the second.

#### \(\delta=1\)

Here \(P=\operatorname{blockCoords}(d,L)\) and, under `DescendView`,
\(C=\operatorname{blockCoords}(d,L+1)\).

The parent witness on \(P\) yields only
\[
F(qm\,u)
=
a_p(qm\,u)+
\sum_{i\in P\setminus\{p\}}a_i(qm\,u)\sigma(u)_i,
\]
because \(qm(u)_p=1\). Neither `hgrade (a)` nor `(b)` puts a \(C\)-factor into this expression.

A separate fold-specific lemma is required:
\[
F(v)=\sum_{i\in C}d_i(v)v_i.
\tag{next-layer support}
\]

Then, since \(p\notin C\), \(qm(u)_i=\sigma(u)_i\) for \(i\in C\), and
\[
F(qm\,u)
=
\sum_{k\in C}
\underbrace{\left(\sum_{i\in C}
d_i(qm\,u)\gamma_{ik}(u)\right)}_{c'_k(u)}
u_k
\]
in `case12`; in `case11`, \(c'_k=d_k\circ qm\).

For (B), use the same layerwise-composition lemma with \(g=qm\) and threshold \(L+1\). The intended lower-layer shear supplies this property, but the stated `hgrade` does not.

### 3. MOST LIKELY FAILURE POINT

The first failure is the free child support, not `hcenter ⊆`.

Take \(\delta=1\), `case11`, zero shear, center \(\{p\}\), and
\[
F(v)=v_pv_sv_e,
\]
with \(p\) in layer \(L\) and \(s\) in layer \(L+1\). Choose the free next state to remain \((L,0)\), so \(S'=P\). Then
\[
F(qm\,u)=u_su_e.
\]

Set every \(P\)-coordinate to \(0\), but \(u_s=u_e=1\). The child equals \(1\), while every proposed sum
\[
\sum_{i\in S'}c'_i(u)u_i
\]
equals \(0\).

That single SymPy substitution settles the state-link obstruction before any Lean work.
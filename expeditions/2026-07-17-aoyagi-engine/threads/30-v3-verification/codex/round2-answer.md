Audited commit `749b336d4`. v4 does not clear the “no false frontier statements” bar.

## 1. Atlas CoV — COUNTEREXAMPLE, VERIFIED

The records in [ProductResolution.lean](/tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean:53) do not connect `dom c` to the germ neighborhood at source origin where `hjac` and `hideal_*` hold.

Take \(D=M=2\), \(x_0=0\),

\[
F_0(x,y)=x,\qquad F_1(x,y)=y^2,
\]
so \(\sum F_i^2=x^2+y^4\), with
\[
\operatorname{rlct}_0(x^2+y^4)=\frac34.
\]

Use one chart
\[
g(s,t)=(s(1-s),st).
\]

All `Chart` fields hold:

- `hg0`, continuity, analyticity: immediate; \(g\) is polynomial.
- `M' = 1`, `bexp 0 = (1,0)`, `k₀=0`; hence \(b=s\).
- `hchain` trivial; `bindingAxes = {0}`; unit multiplicity is \(1\).
- `jac=(1,0)`, `unit(s,t)=1-2s`.
- \(\det Dg=s(1-2s)\), so globally
  \[
  |\det Dg|=|s|\,|1-2s|=\operatorname{jacWeight}(1,0)\,|\mathrm{unit}|.
  \]
- Pullbacks are
  \[
  F_0\circ g=s(1-s),\qquad F_1\circ g=s^2t^2.
  \]
  Forward representation by \(b=s\) uses coefficients \(1-s\) and \(st^2\). Backward representation uses \((1-s)^{-1}(F_0\circ g)=s\) near zero.

For the `Resolution`, let

\[
\mathrm{dom}=\{(0,0)\}\cup
\left([3/4,5/4]\times[-1/4,1/4]\right),\qquad
U=(-1/8,1/8)^2.
\]

`dom` is compact and contains zero. The inverse branch near \(s=1\) maps the rectangle onto \(U\): solve \(s(1-s)=x\) with \(s\in[3/4,5/4]\), then \(t=y/s\). Thus `hcover` holds exactly.

At the chart origin,

\[
(\sum F_i^2)\circ g
=s^2\bigl((1-s)^2+s^2t^4\bigr).
\]

The bracket and \(|1-2s|\) are units, so the weighted integrand is comparable to

\[
|s|^{1-2c},
\]

which is locally integrable iff \(c<1\). Hence the sole chart value is \(1\), while downstairs it is \(3/4\). The theorem asserts

\[
\frac34=1.
\]

The failure is not an uncovered null set: the neighborhood is fully covered, but by a remote source branch invisible to `wrlctAt … 0`.

Injectivity is absent. This witness is even injective on the rectangle; only \(0\) and \((1,0)\) collide. A mere a.e.-injectivity field would not repair it.

`rlctAt_sumSqFam_le_chart` states the correct direction

\[
\operatorname{rlctAt}(\text{downstairs})\le
\operatorname{wrlctAt}(\text{chart}),
\]

and here \(3/4\le1\). But its proof is not independent: it rewrites using the false atlas equality. It does not prove the missing direction \(\min_c\operatorname{wrlctAt}_c\le\operatorname{rlctAt}\).

A low redundant chart was not needed. The decisive omission is control of every relevant source point over \(x_0\), rather than only the distinguished origin.

## 2. Guarded Object A — PARTLY COUNTEREXAMPLE, VERIFIED

Subverdicts for [IdealInvariance.lean](/tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/IdealInvariance.lean:110):

- `rlctAt_mono_of_eventually_le`: SOUND-as-stated.
- Unweighted germ-representation `≤`: SOUND-as-stated.
- Unweighted two-sided equality: SOUND-as-stated.
- Weighted germ-representation `≤`: COUNTEREXAMPLE.
- Weighted two-sided equality: COUNTEREXAMPLE.

The weighted statements omit measurability hypotheses.

Let \(n=1\), \(x=0\), \(W\equiv1\). Choose \(A\subset\mathbb R\) that is not measurable modulo null sets in any neighborhood of zero. Such an \(A\) can be formed from nonmeasurable subsets of disjoint intervals tending to zero.

Writing \(z=w(0)\), define

\[
G=(z1_A,z1_{A^c}),\qquad
F=(2z1_A,z1_{A^c}).
\]

Then

\[
\sum G_i^2=z^2,\qquad
\sum F_i^2=
\begin{cases}
4z^2,&z\in A,\\
z^2,&z\notin A.
\end{cases}
\]

All hypotheses hold:

- \(G\) is represented by \(F\) using \(\operatorname{diag}(1/2,1)\).
- \(F\) is represented by \(G\) using \(\operatorname{diag}(2,1)\).
- Both coefficient systems are continuous.
- Both weighted zero sets are \(\{0\}\), satisfying `LocallyNullZerosW`.
- \(W\ge0\).
- The admissible sets are bounded.

For \(G\), the threshold is \(1/2\). For \(F\), every \(c>0\) gives a non-a.e.-measurable negative power on every neighborhood: its two distinct values recover \(1_A\). Thus only \(c=0\) is admissible, giving threshold \(0\).

Therefore weighted `≤` asserts \(1/2\le0\), and weighted equality asserts \(1/2=0\).

The zero guard itself is sufficient—indeed stronger than necessary. Since it uses \(\{WK=0\}\), a positive-measure zero set of \(W\) is excluded. Its comment is inaccurate, however: the actual integrand is \(W K^{-c}\), not \((WK)^{-c}\).

Repair: require measurability of \(W\) and the target family in weighted `≤`, and both families for weighted equality.

## 3. `no_unit_forces_axis_jac_coupled` — SOUND-as-stated, VERIFIED

The eventual identity holds throughout some neighborhood. Put \(u=(t,t)\), \(t\ne0\). Then

\[
3|t|^4=|t|^2w(t,t),
\]

so \(w(t,t)=3|t|^2\to0\). Continuity forces \(w(0)=0\), contradicting `w 0 ≠ 0`.

## 4. `coreGen` / `coreReduction` — COUNTEREXAMPLES, VERIFIED

`coreGen` itself is concrete and correctly indexed: `finProdFinEquiv.symm` enumerates every row/column entry of `mult d (e u)`, and its sum of squares agrees with the trace definition of `lossDLN d 0`.

But [coreReduction](/tmp/aoyagi-v3-review/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean:68) is false because it accepts any measure-preserving `MeasurableEquiv` fixing zero, without continuity.

Take \(N=1\), \(d=(1,1)\), identifying both parameter spaces with \(\mathbb R\). Let \(e\) be the measure-preserving involution swapping by translations

\[
(-1,0)\leftrightarrow(1,2),\qquad
(0,1)\leftrightarrow(-2,-1),
\]

and fixing zero and everything else.

Then:

\[
\operatorname{rlctGlobal}(a^2)=\frac12.
\]

But the flattened core is \(e(u)^2\), which is bounded away from zero on the punctured neighborhood \((-1,1)\) and is zero only at \(u=0\). Every \(c\ge0\) is locally admissible. Its unbounded real `sSup` is the documented junk value \(0\). Thus `coreReduction` asserts \(1/2=0\).

There is a second false frontier statement: `exists_coreResolution` omits even `e 0 = 0`. For the same \(d\), take \(e(u)=u+1\). Then `coreGen d e 0 = 1`. But every proposed chart has:

- `hg0 : g 0 = 0`;
- `hbind` and `hchain`, forcing every monomial generator to vanish at zero;
- `hideal_fwd`, forcing every pulled-back `coreGen` to vanish at zero.

Contradiction. Hence no such `Resolution` exists.

## 5. Banked reuse — MISMATCH, VERIFIED

The banked flatten is general-width, not `(2,2,2)`-only:

```lean
paramsEquivFlat (H : Fin (L + 1) → ℕ) :
  Params H ≃ᵐ (Fin (DLNFibre.DLN.RLCT.flatDim H) → ℝ)
```

with `measurePreserving_paramsEquivFlat` and separate continuity/inverse-continuity theorems in [ParamsFlat.lean](/tmp/aoyagi-v3-review/lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat.lean:80).

Exact deltas:

- Banked `Params H` uses matrices \(H_s\times H_{s+1}\); `Tuple d` uses \(d_{s+1}\times d_s\). A transpose per layer is required.
- The banked direction is `Params → flat`; `exists_flatten` wants `flat → Tuple`.
- The two `flatDim`s agree propositionally using multiplication commutativity, not definitionally.
- Zero preservation is not packaged in the banked theorem.
- `exists_flatten`/`coreReduction` discard the banked homeomorphism structure.

The deepest result is exactly:

```lean
deepest_le_of_homogeneous_core
  (F) (v) (D) (hFmeas)
  (hhomog : ∀ c w, F (c • w) = c ^ D * F w) :
  rlctAtOn F 0 ≤ rlctAtOn F v
```

It is a local inequality in `ENNReal`; see [DeepestMinRlct.lean](/tmp/aoyagi-v3-review/lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean:157). `coreReduction` requires an equality between an ℝ-valued global RLCT and an ℝ-valued local RLCT. Missing bridges are:

- global \(=\) minimum local;
- `ENNReal` to ℝ;
- topology-preserving flatten transport.

None of `ParamsFlat`, `DeepestMinRlct`, or the relevant bridge module is in `LearningCoefficient`’s import cone. The reuse claim is currently commentary, not composition.

## 6. Two-chart blow-up inhabitation — SOUND-as-stated, VERIFIED

For \(F=(x,y)\), use

\[
g_1(u,v)=(u,uv),\qquad g_2(u,v)=(uv,v).
\]

Chart 1:

- dominant monomial \(u\), `bexp=(1,0)`;
- \(\det Dg_1=u\), `jac=(1,0)`, unit \(1\);
- \((u,uv)\) represents \(\langle u\rangle\) using coefficients \(1,v\), and \(u\) is the first generator.

Chart 2:

- dominant monomial \(v\), `bexp=(0,1)`;
- \(\det Dg_2=v\), `jac=(0,1)`, unit \(1\);
- \((uv,v)\) represents \(\langle v\rangle\) using coefficients \(u,1\), and \(v\) is the second generator.

In both charts, `hchain`, `hbind`, unit multiplicity, analyticity, and `hjac` hold globally.

For \(\varepsilon>0\), take

\[
\mathrm{dom}_1=[-\varepsilon,\varepsilon]\times[-1,1],\qquad
\mathrm{dom}_2=[-1,1]\times[-\varepsilon,\varepsilon],
\]
and \(U=(-\varepsilon,\varepsilon)^2\).

If \(|y|\le|x|\), use \(g_1(x,y/x)\); if \(|x|\le|y|\), use \(g_2(x/y,y)\). Thus the two compact images cover \(U\) exactly.

This positive example inhabits the record, but it does not validate the general CoV theorem: here the monomial identities remain valid throughout the compact domains, unlike the counterexample in target 1.

## Overall

Ranked false statements:

1. `rlctAt_sumSqFam_eq_iInf_charts`: remote-branch atlas counterexample \(3/4\ne1\).
2. `exists_coreResolution`: arbitrary flatten need not send zero to zero.
3. `coreReduction`: discontinuous measure-preserving flatten gives \(1/2\ne0\).
4. Weighted Object-A `≤` and equality: missing measurability gives \(1/2\ne0\).

Consequently v4 does not clear the frontier-soundness bar.
## Q1

**NO — the arm is not provable from the stated hypotheses.** Your counterexample is correct.

Take zero shear and \(F(v)=v_{\mathrm{pivot}}\). Then \(F\) satisfies `hslot` and `Deg1SupportedOn center`, but

\[
F(qm(u))=1.
\]

Every \(S'\)-supported decomposition vanishes when all \(S'\)-coordinates vanish, whereas this function equals \(1\), including at \(u=0\). `PerLayerDeg1From` does not help: constants are affine of degree \(0\) on every layer.

## Q2

The weakest implementation-ready missing obligation is precisely clause 1 on the strict transform. Writing \(S'=\operatorname{blockCoords}(d,S+1)\) and \(g_j(u)=F_j(qm(u))\):

\[
\forall j\;\exists c'_k,\quad
(\forall k,\ c'_k\text{ continuous})\ \land\
g_j(u)=\sum_{k\in S'}c'_k(u)u_k.
\]

The full `Deg1SupportedSlot g j S' (S+1) univ` is sufficient but stronger than necessary: its `PerLayerDeg1From` conjunct follows structurally because, on layers \(\ell\ge S+1\), `qm` fixes that layer and its other components ignore it.

The semantic core is the weaker vanishing condition

\[
u|_{S'}=0\Longrightarrow g_j(u)=0.
\]

Together with the derived continuity and layer-\((S+1)\) affinity, this is equivalent to the required support decomposition.

**Truth status:** this is **not** implied by the listed pins. It is expected to be **true for the intended DLN residuals** by the Schur/cofactor calculation: the pivot coefficient still contains a factor from the next-layer block. That is additional monument content and must be proved or stubbed. Consequently, the advertised gate cannot close this arm without such an obligation.

## Q3

**Impossible from the stated hypotheses.**

The available expression is

\[
g_j(u)=c_p(qm(u))
+\sum_{i\in P\setminus\{p\}}c_i(qm(u))\,\operatorname{edgeShear}(u)_i,
\]

where \(P\) lies in layer \(S\), disjoint from \(S'\) in layer \(S+1\). Nothing says that \(c_p(qm(u))\), or any other summand, contains an \(S'\)-factor.

With the missing cofactor identity

\[
c_i(qm(u))=\sum_{k\in S'}a_{ik}(u)u_k,
\]

one could take

\[
c'_k(u)=a_{pk}(u)+
\sum_{i\ne p}a_{ik}(u)\operatorname{edgeShear}(u)_i.
\]

That identity is exactly the absent cross-layer content.

## Q4

### (a) \(\delta=0\)

All nonterminal subcases are provable:

- `case11`: **YES**
- `case12`: **YES**
- `case2`: **YES**
- `rollover`: **YES**

The child support and threshold equal the parent’s. Canonical centers lie below that threshold, while the shear writes only below it and ignores every layer above it. Hence the pullback preserves both the support decomposition and each `AffineOn` grade.

### (b) \(\delta=1\), `case11`

For a genuine case11 branch: **YES, provided one uses the real-branch pivot-separation fact**

\[
\mathrm{pivot}\notin \operatorname{blockCoords}(d,S).
\]

The reused pivot was born in an earlier layer. Since case11 has identity shear,

\[
F_j(qm(u))
=\sum_{i\in P}c_i(qm(u))u_i,
\]

so no pivot constant term arises and the per-layer grades are preserved.

If pivot separation is not among the available consequences, the arm is **not** provable: \(F=v_{\mathrm{pivot}}\) breaks it, and `Deg1SupportedOn ed.center` does not repair that.

`realBranch_boostReady_case11` resolves only conjunct A—the `StepInv` divisibility identity. It neither supplies nor is needed for conjunct B once pivot separation is available.
# Independent review

## 1. Fidelity

### A — ideal invariance

**VERIFIED — faithful, with the mandated corrected sign.** `GermIdealSubset G F` means \(G_i\in\langle F\rangle\), and Lean concludes
\[
\operatorname{rlct}\!\left(\sum G_i^2\right)\le
\operatorname{rlct}\!\left(\sum F_j^2\right),
\]
then obtains equality from mutual containment ([IdealInvariance.lean:109](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/IdealInvariance.lean:109)). This matches corrected Aoyagi Lemma 1 at [worked.tex:153](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:153).

**VERIFIED — weighted form is not literally Aoyagi’s lemma, but is a valid strengthening.** Multiplying both comparison inequalities by the same nonnegative weight is the correct operation ([IdealInvariance.lean:148](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/IdealInvariance.lean:148)). Its measurability and a.e.-nonzero assumptions make it narrower than the analytic-germ statement, not stronger in a dangerous way.

### B — product resolution

**VERIFIED — `ideal_identity` reflects Aoyagi’s central ideal identity.** It matches the recursive invariant and terminal diagonalisation at [worked.tex:475](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:475)–490.

**VERIFIED — major fidelity defect in the resolution datum.** The type of `g` carries no proposition saying:

- source and target have the same dimension;
- \(g(0)=0\);
- \(g\) is analytic, proper, or birational;
- `jacWeight res.jac` is its absolute Jacobian up to a nonvanishing unit;
- the charts cover the exceptional fibre.

These properties occur only in comments ([ProductResolution.lean:90](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean:90)). Nevertheless `properMapRlctInvariance` asserts the CoV equality for every `res` ([ProductResolution.lean:129](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean:129)).

This does not faithfully express the paper’s proper resolution. Aoyagi uses a proper map, local charts, the actual Jacobian, and a minimum over charts ([worked.tex:173](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:173)–189; [worked.tex:499](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:499)–520).

**VERIFIED/INFERRED — `divisor_spec` overclaims the paper.** The paper identifies terminal candidates \(M_{s,k}=Mval(t)\) and their minimum ([worked.tex:529](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:529)–542). It does not state that the axes of one chart range exactly over every value \(G_{\rm qip}(d,e)\) for every feasible \(e\). That exact-image assertion needs a separate theorem and is geometrically more naturally indexed by `(chart, divisor)`.

**INFERRED — unconditional existence is false in degenerate widths.** For \(N=1,d=(0,1)\), the unique feasible QIP point has \(G_{\rm qip}=0\), while `divisor_spec` requires some `jac j + 1 = 0`, impossible for `jac j : ℕ`. Thus [exists_coreLoss_monomialisation](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean:119) needs positivity/nondegeneracy hypotheses or a separate zero-core case.

### C — monomial RLCT

**VERIFIED — this is not Aoyagi’s boxed rule as stated.** Aoyagi’s rule applies after the pullback has become a single normal-crossing monomial times a unit ([worked.tex:173](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:173)–189). Lean assumes only
\[
k_j=\min_i e_{ij},
\]
which records coordinate-axis orders but not principal normal crossings or the full Newton polyhedron ([MonomialRLCT.lean:85](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/MonomialRLCT.lean:85)).

**INFERRED — the theorem is false.** Coordinatewise minima miss coupled valuations; see the explicit counterexample below. This is a load-bearing mis-transcription.

### D — boxed value versus codimension

**VERIFIED — non-circular and mathematically sensible conditionally.** Its conclusion mentions only `boxedRLCT`, divisor data, and `cCodim`; it contains no RLCT of the original loss ([Engine.lean:46](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/Engine.lean:46)). Given the exact-image `divisor_spec`, it really is
\[
\min_j(\mathrm{jac}_j+1)=\min_eG_{\rm qip}(d,e)=cCodim.
\]
This matches the minimum-level geometric reformulation at [worked.tex:537](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:537)–542.

It is close to a combinatorial tautology given `divisor_spec`, but it is not circular. The unsupported strength lies in B’s divisor specification, not D.

### Corollary

**VERIFIED — the Frobenius-loss identity and deepest-point reduction are faithful.** Compare [LearningCoefficient.lean:34](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean:34) and [LearningCoefficient.lean:45](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean:45) with [worked.tex:120](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:120)–128 and Aoyagi Theorem 4 at [worked.tex:437](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex:437)–458.

**VERIFIED — the final statement is only a conditional assembly, not yet Aoyagi’s corollary.** It assumes `res`, five analytic side conditions, `hmono`, `hqip`, and `hpos` ([LearningCoefficient.lean:57](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean:57)). It never obtains `res` from `exists_coreLoss_monomialisation`, and measurability cannot be derived from the current record because `g` is an arbitrary function. Thus Object A is now load-bearing, but B’s existence theorem remains off the final dependency cone.

## 2. Math sense-check

### (a) Is `ideal_identity` non-vacuous?

**Yes, narrowly.** For a fixed genuine chart \(g\), a generic monomial family does not generate the pulled-back product ideal. It genuinely constrains `b`.

However, it constrains only \(\langle(\prod C)\circ g\rangle\), and `g` is chosen simultaneously without geometric conditions. Therefore it does not by itself certify a resolution of the original tuple space.

### (b) Is D non-circular?

**Yes.** It is a real min-over-image computation and is not logically equivalent to `rlct = cCodim/2`.

### (c) Is weighted ideal invariance correct, and is `transfer` derived?

**Mixed.**

- Weighted ideal invariance is the correct tool.
- **VERIFIED:** `transfer` is syntactically proved from `properMapRlctInvariance` and weighted A ([ProductResolution.lean:150](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean:150)–155).
- Semantically, the unconstrained `properMapRlctInvariance` has reintroduced an opaque RLCT equality one step earlier. Thus the repair is not yet honest at the geometric frontier.

### (d) Is proper-map CoV a sound bridge?

**Conceptually yes; this statement no.** The monomial absolute Jacobian belongs in the transformed integral. But the correct local statement is normally a minimum over points/charts above the source point, using the actual Jacobian up to a positive unit. Equality with one arbitrary chart at its origin is unjustified.

### (e) Explicit counterexample and other smells

Take \(N=1,d=(1,2)\). Then tuple space is \(\mathbb R^2\) and
\[
coreLoss(a,b)=a^2+b^2,\qquad \operatorname{rlct}_0=1.
\]
Let
\[
g(x,y)=(xy^2,x^2y),\quad
b_1=xy^2,\quad b_2=x^2y,\quad
vanish=(1,1),\quad jac=(1,1).
\]

**INFERRED, direct check:**

- `ideal_identity` holds exactly.
- `vanish_spec` holds.
- The unique feasible QIP point has \(G_{\rm qip}=2\), so `jac+1=2` satisfies `divisor_spec`.
- All measurability/a.e.-nonzero side conditions hold.

But
\[
W=|xy|,\qquad
K\circ g=x^2y^2(x^2+y^2),
\]
whose weighted threshold is \(2/3\): polar coordinates give radial integrability precisely for \(c<2/3\). Therefore:

- `properMapRlctInvariance` falsely asserts \(1=2/3\);
- C falsely asserts \(2/3=1\), since both axis ratios equal \(1\).

The actual Jacobian is
\[
|\det Dg|=3|x|^2|y|^2,
\]
not `jacWeight (1,1)`. This pinpoints the missing Jacobian certificate. Even with the actual Jacobian, C’s axis-only formula still misses the coupled Newton valuation.

Object E is also only a placeholder: `ncOrder_regularSeq` is a pure finite-count identity, not Aoyagi’s analytic pole-multiplicity theorem, and it is import-only rather than on the engine dependency cone. Moreover a global order must count simultaneously intersecting binding divisors, not all binding axes across unrelated charts.

## 3. Verdict

**FAIL: the repair fixes the original non-vacuity and circularity complaints, but the blueprint still has load-bearing false statements.**

Ranked defects:

1. **Critical:** Object C is false for coupled monomial families; `hvo` does not encode normal crossings or a Newton polyhedron.
2. **Critical:** `properMapRlctInvariance` lacks every geometric/Jacobian/atlas hypothesis and is itself false for admissible records.
3. **High:** B collapses a multi-chart resolution into one Euclidean chart and asserts an unsupported exact QIP-image specification.
4. **High:** `exists_coreLoss_monomialisation` is false for permitted zero-width cases.
5. **Medium:** the “corollary” remains conditional; resolution existence and analytic side-condition discharge are not wired into it.
6. **Nonblocking/deferred:** E does not yet formalize Aoyagi’s order theorem.

A sound repair needs an atlas-level resolution certificate with actual Jacobian data, a principal-normal-crossing condition or the genuine Newton-polyhedron rule, and a closed wrapper that obtains the resolution and discharges its analytic conditions.
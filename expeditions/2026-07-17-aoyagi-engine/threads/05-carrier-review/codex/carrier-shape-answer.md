Overall verdict: reject the current obligations as a faithful resolution certificate. The edge-labelled tree is an appropriate carrier, but `StepRel` does not certify the paper’s state transitions, and `ChartBridge` does not support the advertised transport argument.

### Q1 — Case 1(1): not faithful

**Fact.** The Case-1(1) clause in [`StepRel`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Engine/EngineObligations.lean:76) never reads `e.child`. Therefore it drops

\[
M'_{s,k}=M_{s,k}+J_1(M^{(S+1)}-J).
\]

Concrete counterexample: take a parent with one divisor, `divExp 0 = 5`, `divTilde 0 = cleared`, \(J_1=2\), and `resCols = 3`. The correct child exponent is \(11\). A Case-1(1) edge whose child exponent is \(0\), \(11\), or \(99\) satisfies exactly the same `StepRel`.

So `∀ p ∈ stepEdges, StepRel ...` permits wrong child exponents.

**Encodability.** Pattern matching on `e.child` gives access to its root state, but the present carrier still lacks two necessary pieces:

- the run length \(J_1\);
- a correspondence identifying a parent divisor with the same child divisor when the `Fin numDiv` types change.

Add an edge transition record containing `runLen` and either a stable divisor identifier or an embedding from parent divisor indices to child indices. Then require the child update explicitly.

This defect affects all cases. Case 2 creates a child divisor, yet the current clause searches the parent ledger. Case 1(2) checks a parent `bExp`, but never asserts that the child advances `cleared` or contains the new pivot.

The checked `(2,2,4)` witness is already a concrete warning: it declares residual dimensions \(1\times1\), although `layer=0`, `cleared=0`, and the documented semantics give \(2\times2\); it uses `localSub=id`, and still proves Case-2 `StepRel` ([witness](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Engine/CanonicalWitness224.lean:24)).

### Q2 — Transport: signature mismatch and laundering risk

**Verdict: `region_glue` cannot use the named lemma on `chartMap`.**

The banked theorem requires an inverse, inverse derivative, open neighbourhood, fixed point, inverse identities, measurability, and determinant bounds in both directions ([signature](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean:292)). `LeafJacobian` provides none of the inverse-side data.

More decisively, for

\[
\pi(u,y)=(u,uy),\qquad |\det D\pi|=|u|,
\]

no positive lower determinant bound exists on any neighbourhood containing \(u=0\), and no local inverse exists there. Thus this is not a missing Lean convenience; the required proposition is mathematically false for the singular blow-up factor.

There are two sound routes:

- Expose `chartMap = ψ ∘ β` (or the appropriate order), where `ψ` is a bounded-unit local diffeomorphism with full inverse data, and `β` is the singular monomial blow-up. Apply the local-homeomorphism lemma only to `ψ`, and a separate area/CoV theorem plus monomial integration to `β`.
- Avoid factorization, but strengthen the leaf certificate sufficiently for a direct area formula: measurable source, appropriate a.e. injectivity, differentiability, measurable Jacobian, and a bounded product-sector domain.

The present bundle supports neither route completely. Therefore the `sorry` in `region_glue` currently owns the singular change-of-variables theorem itself, not merely “assembly.” That is a real laundering risk.

### Q3 — Structurally sound, semantically weaker

**Fact.** `terminalExponents` is a flat-map over recursively reachable leaves ([definition](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Engine/ResolutionTree.lean:188)). Hence membership:

- cannot hold vacuously for an empty list;
- does imply that some structurally emitted leaf contains that numerical exponent;
- does not require a separately stored edge list to rule out an off-tree leaf.

But it does not prove the advertised stronger facts:

- the leaf profile equals the chosen `tStar`;
- the leaf has a nonempty source domain;
- the binding divisor actually approaches zero on a positive-measure chart region.

A dummy emitted leaf with `srcBox = ∅` satisfies `InjOn`, `LeafPullback`, and `LeafJacobian` vacuously and can contribute `minAdm` to `terminalExponents` while playing no role in the atlas cover. Thus attainment can be analytically phantom even though it is not structurally phantom.

For binding-cell realization, use a witness such as

\[
\exists(l,\mathrm{comp})\in\mathrm{leafPaths},\ \exists k,\quad
l.\mathrm{divProfile}(k)=tStar(M),\quad
l.\mathrm{divExp}(k)=\minAdm(M),
\]

together with a live-domain/exceptional-locus condition. An explicit path alone does not exclude an empty chart.

### Q4 — Further soundness gaps

The main additional gaps are:

- **Residual Morse threshold omitted.** If the pullback is \(u^2z^2\) with Jacobian weight \(|u|^{e-1}\), integrability also requires \(c'<\mathrm{resRank}/2\). For `resRank = 1`, `e = 2`, and \(c'=3/4\), `hrat` holds since \(3/4<1\), but the \(z\)-integral \(\int |z|^{-3/2}\,dz\) diverges. Either include every positive `resRank` in the threshold ledger or prove `resRank = 0 ∨ minAdm ≤ resRank`.

- **Coordinate independence is only a comment.** `divCoord` and `resCoord` need injectivity and disjoint ranges. If two divisors use the same coordinate, individual conditions \(c'<e_k/2\) are generally false as a combined threshold.

- **Profiles need admissibility.** `IsFullMonomialization` does not require `divProfile k ∈ Adm M`. For \(M=(2,2,4)\), the non-admissible profile \(T=(0,4)\) nevertheless has \(Mval(T)=4=\minAdm(M)\). Relabelling a legitimate exponent-4 leaf by this impossible profile preserves every current analytic predicate.

- **Transition metadata is disconnected.** `jacPow` is never related to the derivative or folded into leaf `divExp`; `StepRel` never examines `subst`; and `bExp`/`support` are not connected to `LeafPullback`. These fields can be corrupted without changing the analytic certificate.

- **Source-domain conditions are absent.** `srcBox` need not be measurable, bounded, product-shaped, or nonempty. Those properties are needed for the stated monomial/radial reads. For genuine blow-up boxes, full `InjOn` also fails on the exceptional fibre; a.e. injectivity or deletion of a specified null subset is the natural condition.

- **Jacobian sign is wrong unless charts are sign-restricted.** The identity should use \(\prod |u_k|^{e_k-1}\), or explicitly require a fixed-sign sector.

Finally, the current engine proves only finiteness below the candidate threshold. Numerical attainment alone does not prove divergence at the threshold. If `rlct ≤ codim/2` is supplied independently, that can provide equality; otherwise the resolution bundle does not establish the claimed tightness.
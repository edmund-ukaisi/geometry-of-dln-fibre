## Verdict

- **Finiteness soundness:** `StepRel` is irrelevant. It could be replaced by `True` without changing the driver’s argument. I find no soundness break traceable to its existential child read.
- **Resolution fidelity:** reject. The existential is far too weak to certify a faithful Aoyagi transition.
- **Sharing corruption:** can satisfy the full bundle as corrupted metadata, but cannot raise the certified threshold unless `ChartBridge`/`region_glue` is itself unsound.

### Q1: no StepRel-based soundness counterexample

**Fact from the code.** The driver uses `coverage_theorem`, `region_glue`, and only the lower-bound half `.1` of `exponent_ledger_bridge`; it never uses `case_step_invariant`, terminal attainment, or `.2` of the exponent bridge ([EngineDriver.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Engine/EngineDriver.lean:44)).

For every terminal exponent,
\[
c'<\frac{\minAdm M}{2},\qquad \minAdm M\le e
\quad\Longrightarrow\quad
c'<\frac e2.
\]
That is the entire ledger argument. `StepRel`, root data, live attainment, and even profile labels do not enter it.

**Inference, conditional on the analytic hole being valid.** No tree can satisfy `ChartBridge` plus these ratio inequalities and falsify finiteness. Such a tree would directly refute `region_glue`, regardless of whether `StepRel` were existential, exact, or absent. Strengthening `StepRel` would not repair that counterexample.

Because [`region_glue`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Engine/EngineObligations.lean:197) is currently `sorry`, Lean itself does not establish that its hypotheses are analytically sufficient. Thus I can assert dependency non-use as fact, but analytic sufficiency remains an inference until that hole is filled.

### Q2: sharing cannot manufacture a too-large `minAdm`

The proposed failure is algebraically impossible under conjunct 5:

\[
\minAdm M\in E,\qquad \forall e\in E,\ \minAdm M\le e,
\]
where \(E=\texttt{terminalExponents}(t)\). Therefore the terminal minimum is literally `minAdm M`; it cannot be “wrong and too large.” Moreover, `minAdm` is independently defined from `Adm` and `Mval` ([RouteMLayerSplit.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev2/lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerSplit.lean:50)). Changing `support` cannot change it or `terminalExponents`.

The real analytic guard is:

- exact `LeafPullback`,
- exact `LeafJacobian`,
- genuine chart coverage,
- the terminal-exponent lower bound.

It is not `StepRel`.

For the sharing obstruction:

\[
F_{\mathrm{shared}}=\delta^2(x^2+y^2)
\]
has a valid terminal form with divisor \(u=\delta\) and a two-dimensional residual core. But
\[
F_{\mathrm{indep}}=\delta_1^2x^2+\delta_2^2y^2
\]
cannot masquerade as the same leaf identity. Claiming both divisors would require divisibility by \(\delta_1^2\delta_2^2\); setting \(\delta_2=0\) and \(\delta_1x\ne0\) contradicts that identity. Claiming only \(\delta_1\) similarly fails at \(\delta_1=0,\delta_2y\ne0\).

So:

- corrupted sharing metadata is reachable;
- the resulting false analytic threshold is not reachable if `ChartBridge` and `region_glue` mean what they state.

### Q3: existential `StepRel` fails fidelity

Concrete Case-1(1) counterexample:

- parent exponents: `[5, 37]`;
- parent tilde levels: `[0, 9]`;
- `cleared = 0`, `runLen = 2`, `resCols = 3`;
- child exponents: `[11]`.

Current `StepRel` succeeds using `kp = 0`, `kc = 0`, since
\[
11=5+2\cdot3.
\]
But the parent divisor of exponent \(37\) simply disappears. Nothing records whether it persisted, merged, or was corrupted.

There is also a full-bundle corruption schema. Given any
\[
t=\operatorname{branch}(n,\mathrm{edges})
\]
satisfying `CanonicalResolution`, replace the root ledger by \(n^+\), obtained by appending one dummy divisor:

- extend `bExp` by a constant-zero coordinate;
- give the dummy arbitrary `divExp`, `divTilde`, and support membership;
- leave all old divisor data, edges, substitutions, children, and leaves unchanged.

Every old existential witness embeds into the enlarged parent, so all outgoing `StepRel`s remain true. Every other conjunct depends on leaves, substitutions, or root `layer/cleared`, so it remains true. Yet the dummy divisor vanishes immediately at every child. Thus the **full bundle admits a non-faithful tree**, though its analytic conclusion is unchanged.

This is a fidelity defect, not a finiteness-soundness defect.

### Q4: minimal repair

To block the disappearing-divisor example, require on every edge:

1. an injection from parent divisors to child divisors;
2. equality of child and parent data for every unchanged divisor;
3. a distinguished updated/new divisor with the case-specific exponent equation.

That still does not validate sharing. Add an exact support-propagation equation under appropriate divisor and generator maps, including the case-specific rule for the new/merged divisor. A cleaner formulation is to define a typed `stepUpdate` and require the child root ledger to equal its output.

No extra “tie `minAdm` to a live profile” clause is needed: live attainment plus `IsFullMonomialization` already yields a live \(k\) with
\[
\operatorname{divExp}(k)=\minAdm M
 = Mval(M,\operatorname{divProfile}(k)),
\qquad \operatorname{divProfile}(k)\in Adm(M).
\]

The clean architectural split is: an `AnalyticCertificate` consumed by the driver, and a stronger `FaithfulAoyagiResolution` with exact transition and support propagation.
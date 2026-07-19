Verdict: C1 has the safe quantifier direction. C2+C3 identify the two ledgers only as sets of `(exponent, profile)` values, not as indexed multisets. The standalone predicate admits vacuous and fabricated models, but it never re-admits the `t̃>0` divisors.

### Q1 — C1 does not smuggle completeness

For a leaf, let

\[
P_{\mathrm{an}}=\{\,l.\mathrm{divProfile}(k):k:\mathrm{Fin}(l.\mathrm{numDiv})\,\}.
\]

C1 says exactly

\[
\forall T\in P_{\mathrm{an}},\quad T\in\operatorname{Adm}(M),
\]

hence \(P_{\mathrm{an}}\subseteq\operatorname{Adm}(M)\).

C2+C3 imply that the analytic and full-`t̃=0` profile supports coincide, so C1 propagates to

\[
P_{\mathrm{full},0}\subseteq\operatorname{Adm}(M).
\]

There is nowhere a quantifier of the forbidden form

\[
\forall T\in\operatorname{Adm}(M),\ \exists l,k,\ l.\mathrm{divProfile}(k)=T.
\]

Concrete countermodel to completeness: take \(L=2\), \(M=(2,2,2)\). Then

\[
\operatorname{Adm}(M)=\{(0,0),(1,0),(2,0)\}.
\]

A leaf whose analytic and full ledgers each contain only \((e,T)=(4,(0,0))\) satisfies C1–C3, since \(Mval(M,(0,0))=4\), while omitting two admissible profiles. It even omits the minimizing profile \((1,0)\), whose value is \(3\).

Thus the direction is unequivocally safe.

### Q2 — Equality of value supports, not exact sublists

Define the pair-valued supports

\[
A_l=\{(l.\mathrm{divExp}(k),l.\mathrm{divProfile}(k)):k\},
\]

\[
F_l^0=\{(l.\mathrm{fullDivExp}(j),l.\mathrm{fullDivProfile}(j)):
\widetilde t(l.\mathrm{fullDivProfile}(j))=0\}.
\]

Then:

- C2 proves \(A_l\subseteq F_l^0\).
- C3 proves \(F_l^0\subseteq A_l\).

Therefore C2+C3 prove \(A_l=F_l^0\) as sets of values.

They do not provide:

- an injection or bijection between indices;
- equality of cardinalities;
- equality as multisets;
- an order-preserving “sublist” embedding;
- coherent mutually inverse witnesses;
- preservation of divisor identity or coordinates.

For example, with \(T=(0,0)\), \(e=4\):

- two analytic entries both equal to \((4,T)\) may both match one full entry;
- one analytic entry may match two full `t̃=0` entries both equal to \((4,T)\).

Both models satisfy C1–C3.

Consequently, the docstring’s “EXACTLY the sublist” wording at [EngineDefs.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev-spine/lean/DLNFibre/DLN/RLCT/Engine/EngineDefs.lean:209) is stronger than the predicate itself.

For the stated downstream use—sets and minima of exponents—the weakening is harmless. C2+C3 preserve exactly the support of `t̃=0` exponent values, and duplicates do not affect membership or a minimum. This matches how the divisor portion of `terminalExponents` is formed in [ResolutionTree.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev-spine/lean/DLNFibre/DLN/RLCT/Engine/ResolutionTree.lean:284). If the support is empty, both sides are empty; the canonical bundle separately supplies attainment.

Multiplicity-sensitive uses—component counts, divisor identity, coordinate products, or pole-order arguments—cannot be justified from C2+C3 alone.

Importantly, the actual `leafOfState` constructor is stronger than this specification: it builds the analytic ledger by filtering the full indices through `t0Indices`. Thus the construction preserves multiplicity and index selection even though `IsFullMonomialization` forgets that fact.

### Q3 — Standalone vacuity is real, but the actual exponent equality is not definitional

There are two direct vacuity cases.

1. A leafless tree is admitted. `ResolutionTree.branch n []` has `leaves = []`, so the outer universal quantifier is vacuous.

2. For a leaf with `numDiv = 0`, C1 and C2 are vacuous. C3 reduces to “the full ledger has no `t̃=0` entry.”

For example, with \(L=1\), a leaf may have:

- `numDiv = 0`;
- one full divisor with profile \(T=(1)\), hence `tildeOf T = 1`;
- an arbitrary full exponent, say \(999\).

C1–C3 hold and the exponent \(999\) is completely unconstrained. If that full profile had `t̃=0`, however, C3 would fail because no `k : Fin 0` could witness it.

Regarding definitional aliasing:

- Hypothetically, if `divExp` were defined as `Mval(...).toNat`, the equality half of C1 would be tautological. Membership and C2/C3 would still impose constraints.
- In the actual carrier, `divExp` is an independent field; see [ResolutionTree.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev-spine/lean/DLNFibre/DLN/RLCT/Engine/ResolutionTree.lean:133).
- The construction maintains the separate `MvalCoh` invariant and proves the `toNat` equality from it in [EngineConstruction.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev-spine/lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean:1365).

So there is no actual definitional-alias vacuity. Nevertheless, the predicate is extensional: by itself it cannot distinguish a genuinely accumulated exponent from a fabricated field populated using `Mval`. Correct transition history comes from `StepRel` and the construction, not C1.

`CanonicalResolution` additionally requires chart coverage, terminal-exponent attainment, and live attainment; those conditions rule out the empty-tree and all-empty-analytic-ledger models.

### Q4 — Other weaknesses; no `t̃>0` overreach

Other limitations of the predicate itself are:

- It does not ensure realization of the minimum of `Adm`; the \(M=(2,2,2)\) singleton example passes while missing the value \(3=\minAdm(M)\).
- It imposes no condition whatsoever on full entries with `t̃>0`: their exponents and profiles may be arbitrary.
- It does not tie the ledgers to root data or legal transitions.
- It does not express chart coverage, pullback monomialization, Jacobians, divisor-coordinate identity, or the folding of stranded divisors into the residual core.
- It does not relate `resRank` to the full stranded ledger.
- It does not preserve multiplicity or index identity, as above.

Those responsibilities are distributed among `StepRel`, `ChartBridge`, exponent hooks, and live attainment in [CanonicalResolution](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/rev-spine/lean/DLNFibre/DLN/RLCT/Engine/EngineDefs.lean:221).

There is no hidden re-admission of stranded divisors:

- C1 quantifies only over analytic indices.
- C2 explicitly requires the matched full divisor to have `t̃=0`.
- C3 has a `t̃=0` antecedent.

Thus no conclusion about a `t̃>0` full divisor can be extracted.

Finally, `.toNat` is not a truncation loophole here. For \(T\in Adm(M)\), weak decrease and the coordinate bounds make both factors in every summand of `Mval` nonnegative. Hence \(Mval(M,T)\ge0\).

### Fact vs inference

Direct facts from the Lean definitions:

- `divExp` and `fullDivExp` are independent stored fields.
- Trees may have no leaves, and leaves may have `numDiv = 0`.
- C2/C3 contain only existential value matches.
- The actual constructor filters full indices using `t0Indices`.
- `CanonicalResolution` adds transition, geometry, lower-bound, and attainment conditions.

Logical inferences from those facts:

- C1 gives only \(P\subseteq Adm\).
- C2+C3 give equality of value supports, not multiset/index equality.
- Set membership and minima survive duplicate collapse.
- The standalone predicate admits vacuous and fabricated models.
- No `t̃>0` divisor is forced into the analytic ledger.

I did not rely on or independently rerun the 847-instance batteries or the stated 17-of-19 computation; the conclusions above follow from the definitions and the explicit \(M=(2,2,2)\) models.
# Thread 04 reproduction check - blow-up certificate

Checker: `Copernicus` (xhigh).
Scope: Aoyagi 2023 PDF pp. 14-23 and
`threads/04-blow-up-certificate/reproduction-draft.md`.
Worktree verified:
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`.
Files edited by checker: none.

## Verdict

The A4 blow-up draft is not reproduction-checked and is not formalisation-ready.
The main blocker is a source-fidelity error in the width bookkeeping. After that
is fixed, chart coverage and regularity/divisibility remain load-bearing gaps.

## Findings

1. **Critical source-fidelity mismatch.** The draft collapses Aoyagi's actual
   layer width `M^{(S+1)}` into the prefix minimum `m[S+1]`. Aoyagi's `D_J`
   has columns `J+1..M^{(S+1)}`, while only the transition test uses
   `M(S+1) = min(M(S), M^{(S+1)})`. The draft uses `m[S+1]` for `D_J` columns
   and exponent increments, undercounting whenever
   `M^{(S+1)} > M(S+1)`.
2. **Wrong transition updates.** Case 1(1), Case 1(2), and Case 2 Jacobian
   numerator updates should use `M^{(S+1)} - J`, not `m[S+1] - J`. Case 2's
   earlier coordinates should use actual widths `M^{(i+1)}`, not prefix
   minima.
3. **Missing charts.** Aoyagi displays the `u_{s,k}` chart and the single pivot
   chart with pivot `d_{J+1,J+1}`. A full blow-up cover also has all other
   `d_{ij}` pivot charts in Case 1 and Case 2. The draft flags this as a risk
   but does not resolve it.
4. **Invariant gaps.** The draft says "apply `Q/P`" but does not reproduce the
   actual coordinate updates `C'_J = Q^{-1} C_J`, the exact transformed
   residual block, or the recurrence proof for the new `b_i`. This is
   especially serious because Aoyagi's displayed Case 1(2) algebra has a
   bookkeeping ambiguity: page 17 defines `b'_i = u b_i`, while page 18 also
   factors out a standalone `u` before `diag(b'_i)`.
5. **Termination issue.** The proposed lexicographic measure is only a
   candidate. Case 1(1) decreases the count at the current jump, but if that
   count becomes zero the next jump changes, so the third component is not a
   stable lexicographic component as written. A formal certificate needs a finite
   multiset/list measure over active `tmin` values or an equivalent branchwise
   proof.
6. **Regularity/divisibility issue.** Aoyagi calls `P` regular, but `P`
   contains quotients `b'_i / b'_{J+1}`. The draft flags this but does not prove
   divisibility from the `b_i` recurrence and gap hypotheses. This is required
   before Lean can treat `P` as a regular coordinate operation.
7. **Boundary cases not checked.** The draft does not explicitly handle `J=0`,
   `J+1=M(S+1)`, rectangular cases `M(S)<M^{(S+1)}` versus
   `M(S)>M^{(S+1)}`, `S=L`, or the advance to `S=L+1`. These are exactly where
   the actual-width/prefix-minimum distinction matters.

## Required repairs before Lean

- Separate actual layer widths from prefix/effective minima throughout the
  certificate.
- Reproduce the displayed Case 1(1), Case 1(2), and Case 2 coordinate formulas
  with the corrected width indices.
- Prove chart coverage or explicitly restrict the certificate to source charts
  that cover the local ideal under named symmetry/permutation hypotheses.
- Prove regularity/divisibility for the `P` matrices.
- Replace the candidate termination measure by a branchwise or finite-list
  measure that survives jump changes.

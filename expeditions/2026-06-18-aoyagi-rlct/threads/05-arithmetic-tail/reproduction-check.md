# Thread 05 reproduction check - arithmetic tail

Checker: `Planck` (xhigh).
Scope: Aoyagi 2023 PDF pp. 22-27 and
`threads/05-arithmetic-tail/reproduction-draft.md`.
Worktree verified:
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`.
Files edited by checker: none.

## Verdict

The A5 arithmetic draft is not reproduction-checked and is not
formalisation-ready. The quadratic algebra and interior Lemma 3 calculation are
mostly reproducible, but the boundary cases, the `\tilde t_{s,k}=0` restriction,
feasibility of minimisers, and Lemma 5 order-count construction remain open.

## Findings

1. **High: Lemma 5 is not independently reproduced.** The draft says Aoyagi gets
   equality by the displayed `T_{s,k}` families on pp. 26-27, especially using
   Case 1(2). Aoyagi's proof is much thinner: it gives an upper bound, lists
   cases (1)-(5), then says the blow-up process is constructed with `T_{s,k}`
   in Eqs. (3) and (4) in Case 1(2). The draft does not verify admissibility,
   coverage, empty ranges, the exclusion
   `(s,k) != (S_2-1, Htilde'_1+1)`, or why those charts force exactly
   `a(ell-a)+1` equal-minimum variables.
2. **High: the candidate minimum drops Aoyagi's `\tilde t_{s,k}=0`
   restriction.** Aoyagi p. 22 says candidates are
   `1/2 min{M_{s,k}, \tilde t_{s,k}=0}`. The draft writes
   `2 lambda_O = min M_{s,k}` without that qualifier. This is a
   source-fidelity mismatch unless separately proved that the unrestricted
   minimum is attained among terminal variables with `\tilde t=0`.
3. **High: Lemma 3 has unresolved boundary defects.** Aoyagi Lemma 3 assumes
   `0 <= a,b <= ell-1`, but Definition 3 gives `a in {1,...,ell}` from
   `M-1 < B/ell <= M`. Thus `a=ell` is possible, while `a=0` is not produced by
   Definition 3. A checked formal statement must split endpoints: `a=ell` has
   only minimizer `b=ell-1`; conventional `a=0` has only minimizer `b=0`; and
   the identity `A(a-1)=A(a)` must not be used at either endpoint.
4. **Medium: feasibility constraints on the `F_j` minimisers are not proved.**
   Aoyagi p. 23 records inequalities such as `F_j - M^(S_{j+1}) >= 0`,
   partial-sum inequalities, and the final `F_ell` inequality. The draft moves
   from the quadratic form to floor/ceil integer minimisers but does not prove
   those minimising `F` patterns are feasible exponent chains or arise from
   actual `T_{s,k}`.
5. **Medium: `F_1`/`H_0` convention is hidden.** The draft defines `F_1`
   separately, but Lemma 4 later writes all `F_j` as
   `H_(j-1)-H_j+M^(S_(j+1))`. For `j=1`, this needs an explicit convention like
   `H_0 = M^(S_1)`, matching Aoyagi's compressed notation.
6. **Medium: Definition 3 must be formalised as indexed/multiset data, not a
   value set.** Aoyagi uses set braces, but the equal-width example on p. 9
   forces indexed selection. Equal residual widths and duplicated selected
   values need explicit hypotheses.
7. **Medium: analytic extraction is suppressed.** The arithmetic draft uses
   `lambda_O` and `theta`, but pp. 22-27 rely on the earlier
   normal-crossing/RLCT extraction and on the blow-up recursion covering local
   coordinates. For Lean, A5 should be an arithmetic theorem conditional on
   A4/A0-style hypotheses, not a standalone RLCT theorem.

## Required repairs before Lean

- Restate Lemma 3 with endpoint cases and prove them separately.
- Keep the `\tilde t_{s,k}=0` terminal-variable restriction in the candidate
  set or prove an explicit equivalence with the unrestricted minimum.
- Prove feasibility of the floor/ceil minimisers as Aoyagi exponent chains.
- Reproduce Lemma 5's chart-family construction rather than summarising it.
- Treat Definition 3 as ordered/indexed selection data so duplicates are not
  lost.

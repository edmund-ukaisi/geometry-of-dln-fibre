# threads.md - thread index (aoyagi-rlct)

`NN-slug` - type - status - subject. Status in `open` / `in-progress` /
`blocked` / `review-pending` / `closed` / `abandoned`.

## Planned threads

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-source-inventory | explore | closed | xhigh scout `Aquinas` returned. Source inventory saved; ledger already aligned with key correction that final target is Theorem 2. |
| 02-analytic-interface | explore/formalisation | closed | Interface draft saved; A2 repair decision keeps A0 extraction-only, excludes Lemma 1/additivity as separate citations, and routes regular variables through full certificate arithmetic. Reopen only after A4 supplies actual normal-crossing certificate data. |
| 03-block-product-reduction | formalisation | in-progress | A1 algebraic block identities and rank formula landed; A2 chart-local induction-step, entry-ideal transport, through-subspace, paper-order chain bookkeeping, fixed-base variable charts, deterministic suffix-state algebra, recursive-`Bprev` topology, endpoint block-diagonal neighborhood handoff, residual-rank implications, source-facing elementary boundary certificates, and Aoyagi-style triangular endpoint multiplier wrappers landed; full printed product-reduction theorem still needs source-hypothesis/rank-stratum handling, and post-Theorem-3 RLCT transport remains separate. |
| 04-blow-up-certificate | pen-and-paper/formalisation | blocked | A4 repair pass separates actual widths from prefix minima and image-checks the Case 2/terminal formulas. The printed Case 2 vector currently disagrees with the printed numerator increment unless `M(S)=M^{(S)}`; corrected Case 2 new-label certificate, finite exponent-domain bookkeeping, Case 2 residual-block entry set, selected-entry substitution scaffold, arbitrary selected-entry finite-center facts, displayed Case 2 finite frontier branch bookkeeping, displayed source-chart frontier implication packages, Case 1 center generators, Case 1 row-strip containment, Case 1 first-jump selected-label hypotheses, Case 1 tail-lowering exponent increment, one-label lower-tail certificate transformer, conditional same-domain Case 1 lower-tail package update, selected-label update-data helpers, and conditional level/tail bridge are Lean-packaged narrowly; pivot-chart coverage, full vector invariant, `b'_i` bookkeeping, transition proofs, termination, and boundary cases remain open. |
| 05-arithmetic-tail | formalisation/source-audit | blocked | Lemma 3/4 arithmetic and supplied Lemma 5 finite-count wrappers are Lean-proved through terminal exactness and terminal source endpoint payload packages. Source-backed Lemma 5 remains blocked: printed lower-bound equations have Lemma 4 witness obstructions, terminal branch/source-realisation remains supplied, and the upper-bound/no-extra paragraph still needs source-backed classifier, injection, and back-to-label data before it can discharge `terminalMinimumLabels subset branchLabelImage`. |
| 06-dln-translation | formalisation | pending | Translate Aoyagi dimension/rank notation to repo DLN notation without quiver inputs. |
| 07-review-hardener | review/hardener | pending | Fidelity, precision, source, and bedrock pass over broad theorems and final assembly. |
| 08-reproduction-checks | pen-and-paper/review | pending | Standing gate. Completed first block/product (`Ramanujan`), blow-up (`Copernicus`), and arithmetic-tail (`Planck`) checks, but every new substantial source calculation still needs its own reproduction artifact and independent checker verdict before formalisation. |

## Execution notes

- Run expedition work from
  `/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`,
  not from the main checkout.
- At thread start, run or reason from `git rev-parse --show-toplevel`; it must
  be the Aoyagi worktree path above. If not, stop before reading or editing.
- Subagent prompts must name the absolute Aoyagi worktree path and tell the
  teammate to work only there.
- Every Lean teammate must read `lean/CLAUDE.md` before editing.
- Worktree isolation is preferred, but verify it with `git worktree list`.
- Controller is sole merger and single writer for `lean/DLNFibre.lean`.
- Each thread writes durable progress to its own `thread.md`; controller mirrors
  cross-thread state in `synthesis.md`, `priorities.md`, `claims.md`, and
  `theorem-ledger.md`.
- Source fidelity means Aoyagi's PDF only. The quiver paper and its Lean branch
  are not evidence for this expedition.
- A substantial calculation cannot move to formalisation-ready until it has a
  pen-and-paper reproduction artifact and a separate checker verdict.

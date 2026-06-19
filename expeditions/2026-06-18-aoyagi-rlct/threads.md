# threads.md - thread index (aoyagi-rlct)

`NN-slug` - type - status - subject. Status in `open` / `in-progress` /
`blocked` / `review-pending` / `closed` / `abandoned`.

## Planned threads

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-source-inventory | explore | closed | xhigh scout `Aquinas` returned. Source inventory saved; ledger already aligned with key correction that final target is Theorem 2. |
| 02-analytic-interface | explore/formalisation | in-progress | Interface draft saved; A2 repair decision keeps A0 extraction-only, excludes Lemma 1/additivity as separate citations, and routes regular variables through full certificate arithmetic. |
| 03-block-product-reduction | formalisation | in-progress | A1 algebraic block identities and rank formula landed; A2 chart-local induction-step, entry-ideal transport, through-subspace, paper-order chain bookkeeping, fixed-base variable charts, deterministic suffix-state algebra, recursive-`Bprev` topology, endpoint block-diagonal neighborhood handoff, residual-rank implications, and source-facing elementary boundary certificates landed; full printed triangular product-reduction theorem still needs source-hypothesis/rank-stratum handling, and post-Theorem-3 RLCT transport remains separate. |
| 04-blow-up-certificate | pen-and-paper/formalisation | blocked | A4 repair pass separates actual widths from prefix minima and image-checks the Case 2/terminal formulas. The printed Case 2 vector currently disagrees with the printed numerator increment unless `M(S)=M^{(S)}`; corrected Case 2 new-label certificate, finite exponent-domain bookkeeping, Case 2 residual-block entry set, selected-entry substitution scaffold, Case 1 center generators, Case 1 row-strip containment, Case 1 tail-lowering exponent increment, and one-label lower-tail certificate transformer are Lean-packaged narrowly; pivot-chart coverage, full vector invariant, `b'_i` bookkeeping, transition proofs, termination, and boundary cases remain open. |
| 05-arithmetic-tail | formalisation | blocked | xhigh scout `Raman` returned and checker `Planck` reviewed. Interior quadratic algebra mostly reproducible, but Lemma 3 endpoints, `tilde t=0`, feasibility, and Lemma 5 count are unresolved. |
| 06-dln-translation | formalisation | pending | Translate Aoyagi dimension/rank notation to repo DLN notation without quiver inputs. |
| 07-review-hardener | review/hardener | pending | Fidelity, precision, source, and bedrock pass over broad theorems and final assembly. |
| 08-reproduction-checks | pen-and-paper/review | closed | Standing gate for first reproduction round. Completed block/product (`Ramanujan`), blow-up (`Copernicus`), and arithmetic-tail (`Planck`) checks; all broad claims still need repair before formalisation except the narrow A1 algebraic chart identity. |

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

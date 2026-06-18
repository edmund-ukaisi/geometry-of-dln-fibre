# threads.md - thread index (aoyagi-rlct)

`NN-slug` - type - status - subject. Status in `open` / `in-progress` /
`blocked` / `review-pending` / `closed` / `abandoned`.

## Planned threads

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-source-inventory | explore | in-progress | xhigh scout `Aquinas`: PDF theorem/definition inventory; fill `theorem-ledger.md` and initial claim cards. Controller source map started. |
| 02-analytic-interface | explore/formalisation | closed | xhigh scout `Boole` returned. Normal-crossing interface mapped; Theorem 4 flagged as analytic/scope conflict unless avoided/proved restricted. |
| 03-block-product-reduction | formalisation | blocked | xhigh scout `Galileo` returned and checker `Ramanujan` reviewed. A1 algebraic chart identities partially pass; A2 not formalisation-ready as stated. Needs source-faithful hypotheses and analytic-boundary decision. |
| 04-blow-up-certificate | pen-and-paper/formalisation | review-pending | xhigh scout `Ptolemy` returned. Draft certificate reproduction landed; independent check pending before Lean. |
| 05-arithmetic-tail | formalisation | review-pending | xhigh scout `Raman` returned. Draft reproduction landed; independent check pending before Lean. |
| 06-dln-translation | formalisation | pending | Translate Aoyagi dimension/rank notation to repo DLN notation without quiver inputs. |
| 07-review-hardener | review/hardener | pending | Fidelity, precision, source, and bedrock pass over broad theorems and final assembly. |
| 08-reproduction-checks | pen-and-paper/review | in-progress | Standing gate. Completed block/product check (`Ramanujan`); arithmetic-tail checker `Planck` and blow-up checker `Copernicus` running. |

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

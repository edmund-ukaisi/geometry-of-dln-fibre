# priorities.md - taste ledger (aoyagi-rlct)

The controller proposes this ranking; the operator may edit this file directly.

## Operator standing choice

- The general normal-crossing-to-RLCT extraction theorem is Cited.
- Other Aoyagi-specific steps default to Prove. Do not mark them Cited or
  Deferred without a probe.
- This is an Aoyagi-only expedition. Do not use the quiver paper, quiver Lean
  results, or quiver notation as source evidence or proof input.

## Active workspace

Work from
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`
on branch `expedition/aoyagi-rlct`. If a resumed controller finds itself in the
main checkout, it should move to this worktree before doing expedition work.
Use absolute paths or explicit `workdir` settings for tool calls; do not rely
on the session's original cwd.

## Ranked next

1. Source inventory. Fill `theorem-ledger.md` from the PDF with source page,
   exact statement, hypotheses, dependency edges, and candidate Lean target.
   This blocks reliable formalisation.
2. Reproduction discipline. For each substantial source cluster, assign a
   pen-and-paper reproduction before Lean work depends on it, then assign a
   separate checker. Record both statuses in `claims.md` and
   `theorem-ledger.md`.
3. Analytic interface shape. Define the cited normal-crossing extraction
   interface precisely enough that later theorem names cannot overclaim.
4. Lean module placement probe. Decide between `DLNFibre.DLN.Aoyagi.*` and a
   flatter `DLNFibre.DLN.*` layout after reading the first source inventory.
   Keep `DLNFibre.lean` single-writer.
5. Block/product reductions. Start with the elementary matrix algebra before the
   blow-up recursion; it will expose the needed coordinate objects. Do not start
   the Lean tide until the block/product reproduction has been checked.
6. Blow-up transition design. Convert Aoyagi's recursive proof to a formal
   certificate early, before polishing later arithmetic. This needs the
   strongest reproduction/checking gate in the expedition.
7. Arithmetic tail. Formalise the minimisation and order count once exponent
   vectors have a stable representation and the arithmetic reproduction is
   checked.
8. Review/hardener cadence. Gate every broad theorem name, every universal
   case-split/exhaustiveness claim, and the final theorem.

## Parked but live

- Whether Aoyagi's deepest-singular-point theorem is needed as a source result
  or can be reproved in the homogeneous/square-Frobenius setting. Default:
  probe and prove if elementary.
- Whether the source PDF text extraction is reliable enough to serve as line
  references. If not, use page references and quote only short labels.
- Whether a small certified script is useful for the blow-up transition system.
  If useful, build it under the expedition and make Lean the final authority.

## Worktree caution

The repository was inspected while the checkout was on
`expedition/core-quiver-engine` with unrelated dirty/untracked work. The Aoyagi
worktree now exists separately. Use surgical staging inside the Aoyagi worktree;
do not use `git add -A` from the main checkout while unrelated expedition
artifacts are present.

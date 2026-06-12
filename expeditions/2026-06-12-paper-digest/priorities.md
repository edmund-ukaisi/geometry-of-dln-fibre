# priorities.md — the taste ledger (paper-digest)

The ranked decision queue. The controller proposes a ranking by value-of-information and directed
suspicion; **the operator edits this file directly** (highest-authority signal). Nothing unranked;
"unclear-but-keep-going" is first-class.

## Ranked (controller's opening proposal — operator to edit)

1. **[VOI: highest] Map Mathlib's quiver-representation coverage.** Does Mathlib have quiver reps, the
   type-A / `A_n` indecomposables, Gabriel, `Ext` for representations? This gates how much of Bundle 2 is
   reuse vs build-from-scratch and therefore the whole programme's shape. → spawn a `scout` (Mathlib recon).
2. **[VOI: high] Verify the digest against the paper, section by section.** Confirm theorem numbers,
   statements, and the rank-closure convention (the overview's footnote flags a possible sign flip in the
   source's defining display). Address the open scholium note (DLN motivation + Aoyagi citation up front).
3. **[VOI: high] Size the combinatorial core (Bundle 1).** Rank patterns ↔ Kostant partitions (Prop 3.1),
   the QIP (Thm 6.1), the lattice-point formula (Thm 7.10): write the precise statements at formalisation
   grain and judge reachability. Likely the first formalisation target.
4. **[VOI: medium] Pin the `Rep_d` / `mult` / rank-loci Lean definitions.** A green `DLNFibre.Core` object
   skeleton — the ambient objects only — is a low-risk bonus that de-risks Bundle 1.
5. **[parked, unclear] The topology (Bundle 3).** Is permutation invariance reachable by an independent
   combinatorial route, or is the equivariant-cohomology layer a cited wall? Park until Bundle 1 is mapped.

## Notes
- Keep `synthesis.md` current each tick (recovery substrate).
- In-repo memory only; never `~/.claude` (CLAUDE.md § Memory).

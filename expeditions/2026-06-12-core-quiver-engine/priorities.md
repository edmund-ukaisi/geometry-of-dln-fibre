# priorities.md — the taste ledger (core-quiver-engine)

The ranked decision queue. The controller proposes a ranking by value-of-information and directed
suspicion; **the operator edits this file directly** (highest-authority signal). Nothing unranked;
"unclear-but-keep-going" is first-class.

## Ranked (controller's opening proposal — operator to edit)

1. **[VOI: highest] Mathlib quiver-representation recon.** Does Mathlib have quiver reps, the type-A / $A_n$
   indecomposables, Gabriel, `Ext` of representations? Gates build-vs-reuse for rung 4 and the whole engine.
   → spawn a `scout` (read-only Mathlib recon + `scripts/lean-search`); record the map in `synthesis.md`.
2. **[reachable now] Ambient objects (rung 1).** Pin `Rep_d`, `mult`, product-rank loci as `DLNFibre.Core`
   defs; green build. Low-risk; de-risks everything downstream. → `formaliser`.
3. **[reachable, first real theorem] Prop 3.1 correspondence (rungs 2–3).** Rank patterns + Kostant
   partitions as data, and the inclusion-exclusion bijection as a characterisation. Pure combinatorics /
   linear algebra. → `formaliser`; statement-card + reviewer fidelity audit at AUDIT.
4. **[depends on #1] Orbits ↔ Kostant (rung 4, Gabriel).** The representation-theoretic identification;
   possibly build-from-scratch. Open only when #1 says whether it is whole-in-reach.
5. **[parked, next expedition] `Ext` codimension (Cor 3.5).** Out of scope here; named successor.

## Notes
- Read `../../lean/CLAUDE.md` before any Lean (Core never imports DLN).
- Keep `synthesis.md` current each tick (recovery substrate).
- In-repo memory only; never `~/.claude` (CLAUDE.md § Memory).
- Reader-facing paper digestion is the operator's activity — not a thread here.

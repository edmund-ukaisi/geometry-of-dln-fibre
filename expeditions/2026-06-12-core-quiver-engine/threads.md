# threads.md — thread index (core-quiver-engine)

The durable thread-status ledger. `NN-slug` · type · status · one-line subject.
Status ∈ `open` / `in-progress` / `blocked` / `review-pending` / `closed` / `abandoned`.

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-mathlib-recon | explore | closed | Mathlib coverage: rungs 1–3 = basic Mathlib; rung 4 (Gabriel/interval modules/Kostant) = build-from-scratch; `Ext` reusable. |
| 02-ambient-objects | formalisation | review-pending | `DLNFibre.Core.Setup`: `Tuple`/`mult`/`Σ^r`/`Σ^{≤r}`/`fibre` (rung 1). Green, axiom-clean, witnessed. Fidelity audit batched with 03. |
| 03-prop31-inversion | formalisation | in-progress | Prop 3.1a: the abstract rank-pattern ↔ Kostant-multiplicity inclusion-exclusion bijection (rungs 2–3). |

Planned:
| 04-review-core | review | pending | Decorrelated fidelity audit of Setup (defs) + Prop 3.1 (theorem), once 03 lands. |
| 05-rung4-orbits-kostant | formalisation | pending | Orbits ↔ Kostant via type-A Gabriel — its own sub-build; open only when whole-in-reach. |

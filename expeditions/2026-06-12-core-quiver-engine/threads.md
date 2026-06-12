# threads.md — thread index (core-quiver-engine)

The durable thread-status ledger. `NN-slug` · type · status · one-line subject.
Status ∈ `open` / `in-progress` / `blocked` / `review-pending` / `closed` / `abandoned`.

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-mathlib-recon | explore | closed | Mathlib coverage: rungs 1–3 = basic Mathlib; rung 4 (Gabriel/interval modules/Kostant) = build-from-scratch; `Ext` reusable. |
| 02-ambient-objects | formalisation | review-pending | `DLNFibre.Core.Setup`: `Tuple`/`mult`/`Σ^r`/`Σ^{≤r}`/`fibre` (rung 1). Green, axiom-clean, witnessed. |
| 03-prop31-inversion | formalisation | review-pending | `DLNFibre.Core.RankPattern`: Prop 3.1a abstract inclusion-exclusion inversion (`diff_cumul`/`cumul_diff`/`rankPatternEquiv`). Green, axiom-clean, witnessed. |
| 04-review-core | review | in-progress | Decorrelated fidelity + precision audit of Setup + RankPattern (incl. the `rankPatternEquiv` naming question). |
| 05-rung4-orbits-kostant | formalisation | pending | Orbits ↔ Kostant via type-A Gabriel — its own build-from-scratch sub-build; open only when whole-in-reach. |
| 06-submult-rankpattern | formalisation | pending | Matrix-side `submult`/`rankPattern` (deferred from 03 — variable-lower-bound cast; shifted-tail or List.prod route). |

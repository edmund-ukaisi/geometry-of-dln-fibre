# threads.md — thread index (core-quiver-engine)

The durable thread-status ledger. `NN-slug` · type · status · one-line subject.
Status ∈ `open` / `in-progress` / `blocked` / `review-pending` / `closed` / `abandoned`.

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-mathlib-recon | explore | closed | Mathlib coverage: rungs 1–3 = basic Mathlib; rung 4 (Gabriel/interval modules/Kostant) = build-from-scratch; `Ext` reusable. |
| 02-ambient-objects | formalisation | closed | `DLNFibre.Core.Setup`: `Tuple`/`mult`/`Σ^r`/`Σ^{≤r}`/`fibre` (rung 1). Green, axiom-clean, witnessed, **reviewed** (thread 04). |
| 03-prop31-inversion | formalisation | closed | `DLNFibre.Core.RankPattern`: Prop 3.1a inversion (`diff_cumul`/`cumul_diff`/`cumulDiffEquiv`). Green, axiom-clean, witnessed, **reviewed** (thread 04). |
| 04-core-audit | review | closed | Decorrelated audit: both modules SURVIVED on the math; two precision findings (`rankPatternEquiv`→`cumulDiffEquiv` rename; stale box docstring) fixed + re-gated. |
| 05-rung4-orbits-kostant | formalisation | pending | Orbits ↔ Kostant via type-A Gabriel — build-from-scratch sub-build; **strategic call pending** (full-build vs cite-Gabriel). Open only when whole-in-reach. |
| 06-submult-rankpattern | formalisation | pending | Matrix-side `submult`/`rankPattern` (deferred from 03 — variable-lower-bound cast; shifted-tail or List.prod route). Unblocks Prop 3.1b. |

# threads.md — thread index (core-quiver-engine)

`NN-slug` · type · status · subject. Status ∈ open / in-progress / blocked / review-pending / closed / abandoned.

## Rungs 1–3 (closed, reviewed bedrock)

| Thread | Type | Status | Subject |
|---|---|---|---|
| 01-mathlib-recon | explore | closed | Coverage map; rung 4 = build-from-scratch. |
| 02-ambient-objects | formalisation | closed | `Core.Setup` (rung 1). Reviewed. |
| 03-prop31-inversion | formalisation | closed | `Core.RankPattern`: Prop 3.1a inversion (`cumulDiffEquiv`). Reviewed. |
| 04-core-audit | review | closed | Decorrelated audit; SURVIVED; precision fixes applied. |

## Rung 4 — type-A Gabriel decomposition (FULL BUILD); ladder refined by the 07 design

| Thread | Type | Status | Subject |
|---|---|---|---|
| 06-submult-rankpattern | formalisation | review-pending | **4a:** `Core.Submult` — `submult`, step/bridge (`mult_eq_submult`), `rankPattern`, `r_{ii}=d_i`. Green, axiom-clean, controller-checked; reviewer audit batched into the rung-4 review. |
| 07-gabriel-design | pen-and-paper | closed | Proof design: peel-one-interval-per-step normal form; **general Krull–Schmidt / all-Dynkin Gabriel NOT needed**; uniqueness free via `diff_cumul`. Refined ladder below. (`findings.md`, sympy-certified.) |
| 08-interval-modules | formalisation | open (next) | **4b (cheapest first):** `M_{ij}` as `Tuple`s; direct sum (block-diagonal); `rankPattern(⊕ M_{ij}^{m}) = cumul m` (ties 4a↔Prop 3.1a). Exercises `submult`. |
| 09-iso-invariance | formalisation | open | **4c (parallel to 4b):** `G_d=∏GL` action `(g·A)_i = P_i A_i P_{i-1}⁻¹`; `submult(g·A) i j = P_j (submult A i j) P_i⁻¹` ⟹ rank pattern base-change invariant. |
| 10-normalform-gabriel | formalisation | open | **4d (CRUX):** every rep ≅ `⊕ M_{ij}^{m}` via the peel (total-dim induction; the splitting fact `f v = w ≠ 0, W=k·w⊕U ⟹ V=k·v⊕f⁻¹U`; backward `comap` complement chain). Prove on an abstract `LinearMap` chain, transport to `Tuple`. |
| 11-orbits-kostant | formalisation | open | **4e (≈free):** orbits = iso classes (Thm 2.4, true by construction) + 4c + 4d + `diff_cumul` ⟹ orbits ↔ Kostant (Cor 2.9) = `cumulDiffEquiv` restricted. |

Design notes (thread 07): prove 4d on an **abstract finite-dim `LinearMap` chain** (mature ker/range/`comap`
API), transport to `Tuple` via one change-of-basis per vertex. **Cite** (don't reprove): `Submodule.exists_isCompl`,
`IsCompl` finrank additivity, `rank(P·C·Q)` unit-invariance. Hardest step: the indexed backward-preimage
complement chain + threading `IsCompl` down the chain (active/dead-edge `Fin` bookkeeping).

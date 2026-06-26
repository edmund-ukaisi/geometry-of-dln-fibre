# Statement card — R1 hfin (upper bound): OBSTRUCTION from the combinatorial atlas; reachable only via the full recursive coupled resolution

**Status:** DESIGN adjudication (no Lean). Verdict: hfin is NOT dischargeable from the combinatorial
`routeLayerAtlas` alone; reachable from scratch (S2-only) only via the FULL recursive coupled
resolution cover — corank-sensitive, the genuine R1 long pole. Date 2026-06-24, seat `pen-and-paper`.
Thread `threads/27-r1-hfin-completeness/`.

## The atom
`hfin` (`routeMLayerCover_of_atoms`, `RouteMLayerCover.lean:180`): `∀ c', (leaf-sum < ⊤) →
∫_{routeMBaseNbhd} |routeMCore M|^{−c'} < ⊤` — the upper bound `rlctAtOn ≥ ½·minAdm`. S2-only (the
cited Aoyagi/Watanabe `rlct ≥ ½·codim` is FORBIDDEN).

## Verdict (named for what it is)
- The `routeLayerAtlas` is a COMBINATORIAL leaf family `(ι, d, k, h)` — `IsResolutionAtlas` carries
  only the two NUMERICAL fields `threshold_ge` / `achiever`, **no charts, no cover**. Each leaf is a
  SINGLE divisor `foldDivisors[Mval(M,T)]` (`d=1`). The hfin hypothesis correctly extracts
  `c' < ½·minAdm`; the conclusion is a GEOMETRIC finiteness the leaf data cannot supply.
- **OBSTRUCTION** (exact + decorrelated Codex): the per-chart UPPER c-o-v needs `F∘φ ≥ c₀·(monomial)²`
  (unit bounded BELOW on the whole chart — a normal-crossing presentation), the OPPOSITE of hdiv. The
  #135 `φ_M` chart's unit `Uval334` VANISHES on a positive-dim sublocus `{a=0,c=0,Δ=0}` in-chart (the
  deeper corank stratum); `φ_M` resolves the TOP stratum, not the sub-stratum. The corank-≥2 binding
  core `‖Δ·S‖²` is reducible + non-quasi-homogeneous (multi-facet Newton polyhedron) → NOT single-
  divisor → needs the coupled `diag(b)` resolution.
- **REACHABLE from scratch** (NOT a headline wall) via a genuine `recStep`-style RECURSIVE cover of
  `routeMBaseNbhd` (the (2,2,2) template `Case222CoverGETail.myF222_threshold_lt_top'` is exactly this —
  4 pivot cells, NOT the single-divisor leaf), with per-cell charts = #135 `φ_M` (top stratum) + coupled
  `diag(b)` sub-charts (recursion into `{V=0}`) for the corank-≥2 cells, + a per-cell upper c-o-v.

## Characterised class
- **Smooth (corank-≤1) cover suffices** iff every admissible path has all per-step coranks ≤ 1 — only
  near-trivial `M` (e.g. `(2,1,2)`).
- **Needs the coupled resolution** for ANY `M` with a corank-≥2 drop on some path — almost all `M` with
  a width ≥ 3 (incl. all corank-2 binding cases). NB: a corank-≥2 NON-achiever stratum doesn't alone
  defeat hfin (its rate is favourable off the minimiser, as (2,2,2)'s done cover shows) — the load-
  bearing hard cell is the corank-≥2 BINDING one.

## Verified (exact, sympy) + corroboration
- leaf = single divisor `foldDivisors[Mval]`, `d=1`, model finite iff `c'<½·minAdm` (`leaf_data.py`).
- `φ_M` unit `Uval334` vanishes on `{a=0,c=0,Δ=0}` positive-dim in-chart (`hfin_V_vanishing.py`).
- `‖Δ·S‖²` reducible + non-quasi-homogeneous, multi-facet Newton (`hfin_obstruction_exact.py`).
- per-path corank classification (`hfin_all_strata.py`); the (2,2,2) Lean hfin is recursive `recStep`.
- Decorrelated Codex (xhigh): OBSTRUCTION on corank-2; per-chart bound needs real charts +
  `F∘φ ≥ c·monomial²`; upgrade to coupled `diag(b)` charts to close from scratch.

## Levels / what would change it
Upper leg only (`cover_le`). hdiv (lower) is closed (#135 `φ_M`). VALUE proven (`routeLayerAtlas_value`).
What makes hfin easier: a recursive per-cell DIRECT finiteness (à la `myF222_threshold_lt_top'`) may
avoid a global atlas — but the corank-≥2 cell still needs its coupled resolution. The forbidden cite is
the only shortcut, so the recursive coupled cover is the from-scratch path. **Largest remaining R1 build.**

**Artefacts:** `thread.md`; `scripts/{leaf_data,hfin_V_vanishing,hfin_obstruction_exact,hfin_all_strata,hfin_class_boundary}.py`; `codex/hfin-{prompt,answer}.md`.

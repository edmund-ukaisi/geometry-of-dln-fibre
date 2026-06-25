# thread 10 — base pivot-chart presentation (G2-1, formalisation / tide — foundation of the build)

**Type:** formalisation (tide) · `OPENED → SPECIFY/DESIGN → CHECKPOINT(no-skip) → PROVE → AUDIT`.
The foundation of the determinantal-presentation build (operator: push until 4.6 closes). G2a located the
wall: the exact-rank coordinate rings are opaque `vanishingIdeal`-quotients with no explicit presentation,
so the Schur trivializing `AlgEquiv` can't be exhibited. This tide builds the first explicit handle: the
**pivot-chart Schur parametrization of the base** `Mat^{rk=r}`.

## Goal (a new `Core` module — e.g. `DLNFibre/Core/DeterminantalChart.lean`)
Over a field `k`, on the pivot chart `U = {M : Mat (Fin p) (Fin q) k | (top-left r×r block of M) ∈ GL_r}`
(here `p = d_N`, `q = d_0`), give the **explicit parametrization** of the exact-rank-`r` locus:

> `M` has rank exactly `r` and top-left r×r block `Δ` invertible
>   ⟺  `M = [[Δ, B12], [B21, B21·Δ⁻¹·B12]]`  for `Δ ∈ GL_r`, `B12 ∈ Mat_{r×(q−r)}`, `B21 ∈ Mat_{(p−r)×r}`.

i.e. on `U`, rank-`r` ⟺ the bottom-right block is the **Schur-forced** value `B21 Δ⁻¹ B12` (rank-`r` ⟺ Schur
complement `= 0`). This is a bijection `Mat^{rk=r} ∩ U ≅ GL_r × Mat_{r×(q−r)} × Mat_{(p−r)×r}`, of dimension
`r² + r(q−r) + r(p−r) = r(p+q−r) = δ`. Deliverables, in order of value:
1. **The block / Schur lemma**: a block matrix `[[Δ, B12],[B21, B22]]` with `Δ` invertible has rank `r`
   (`= size of Δ`) **iff** `B22 = B21 Δ⁻¹ B12` (Schur complement vanishes). (Mathlib has Schur-complement
   rank lemmas — `Matrix.rank_fromBlocks…` / `Matrix.fromBlocks_…`; search first.)
2. **The parametrization bijection** (or the explicit coordinate ring of `Mat^{rk=r} ∩ U`), establishing the
   chart is `GL_r × Mat × Mat` — the explicit presentation the Schur `AlgEquiv` (G2-3) will localize over.
3. (If reachable) the chart dimension `= δ`, cross-checking the thermometer.

## SPECIFY/DESIGN-first — checkpoint before grinding
The exact engine form matters (how to phrase "the pivot chart" + the parametrization so it feeds the
later localized `AlgEquiv`, and whether to work at the `Matrix`/variety level or the coordinate-ring
level). At the checkpoint, report: the chosen formulation, the Mathlib Schur-complement lemmas found, and
whether the parametrization is reachable this run. **Fire a decorrelated `local-codex-consult`**
(authenticated, xhigh) on the cleanest formulation of the chart presentation for feeding G2-3; save under
`threads/10-base-chart-presentation/codex/`. If a sub-step walls, report precisely (don't grind / don't sorry).

## Read first
- `Core/DeterminantalStratumDim.lean` (the thermometer — `dim Mat^{rk=r} = δ`, and how `productRankLocusLE
  ![p,q] r` relates to the determinantal variety; the N=1 specialisation).
- `Core/ChartFlatnessProbe.lean` + `Core/FlatTrivialProductProbe.lean` (the route pins: localized comorphism,
  the tensor Schur closer `R_t ≃ R_b ⊗ F_E`).
- `Core/MultComorphism.lean` (F1), `Core/Setup.lean` (`mult`, `productRankLocus`).
- Mathlib: `Matrix.rank`, Schur complement (`Matrix.fromBlocks`, `Matrix.rank_fromBlocks_…`,
  `Matrix.det_fromBlocks₁₁`), `Matrix.invertible`/`GeneralLinearGroup`.
- `lean/CLAUDE.md` (zero sorry/axiom/native_decide; `decide +kernel`; `↦`; name=content; bedrock).

## Build / rules
Build via `scripts/lb` (never bare `lake build`/`cache get`). **Core only — never import `DLNFibre.DLN`.**
Do NOT edit the aggregator — report the import line. Pre-stage uncertain Mathlib API (Schur/fromBlocks
rank lemmas) with `example` blocks. Confirm lemmas exist before building on them. Don't touch other
worktrees or any stash. In-repo memory only.

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on headlines = `[propext,
Classical.choice, Quot.sound]`. Witness: the `(2,2,2), r=1` chart (Δ a 1×1 invertible scalar).

## Scope
**Just G2-1** (the base pivot-chart presentation). G2-2..G2-5, G3, G4 are later tides. Report to `main`:
theorem names + signatures; green/sorries/axioms; module path + aggregator line; the Schur Mathlib lemmas
used; the decorrelated-Codex read; any v4.29 friction. Commit on `expedition/fibre-codimension` when green.

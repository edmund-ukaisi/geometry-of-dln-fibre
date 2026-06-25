# Thread 07 — W1 `detΔ` all-top avoidance certificate (pen-and-paper) — persisted by controller

## VERDICT: W1 is TRUE — globally, single canonical pivot; the math is ALREADY a landed Lean lemma

**Every top-dim minimal prime `p` of `sigmaIdeal d r` satisfies `detΔ ∉ p`** — the canonical deep
top-left `r×r` pivot minor `ΔPdeep d r` does not vanish identically on any top-dim component of `Σ̄^r`.
Stronger: holds for every corner-`r` Kostant partition's component (product rank exactly `r`).

**GLOBAL, not per-component:** a single fixed polynomial `detΔ` avoids all top components at once. Only the
*witness point* is per-component (a base change of the realizer to normal form `diag(I_r,0)`); the *pivot* is
fixed. ⟹ thread 08's W1 wiring is **one global localization at `detΔ`, no per-component chart**.

**ALREADY PROVED IN LEAN (the key result):** `Core.SourceNoDrop.chartDsig_not_mem_partitionIdeal`
(`SourceNoDrop.lean:66-99`) proves `ΔPdeep ∉ vanishingIdeal(orbitRankLocus(realizerD m))` for
**`hm : m ∈ kostantPartitions d r`** — *no minimisation hypothesis*. So W1's genuine math content is done;
thread 08 needs only the WIRING: quantify it over `topComponents` via the PROVED
`bijOn_partitionIdeal_topComponents` (each top component = `vanishingIdeal(Ō_{realizerD m})` for a minimising
partition `m ∈ kostantPartitions`; apply `chartDsig_not_mem_partitionIdeal` at each) + the localization-
survival lemma + the per-prime componentwise no-drop.

## Structural reason
`detΔ ∈ p` ⟺ `Ō_M ⊆ {detΔ=0}` ⟺ *every* point of the component has top-left `r×r` minor 0. But
`M = realizerD m` has product rank exactly `r` (`rank_mult_realizerD`, from corner `m(0,last)=r`); an
end-factor base change `P` (`FibreNormalForm.exists_baseChange_of_rank_eq`, needs `N≥1`) carries `mult M` to
`E = diag(I_r,0)`, `A = P•M ∈ Ō_M` (rank patterns base-change-invariant), and at `A` the top-left minor of
`mult A = E` is `det(I_r) = 1 ≠ 0`. So `detΔ ≢ 0` on the component. (`detΔ` at the realizer *point* may be 0;
only non-vanishing *somewhere* on the component is needed — the base change does the work.)

## Exact-algebra verification (Singular `minAssGTZ` over ℚ, SOURCE Σ̄^r side) — #BAD = 0 throughout
`(2,2,2)`r1, `(2,2,2,2)`r1, `(2,2,2,2,2)`r1, `(3,3,3)`r1/r2, `(3,3,3,3)`r2, `(4,4,4)`r3, `(2,2,3)`r1
(non-equidim; lower comp also avoids), `(2,2,3,2)`r1 (Codex adversarial, rectangular-pair `det(A_3A_2)`),
`(3,2,3)`/`(2,3,2)`/`(3,2,2)` (valley/peak/asymmetric). Every case: **#BAD=0** and **#lowrank_top=0** (no top
component sits at product-rank `<r`). θ-counts match `cTheta(d−r)` where comparable (setup cross-check).

Adversarial confirmations: `detΔ` CAN be 0 at a realizer point while `detΔ ∉ p` (`(3,3,3)`r2,
`A_1=diag(0,1,1)`) — avoidance is component-level not point-level; explicit per-component witness points
(`(2,2,2,2)`r1: `A_i=diag(1,0)`, others `=I` ⟹ `detΔ=1`). Decorrelated Codex (xhigh) concurred independently
(global single pivot, normal-form base change, rank-`<r` non-issue).

## Scope / kill-condition
Arbitrary `d`, `N≥1`, `r ≤ d 0`, `r ≤ d(last)`, infinite field (the Fact B hyps). `r=0`: `detΔ=1` (unit,
vacuous). The sharp dividing line (does NOT cross): a top component contained in `{rank P < r}` (so `diag(I_r,0)`
outside its closure, all `r×r` minors vanish) — ruled out (`#lowrank_top=0`; top components are corner-`r`
generic-rank-`r` realizer closures).

## Remaining (formal, for thread 08 — NOT a math truth-value)
The per-prime componentwise no-drop `dim((A/comap P)_f) = dim(A/comap P)` (invoke
`AffineLocalizationNoDrop.ringKrullDim_localizationAway_eq_of_fg_domain` per surviving prime, not the global
no-drop). A wiring task.

## Artifacts
`threads/07-dsig-avoidance/scripts/` (`.sing` + `adversarial.py`, `witness_points.py`; `Singular -q FILE < /dev/null`),
`.../codex/avoidance-{prompt,answer,stdout.log}`. Lean: `SourceNoDrop.lean:66-99`, `ThetaComponentCount.lean:152`
(`rank_mult_realizerD`), `DeepChartRing.lean:112` (`ΔPdeep`).

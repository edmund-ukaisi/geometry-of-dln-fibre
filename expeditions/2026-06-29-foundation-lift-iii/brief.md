# Brief — `foundation-lift-iii` expedition

## Central question

> **Package the reusable differential-algebra interface behind the orbit-dimension argument — the chain
> `generic differential rank → Jacobian/Kähler rank → trdeg bound → image dimension` — as a clean,
> Mathlib-grade, DLN-free library (Phase 1); then lift the orbit-dimension capstone that stands on it,
> de-coupled from the DLN `Tuple` encoding (Phase 2).**

The third **build-the-buildable** expedition, on `origin/dev` `5bb7adc2` (after #14 + FL-II #15/#16/#17).
Spec: `/tmp/next-foundational-expedition.md`. Same machine as FL-II — autonomous, per-phase stacked PRs,
decorrelated review on the crux rungs.

## Recalibration (operator-confirmed) — Phase 2 is the *squeeze*, not orbit–stabilizer

The repo does **not** compute orbit dimension via `dim 𝒪 = dim G − dim Stab` (no `Stab` anywhere). It pins it
by a two-sided **differential/transcendence squeeze**:

> `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank(range δ⁰) ≤ finrank(cotangent) = varietyDim`.

So the Phase-2 capstone is **"orbit dimension = differential rank at a smooth point = cotangent dimension,"
+ orbit-as-image irreducibility** — the deeper, reusable engine. `dim G − dim Stab` would be net-new math the
repo doesn't use (out of scope unless separately targeted).

## Two layered phases

### Phase 1 — the differential-algebra interface (`Core.RingTheory.Kaehler` + `Core.Dimension.Trdeg`)
**~70% already built and DLN-free** (recon). Mostly **re-home + consolidate + extract one missing
base-change-rank variant + name-hygiene** — FL-II-shaped, low-risk. Pieces already exist: generic
differential rank (`JacobianTrdeg`), the `trdeg ≤ diff-rank` crux **already proved** (char-0, isolated to the
perfect-field step), the Jacobian/Kähler bridge (FL-II P3 `CotangentJacobian`), 2 of 3 base-change-rank
variants (FL-II P2 `rank_map_eq_of_injective` + `MatrixKaehler.finrank_range_baseChange`), `dim = trdeg`
(#14). Stands alone regardless of Phase 2.

### Phase 2 — the orbit-dimension capstone (`Core.AlgebraicGeometry.Group.Orbit`) — PROBE-GATED
A genuine **~2400-line refactor**: de-`Tuple` the Maurer–Cartan / `cochain` deformation-complex machinery
(`OrbitDifferentialRank`, `OrbitTangentCotangent`, `OrbitSmooth`) onto an abstract affine-`G`-variety
interface (`R`, `μ*`, `δ⁰`), built on Phase 1. The type-A orbit-closure (Abeasis–Del Fra box-moves) **stays
DLN-specific**. **Rung-0 = a de-`Tuple` probe** (write the interface + restate one key lemma against it):
default is to **proceed** on a positive probe (operator-confirmed); halt + surface only if it reveals the
argument is irreducibly `Tuple`-shaped.

## The ladder

Per-phase rung ladder + Mathlib-coverage + crux flags in [`priorities.md`](priorities.md) (from the
coverage recon, which is the detailed brief).

## Execution (operator-confirmed)
Drive Phase 1 → Phase 2 to completion, **no pausing for merges**; one **PR per phase** (stacked branches
`fl3-p1` off `origin/dev`, `fl3-p2` off `fl3-p1`), async operator review. Default-drive Phase 2 on a positive
probe. Per rung: re-home/generalize, re-gate (boundary + crux per L5), decorrelated review on the crux. Cite
only the monument (Aoyagi `rlct = ½·codim`, untouched).

## Closing criteria
- The differential-algebra interface packaged Mathlib-grade (`Core.RingTheory.Kaehler` + `Core.Dimension.Trdeg`),
  the 3 base-change-rank variants visibly distinct, char/separability hypotheses explicit (name=content);
  green / sorry-free / axiom-clean; the `trdeg ≤ diff-rank` crux reviewed.
- The orbit-dimension capstone on the interface (squeeze form), de-`Tuple`'d, reviewed — OR, if the probe
  fails, the orbit dim stays DLN-local and Phase 1 ships alone (honestly recorded).
- DLN consumers tag to the libraries; DLN payoff axioms unchanged. 2 (or 1) per-phase PRs.

## Provenance
Coverage recon (scout, 2026-06-29) — the 2-phase ladder + the squeeze recalibration. Spec:
`/tmp/next-foundational-expedition.md`. Built on #14 + FL-II. **Blind** to `expedition/aoyagi-full`.

# priorities.md — the taste ledger (core-quiver-engine)

The ranked decision queue. The controller proposes; **the operator edits this file directly**.

## Done + reviewed (bedrock)
- ✅ Recon (01); ambient objects (02, rung 1); Prop 3.1a inversion (03, rungs 2–3); audit (04).

## Rung 4 — type-A Gabriel (operator chose FULL BUILD); opened
- ✅ **4a** (06): `Core.Submult` — `submult`/`rankPattern`/bridge. Green, axiom-clean, controller-checked.
- ✅ **Design** (07): peel-one-interval normal form; **no general Gabriel/Krull–Schmidt needed**;
  uniqueness free via `diff_cumul`; prove on abstract `LinearMap` chain, transport to `Tuple`.

## Ranked next (controller proposal — operator may edit)

1. **4b — interval modules + direct sums (thread 08).** `M_{ij}` as `Tuple`s, block-diagonal `⊕`, and
   `rankPattern(⊕ M_{ij}^{m}) = cumul m` (block-rank additivity) — ties 4a ↔ Prop 3.1a. Cheapest; exercises
   `submult`; do first. → `formaliser`.
2. **4c — base-change invariance (thread 09), parallel to 4b.** `G_d` action; `submult(g·A) i j =
   P_j (submult A i j) P_i⁻¹` ⟹ rank pattern invariant. Cite `rank(P·C·Q)` unit-invariance. → `formaliser`.
3. **4d — the normal-form CRUX (thread 10).** Peel: total-dim induction + the splitting fact
   (`f v = w ≠ 0, W = k·w ⊕ U ⟹ V = k·v ⊕ f⁻¹U`) + backward `comap` complement chain on an abstract
   finite-dim `LinearMap` chain; transport to `Tuple`. The hardest step (active/dead-edge `Fin`
   bookkeeping). Likely a `pen-and-paper`/`formaliser` pair + a dedicated reviewer. Open when 4b/4c land.
4. **4e — orbits ↔ Kostant (thread 11), ≈free.** Cor 2.9 = `cumulDiffEquiv` restricted, once 4c+4d land.
5. **[gate] Rung-4 reviewer audit** — decorrelated fidelity/precision pass over 4a–4e before rung 4 closes
   (4a's audit is batched here).

## Parked (later / other expedition)
- `Ext` codimension (Cor 3.5); QIP (Thm 6.1) + explicit lattice-point formula (Thm 7.10); the `rlct=½codim`
  cap (Bundle 4). Cosmetic: clear the `abel_nf` info at `RankPattern.lean:128`.

## Notes
- Read `../../lean/CLAUDE.md` before any Lean (Core never imports DLN). In-repo memory only.
- Reader-facing paper digestion is the operator's activity.

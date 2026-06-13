---
title: "Thread 12 — decorrelated rung-4 audit (4a–4d)"
status: closed
topics: [review, audit, rung-4, gabriel, barcode, gate]
created: "2026-06-12"
updated: "2026-06-12"
---

# Thread 12 — decorrelated rung-4 audit (the no-skip AUDIT gate)

Independent reviewer (`reviewer4`, report-only, ran in the main checkout — read+build+/tmp, no git
mutations) + decorrelated Codex (xhigh, frame-in/hypothesis-out). Audited the full rung 4 at
`expedition/core-quiver-engine` HEAD `6e57571`. **Verdict: all four modules SURVIVED — gate PASSES.**

## Gate re-run (reviewer's own outputs)
- `lake build` (Submult/IntervalModule/BaseChange/Barcode): green, exit 0 (1794 jobs).
- `scripts/sorries`: 0 sorry / 0 #exit / 0 native_decide / 0 axiom.
- `#print axioms` on `hasBarcode_of_isSubrep`, `hasBarcode_top`, `submult_baseChange`,
  `rankPattern_baseChange`, `rankPattern_intervalDirectSum_eq_cumul`, `isCompl_span_singleton_comap`,
  `exists_peel` → ALL `[propext, Classical.choice, Quot.sound]`.

## Per-module verdict
- **4a `Submult` — SURVIVED.** `submult` = ordered composite `A_j⋯A_{i+1}`; `rankPattern = .rank`;
  `rankPattern_self = d_i`. Matches paper §3 (`r_{ij}`, `r_{ii}=d_i`). Witness genuine; `CommRing` weakest.
- **4b `IntervalModule` — SURVIVED.** `intervalModule = M_{ij}` (verified the degenerate entering/leaving
  edges are the correct zero maps); `rankPattern_intervalModule` = the Prop-3.1 indicator;
  `rankPattern_intervalDirectSum_eq_cumul` with `cumul` = exactly Prop 3.1's `r_{ij}(m)`. Scope honest
  (constructed-direct-sum side, not completeness). `Field`/`CommRing` split honest. Witnesses genuine.
- **4c `BaseChange` — SURVIVED.** `(P•A)_i = P_{i+1}·A_i·P_i⁻¹` matches paper §2.1; genuine `MulAction`;
  telescoping conjugation + rank invariance sound. `CommRing` throughout (no spurious `Field`). Witness is a
  genuine non-identity `GL₂(ℤ)` element; `r_{02}=2` survives.
- **4d `Barcode` (THE CRUX) — SURVIVED.** Fidelity: the 7 `HasBarcode` clauses faithfully encode the
  existence half of Thm 2.5 (each bar a genuine interval module + f-stable at every edge ⟹ a subrep;
  `iSupIndep` + `⨆=P_t` = vertex-wise internal direct sum = P). `hasBarcode_of_isSubrep` is the real theorem.
  Precision: EXISTENCE only — no uniqueness/orbit↔Kostant claim; deferred items named. **Non-vacuity** (the
  critical check): an adversarial in-Lean probe proved `HasBarcode` with `P t₀ ≠ ⊥` FORCES a genuine nonzero
  line at `t₀` (fired on the `ℚ--id-->ℚ` witness, bar `M_{0,1}`), and the empty barcode satisfies it ONLY
  when `P ≡ ⊥` — no vacuity. Bedrock: `exists_peel` produces a strictly-smaller subrep
  (`finrank_sup_add_finrank_inf_eq` → `Finset.sum_lt_sum`, omega-sound); `Nat.strongRecOn` well-founded on
  `totalDim`; `relSplitting`'s hypothesis is used (not decorative); `Field` necessary (splitting fact needs
  `NoZeroSMulDivisors`).

## Decorrelation (Codex)
FAITHFUL-WITH-CAVEAT, clause-by-clause agreeing, independently confirming non-vacuity. Artifacts were in
`/tmp/codex-audit/` (reviewer report-only; not persisted to the thread codex dir).

## The one caveat (NOT a defect) — controller action
`HasBarcode` encodes the decomposition as an internal-direct-sum **barcode-basis predicate** over chosen
ambient lines, NOT as an explicit Lean iso object `P ≅ ⊕ M_{ij}^{m}`. Logically equivalent (the iso is a
near-free corollary of the f-stable vertex-wise internal direct sum), and the docstrings honestly say
"Equivalently … isomorphic to a direct sum of interval modules" — so it is correctly named. **But the
Tuple-transport tide must still construct that iso as an object.** Recorded in the 4d statement card
(`threads/10-barcode/findings.md`).

## Net
No critical findings; no fidelity break; no vacuity; no overclaim. **Rung 4 (4a–4d) is bedrock; the
AUDIT gate passes.** Remaining for the full orbit ↔ Kostant bijection (Cor 2.9): the explicit iso object +
Tuple transport, uniqueness (near-free via `diff_cumul`), and 4e — all downstream of the audited existence.

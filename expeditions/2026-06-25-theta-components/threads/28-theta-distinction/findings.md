# Thread 28 — θ-invariants distinction capstone (PR #11 follow-up) — certificate

**Formaliser tide (theta-distinction), both capstones CLOSED.** New module
`lean/DLNFibre/DLN/Aoyagi/ThetaOrderDistinction.lean`, wired by the controller; whole library green
(3807 jobs); headlines axiom-clean `[propext, Classical.choice, Quot.sound]` (controller-gated); reviewer
fidelity PASS. Commits `4af0423d` (module), `b24ae93c` (card pin).

## The order-side companion to `codimRepCanonical_fibre_eq_two_paperLambda`
codim MATCHES Aoyagi's λ; θ genuinely DIVERGES. L&R's θ is a geometric **component count**
(`Core.numTop`/`Core.cTheta`); Aoyagi's θ is an analytic **pole order**. This module proves the two
DIFFER + pins exactly when they agree — it asserts NO (false) equality of them.

## Definition (honest naming — reviewer rename adopted)
`aoyagiPoleOrder (ell a : ℕ) : ℕ := a * (ell - a) + 1` — an analytic pole order, NOT a component count
(the bare def can never be read as a count).

## Capstone 1 — the mismatch, tied to the LIVE count (FULLY CLOSED)
- `numTop_d22222_ne_aoyagiPoleOrder : numTop d22222 0 kostantPartitions_d22222_nonempty ≠
  aoyagiPoleOrder 4 2` where `d22222 := ![2,2,2,2,2]`. Routes `numTop_d22222_zero` (= 6) through
  `Core.numTop_zero_eq_cTheta` + `cTheta_d22222 = 6` (decide+kernel), then `6 ≠ 5 = aoyagiPoleOrder 4 2`.
  So the **live** `Core.numTop`/`cTheta` of the actual dimension vector ≠ Aoyagi's pole order —
  impossible to conflate downstream. Nonemptiness discharged in-file (QIP witness `![2,0,0,0]`).
- abstract core `choose_four_two_ne_aoyagiPoleOrder : Nat.choose 4 2 ≠ aoyagiPoleOrder 4 2` (axiom-FREE).
- Deferred (only): tying the `5` to a live `ClosedForm.ell`/`residueA` (those are noncomputable via
  `Tuple.sort` + `ediv`, don't `decide`-reduce; the `(ℓ,a)=(4,2)` correspondence is documented). Reviewer
  independently decide+kernel-verified the harness prefix integers reproduce the exposition: `qipM=4`,
  `qipS=10`, `|δ|=2`, `cTheta=6`.

## Capstone 2 — the agreement regime (FULLY CLOSED, no residual)
- `choose_eq_aoyagiPoleOrder_iff {ell a} (haell : a ≤ ell) : Nat.choose ell a = aoyagiPoleOrder ell a ↔
  min a (ell - a) ≤ 1`.
- genuine strict-divergence half: `choose_gt_aoyagiPoleOrder {ell a} (ha : 2 ≤ a) (hg : 2 ≤ ell - a) :
  aoyagiPoleOrder ell a < Nat.choose ell a`, by Pascal induction (fixed gap `g = ℓ−a`, induction on base;
  `choose_succ_succ'` + column lower bound via `choose_symm` + `choose_le_choose`) — Codex-recommended
  route, lemma names verified against Mathlib v4.29.

## Gates
`#print axioms` both headlines + `choose_gt_aoyagiPoleOrder` = `[propext, Classical.choice, Quot.sound]`
(no sorryAx, no native_decide); `scripts/sorries` 0/0/0/0; whole library green 3807. Aggregator import
wired: `import DLNFibre.DLN.Aoyagi.ThetaOrderDistinction`.

## Distinction preserved
Geometric-count (`Core.cTheta`/`numTop`) vs analytic-pole-order (`aoyagiPoleOrder`) kept apart by name,
docstring, and the `≠` theorem. This is the Lean counterpart to `docs/expositions/theta-invariants-distinction.md`.
Artifacts: `threads/28-theta-distinction/statement-card.md` + Codex consults.

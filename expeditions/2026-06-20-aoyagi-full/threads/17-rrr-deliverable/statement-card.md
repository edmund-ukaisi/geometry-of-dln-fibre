# Statement card — RRR (L=2) model + Aoyagi Theorem 1 (Deliverable #17)

The reduced-rank-regression (`L = 2`) model and Aoyagi Theorem 1, formalised **general-`L`-first**:
RRR is the `L = 2` *instance* of the existing general-`L` API, not a parallel API.

Module: `lean/DLNFibre/DLN/RLCT/Validate/RRR.lean` @ `3f00e68f` (worktree branch
`agent/rrr-deliverable-17`, off `expedition/aoyagi-full` @ `8aaa0837`).

---

## 1. `rrrLambda` / `aoyagi_rrr` — the headline value (sorry-CONDITIONAL)

> **Claim.** The global learning coefficient of the three-layer (`L = 2`) deep-linear square-Frobenius
> loss — the infimum of the local RLCT over the fibre `mult⁻¹(B)` — equals Aoyagi's RRR closed form,
> for any rank-`r` target `B` with every width `≥ r`.

- **Lean:**
  - `def rrrLambda (H : Fin 3 → ℕ) (r : ℕ) : ℚ := aoyagiLambda H r`
  - `theorem aoyagi_rrr (H : Fin 3 → ℕ) (r) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)`
    `(hB : B.rank = r) (hr : ∀ s, r ≤ H s) :`
    `(⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (rrrLambda H r)`
    (proof: `aoyagi_learning_coefficient (L := 2) H r B hB hr (by norm_num)`)
- **Gloss.** `rrrLambda` is *defeq* `aoyagiLambda` at `L = 2`; `aoyagi_rrr` is literally the general
  headline `aoyagi_learning_coefficient` specialised to `L := 2`. The general-`L`-first identity:
  RRR adds no closed-form API of its own.
- **Proved.** That `aoyagi_rrr` is the genuine `L = 2` instance of the general theorem (the
  specialisation type-checks; `Fin (2+1) = Fin 3`, `Fin.last 2 = (2 : Fin 3)` line up; `1 ≤ 2` by
  `norm_num`). The closed-form value `rrrLambda` reproduces RRR ground truth — `#eval`-enforced:
  `(2,2,2)→3/2`, `(2,1,2)→1`, `(1,1,3)→1/2` (dominated `ℓ=1`), `(3,3,4)-core→4`.
- **Assumed.** `hB : B.rank = r`, `hr : ∀ s, r ≤ H s` (well-definedness / fibre-nonemptiness domain).
- **Cited.** S2 (`monomial_rlct`, Watanabe/Hironaka monomial-integral threshold) — via the general
  assembly.
- **Deferred (the inherited open obligations, NOT done).** Transitively, the two named general-headline
  sorries: `deepest_regular_core_normal_form` (the gauge-slice normal form, #44) and
  `rlctAt_deepest_le_of_optimal` (the D1≥ fibre-monotonicity). `aoyagi_rrr` carries **no new sorry** but
  is sorry-conditional to exactly this degree — `#print axioms aoyagi_rrr` shows `sorryAx`.
- **Status.** sorry-free FILE; statement sorry-conditional (inherits the general headline).

## 2. `aoyagi_rrr_222` / `aoyagi_rrr_212` — concrete anchors (sorry-FREE)

> **Claim.** The local RLCT of the `(2,2,2)` (resp. `(2,1,2)`) three-layer loss at the deepest point of
> the `B = 0` fibre equals `rrrLambda` there: `3/2` (resp. `1`).

- **Lean:**
  - `theorem aoyagi_rrr_222 : rlctAt H222 (dlnLoss H222 0) deepest222 = ENNReal.ofReal (rrrLambda H222 0)`
  - `theorem aoyagi_rrr_212 : rlctAtOn (dlnLoss ![2,1,2] 0) deepest212 = ENNReal.ofReal (rrrLambda ![2,1,2] 0)`
- **Gloss.** Re-exports of the validated `case222_rlct` / `case212_rlct`, recast against `rrrLambda`.
  The machinery reaches a *proven* (not merely assembled) RLCT value at `L = 2`.
- **Proved.** Both equalities, **sorry-free**.
- **Cited.** `aoyagi_rrr_222`: S2 (`monomial_rlct`) — `#print axioms` = `[propext, Classical.choice,
  Quot.sound, monomial_rlct]`. `aoyagi_rrr_212`: **none** — `[propext, Classical.choice, Quot.sound]`
  (S2-free, axiom-clean).
- **Deferred.** none.
- **Status.** sorry-free.

## 3. `rrrTheta` — the order (combinatorial value sorry-FREE; analytic binding is a SEAM)

> **Claim.** The RRR order is `θ = a(ℓ − a) + 1` with `(ℓ, a)` from the `L = 2` selector `def:Mset-L2`.

- **Lean:** `def rrrTheta (ℓ a : ℕ) : ℕ := aoyagiTheta ℓ a` (`#eval`: `(2,2,2)→1`, `(2,1,2)→2`,
  `(1,1,3)→1`).
- **Proved.** The combinatorial value, on *given* selector data. `#print axioms rrrTheta` = no axioms.
- **Deferred / SEAM (NOT stated).** The analytic binding `monomialOrderAnalytic (RRR loss) = aoyagiTheta`
  at `L = 2`. Blocked on (i) no Lean def of the `L = 2` selector `(ℓ, a)` (`def:Mset-L2`, itself
  tie-underspecified, §5 ledger (F-1)); (ii) no chart-count identity binding `monomialOrderAnalytic` to
  `aoyagiTheta` (general `aoyagiTheta_eq` is a weak existential that does not reference the widths —
  intentionally not mirrored here). This is the order-half blocker (discuss-at-close item 2).
- **Status.** sorry-free (value only).

---

## Review verdict — PASS (fidelity, 2026-06-24)

Independent reviewer (decorrelated Codex): **PASS** on all five checks. `aoyagi_rrr` confirmed
literally `aoyagi_learning_coefficient (L := 2)` (verified by elaboration probe); general-`L`-first
confirmed (RRR imports the general API, never the reverse; no def/proof depends on RRR); non-vacuity
inhabitant-tested; `#print axioms` machine-confirmed the Proved/Assumed/Cited/Deferred split
(`aoyagi_rrr`→`sorryAx`; `_222`→S2 only; `_212`→axiom-clean; `rrrTheta`→no axioms); ground truth
reproduced by an independent Python re-implementation of the `Mval`/`Adm` minimisation. The dropped
weak θ-order theorem judged the honest call. **Status: sorry-free + reviewed.**

One awareness note (not a defect): `hr : ∀ s, r ≤ H s` also demands `r ≤ H¹` (inner width), slightly
stronger than minimal rank-feasibility — but it is exactly the general headline's `hr` being
instanced (conservative; restricts domain, never weakens conclusion). Tighten upstream if ever.

## Fidelity notes for the reviewer

- **General-`L`-first preserved.** `rrrLambda := aoyagiLambda`, `aoyagi_rrr := aoyagi_learning_coefficient
  (L := 2)`. No RRR-specific closed-form split shapes the general API; the §5 regime split (balanced
  `ℓ=2` / dominated `ℓ=1`) is cross-check ground truth only.
- **Non-vacuity.** `aoyagi_rrr` is the genuine instance (not trivially satisfiable); `aoyagi_rrr_222/212`
  exhibit proven values; `rrrTheta` `#eval`s match. The weak `∃` order theorem was DROPPED (controller
  decision) precisely because it would be free-choice-provable and capture nothing about RRR's order.
- **Trap-iii-clean.** The sorry-conditional headline carries `sorryAx`; the proven anchors do not — the
  axiom prints make the proof-state machine-checkable, not just asserted.

# rev-Q — fidelity verdict: lemma (Q) vs the L7 certificate

Reviewer rev-Q, 2026-07-22. Function: **fidelity** (report-only — statement/hypotheses vs the informal
claim; no mathematics rewritten). Target: `lean/DLNFibre/Core/Aoyagi/BlockBlowupCover.lean` (2 theorems).
Spec: `fan-design-certificate.md` §2.1 (the block-atom `(Q)`) + `statement-card-Q-block-cover.md`.
Model it generalizes: `Core/Aoyagi/OriginBlowup.ball_subset_iUnion_blowup_image` (the `S = univ` atom).

## VERDICT: SURVIVED

Both theorems faithfully implement the certificate's `(Q)`. The R = 1 corollary
`ball_subset_iUnion_blockBlowup_image` is **exactly** the certificate's displayed `(Q)`; the
general-radius `ball_subset_iUnion_blockBlowup_image_radius` is a true, tight strengthening consistent
with the certificate. Forced recompile (olean deleted) + fresh-scratch `#print axioms` on both =
`[propext, Classical.choice, Quot.sound]` — sorry-free, no cited axiom. Decorrelated Codex (xhigh,
hypothesis withheld) independently re-derived all four points and sharpened the tightness (below).

## Per-point findings (seat-Q's list + the standard bar)

1. **Sup-norm ball = the cube — CONFIRMED.** The norm on `Fin D → ℝ` is `Pi.normedAddCommGroup` (sup
   norm on a finite product). The proof discharges the target membership with `pi_norm_lt_iff hR`
   (`‖x‖ < R ↔ ∀ j, ‖x j‖ < R`, `0 < R`) and the source membership with `pi_norm_le_iff_of_nonneg`
   (`‖w‖ ≤ ρ ↔ ∀ j, ‖w j‖ ≤ ρ`, `0 ≤ ρ`) — both verified present in Mathlib v4.29
   (`Analysis/Normed/Group/Constructions.lean:314,333`). So `Metric.ball 0 R` genuinely IS the open
   sup-norm cube `{x | ∀ j, |x_j| < R}` and `closedBall 0 ρ` the closed cube. Faithful.

2. **Spectator passthrough — CONFIRMED.** `blockBlowupMap` (`Core/Aoyagi/BlockBlowup.lean:31`) is
   `fun w j ↦ if j = p then w p else if j ∈ S then w p * w j else w j`. For a spectator `j ∉ S` (and
   `j ≠ p`, forced since `p ∈ S` in the cover): both guards fail ⟹ `w j` (identity). Matches the
   certificate's `j ∉ S ↦ w_j` exactly. The pivot slot `p ↦ w_p` and center-nonpivot `j ↦ w_p·w_j`
   also match.

3. **Union fans over `p ∈ S`; `S = univ` recovers OriginBlowup — CONFIRMED.** RHS is
   `⋃ p ∈ S, blockBlowupMap S p '' (closedBall 0 (max R 1))`, matching the certificate's `⋃_{p∈S}`.
   `blockBlowupMap univ p = blowupMap p` is proven (`BlockBlowup.blockBlowupMap_univ`); at `S = univ`
   the shape aligns with the OriginBlowup atom (`⋃ p ∈ univ` = `⋃ i : Fin D`, `max 1 1 = 1`). The
   file honestly states it does NOT re-derive OriginBlowup — it stands on the same `Core.Aoyagi` atoms.
   Note (strength, not a defect): at `S = univ`, `(Q)` needs only `S.Nonempty` (i.e. `D ≥ 1`), whereas
   OriginBlowup's model needs `2 ≤ D` — so `(Q)` is strictly stronger there, and correct at `D = 1`
   (`blockBlowupMap {0} 0 = id`, cover trivial).

4. **`S.Nonempty` is the ONLY extra hypothesis — CONFIRMED.** Radius form: `(hS : S.Nonempty)` +
   `(hR : 0 < R)`. R=1 corollary: `(hS : S.Nonempty)` only. No smuggled side conditions — `p ∈ S` is
   not a hypothesis (`p` is chosen internally by `Finset.exists_max_image S _ hS`); no `2 ≤ D`, no
   `D ≠ 0` (subsumed by `S.Nonempty`), no tie-breaking assumption. The R=1 corollary's statement is
   character-for-character the card's `(Q)`.

5. **General-radius `max R 1` hardening — TRUE, TIGHT (uniformly over `|S| ≥ 2`), R=1 form follows.**
   The witness coordinates scale as: pivot `|w_p| = |x_p| < R`; center-ratio `|w_q| = |x_q|/|x_p| ≤ 1`
   (argmax); spectator `|w_j| = |x_j| < R`. So the source box must hold both the `< R` scale and the
   `≤ 1` scale ⟹ radius `max R 1`. Codex-sharpened tightness (I verified both):
   - `R < 1`, `|S| ≥ 2`: `x = (R/2)` on two center coords, else 0 ⟹ any pivot forces some `w_q = 1 > R`,
     so radius `R` is insufficient — `max R 1 = 1` is needed.
   - `R > 1`: `x = (R+1)/2` on `S` ⟹ `|w_p| > 1`, so radius `1` is insufficient — `max R 1 = R` is
     needed.
   The R=1 corollary follows by `rwa [max_self]` (`max 1 1 = 1`). Nothing in the certificate
   contradicts the general form — §2.4's R-parametric fold (box bound `R·(1+R)^m`) consumes exactly
   this kind of box. Naming is honest: `…_radius` = radius form, name = content, for both.

6. **Vacuity / degeneracy — CLEAN, no silent vacuity.**
   - `D = 0`: `Fin 0` empty ⟹ no `S : Finset (Fin 0)` is nonempty ⟹ hypothesis unsatisfiable. This is
     the honest boundary (no pivot exists), not a hidden vacuity; non-vacuous for all `D ≥ 1`.
   - `|S| = 1` (`S = {p}`): `blockBlowupMap {p} p = id`; cover reduces to
     `ball 0 R ⊆ closedBall 0 (max R 1)` — true, non-vacuous. Proof's ratio branch is simply empty.
   - `R < 1`: `max R 1 = 1`; proof carries `|x p| < R ≤ max R 1`. Non-vacuous (`ball 0 R ∋ 0`).

7. **Decorrelated Codex (xhigh, hypothesis withheld;
   `codex/rev-Q-fidelity-{prompt,answer}.md`).** Verbatim overall: "the Lean statement faithfully
   captures Q; its radius is uniformly sharp, though oversized for singleton `S` when `R < 1`."
   [fact] Q true incl. `x_p = 0` and `|S| = 1`; [fact] `max R 1` tight for `|S| ≥ 2` via the two
   explicit counterexamples above; [fact] no hidden hypotheses, vacuous only at `D = 0`; [fact]
   `S = univ` recovers `blowupMap`. It converged on the same routing (`p = argmax_{q∈S}|x_q|`, ratio
   lift) I read from the proof.

## The single precision nuance (non-defect, flagged for name=content)

The radius docstring says "the `max R 1` source radius is **forced** by the blow-up geometry." Precisely,
`max R 1` is forced only for `|S| ≥ 2`; for the singleton `|S| = 1` sub-case the ratio branch is
vacuous, so only `R` is forced and `max R 1` is (harmlessly) oversized when `R < 1`. The statement stays
TRUE at `|S| = 1` (a superset source box), and a per-cardinality tightening would complicate the
signature the fold consumes for no gain — so this is a wording precision point, not a fidelity defect.
"Forced" reads as "forced in general (`|S| ≥ 2`)", which is correct. No change requested; recorded so the
controller can decide whether to soften "forced" to "the tight uniform bound (`|S| ≥ 2`; loose only at
the vacuous singleton)".

## Evidence

- Forced recompile: deleted `BlockBlowupCover.olean`/`.ilean`, `scripts/lb
  DLNFibre.Core.Aoyagi.BlockBlowupCover` → green (7.1s).
- Fresh-scratch `#print axioms` (imports the module anew) on BOTH theorems =
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `@[cited]` axiom.
- Mathlib lemma existence verified by grep at the v4.29 pin.
- Codex artefact: `threads/L7/codex/rev-Q-fidelity-{prompt,answer}.md`.

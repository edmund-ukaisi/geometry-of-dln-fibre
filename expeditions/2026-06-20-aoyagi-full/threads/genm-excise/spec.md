# genm-excise — build spec: RETIRE the `monomial_rlct` axiom → S2-FREE library (Stage B)

**Mandate (controller, executing operator CLOSE plan point 2 Stage B + standing-decision-6 +
discuss-at-close #86).** The learning-coefficient headlines (`aoyagi_learning_coefficient_L2`, `_gen`,
`_gen_le`, `aoyagi_deepest_reduction_gen`) are ALREADY clean-three (S2-free on the λ-path via the
proven identity `monomialThreshold_eq_iInf_axisRatio`). The `monomial_rlct` axiom still EXISTS, used
only by (a) two upstream Skeleton threshold-helpers and (b) the θ side (an opaque + a sorry
placeholder). This strand RETIRES the axiom entirely → a fully **S2-FREE** library.

## Discipline (read first)
- `lean/scripts/lb` ONLY; force-recompile touched files; forced `#print axioms` on the four headlines
  (`aoyagi_learning_coefficient_L2`, `_gen`, `aoyagi_learning_coefficient_gen_le`,
  `aoyagi_deepest_reduction_gen`) — they MUST stay `[propext, Classical.choice, Quot.sound]`
  (unchanged) after the excise.
- **NO sorry-scaffold. FAIL-FAST:** if deleting the axiom/opaque/placeholder surfaces a live consumer
  you didn't expect (broader fallout than the map below), STOP and report the shrunk ladder — do not
  paper it. This is a delicate deletion; report the fallout scope at the first checkpoint.
- **Branch `genm-excise`** (run `git ls-remote --heads origin genm-excise` first; if taken, use
  `genm-excise2`). Checkpoint-commit + SendMessage to team-lead at: (1) the fallout-scope report
  (after grepping all consumers, BEFORE deleting), (2) helpers relocated + green, (3) axiom deleted +
  full green S2-free. SendMessage summaries ≤180 chars. Fire a decorrelated local-codex-consult if a
  deletion's fallout looks gnarly.
- **File ownership:** you OWN `Skeleton.lean` (the axiom :120-122, the two helpers, the opaque
  `monomialOrderAnalytic` :101, the placeholder `aoyagiTheta_eq` :1705), `Case222Cover.lean`,
  `Case222CoverGE.lean`, `ResolutionAtlas.lean`, `RRR.lean`, `AxCheck.lean`, and
  `MonomialThresholdIdentity.lean` (if you relocate the helpers there). **Do NOT touch** the Validate
  headline files (`HeadlineGenAssembly`, `HeadlineGenBounds`, `HeadlineL2Assembly`, `DeepestFrontGaugeGen`)
  or the LEGACY sorried Skeleton headline stack (`aoyagi_learning_coefficient` :1725,
  `deepest_point_reduction`, `deepest_regular_core_normal_form` :1124, and the :1172/:1228 sorries — that
  is a SEPARATE peel-stack the controller parks; leave those sorries alone, just don't let them break).

## The map (verified — the axiom's structure + every live use)
`axiom monomial_rlct (d) (k h) : monomialThreshold d k h = ⨅ⱼ axisRatio (h j) (k j)   -- .1 (threshold)
  ∧ ((∃ j, k j ≠ 0) → monomialOrderAnalytic d k h = monomialOrder d k h)              -- .2 (order)`
- **`.1` (threshold) is now PROVEN downstream:** `monomialThreshold_eq_iInf_axisRatio (d) (k h)`
  (`Validate/MonomialThresholdIdentity.lean`), which imports Skeleton (→ the circular wall: Skeleton
  can't reference it).
- **LIVE `.1` users (6):** two are the Skeleton HELPERS themselves —
  `monomialThreshold_ge_of_mult` (Skeleton:~132) and `monomialThreshold_le_axis` (Skeleton:~143) — and
  four are direct: `Case222Cover.lean:157`, `Case222CoverGE.lean:88` + `:116`, `ResolutionAtlas.lean:100`.
- **LIVE `.2` / θ users:** `monomialOrderAnalytic` (opaque def Skeleton:101) is referenced only by the
  axiom `.2` (Skeleton:122); `aoyagiTheta_eq` (Skeleton:1705) is a bare `sorry` weak-existential
  (`∃ ℓ a d k h, monomialOrder d k h = aoyagiTheta ℓ a`) — it does NOT use the axiom, but it IS the
  "θ order-count" placeholder standing-decision-6 says to excise. `RRR.lean` mentions both in PROSE.

## The plan (execute in order; checkpoint after step 1)
0. **SCOPE-REPORT (checkpoint):** grep EVERY consumer of `monomial_rlct`, `monomialOrderAnalytic`,
   `aoyagiTheta_eq`, `monomialThreshold_ge_of_mult`, `monomialThreshold_le_axis` (live proof terms, not
   comments). Confirm the four `.1` direct users + the two helpers are the ONLY `.1` consumers, and that
   `monomialOrderAnalytic`/`aoyagiTheta_eq` have NO live consumers beyond the axiom/their own decls.
   Report the scope to team-lead. If broader than this map, STOP.
1. **Relocate the two helpers downstream.** Move `monomialThreshold_ge_of_mult` +
   `monomialThreshold_le_axis` out of Skeleton into `MonomialThresholdIdentity.lean` (or a new file
   importing it), reproving each via `monomialThreshold_eq_iInf_axisRatio` instead of
   `(monomial_rlct …).1` (the proofs are `rw [identity]; exact le_iInf …` / `iInf_le …` — trivial swaps).
   All their consumers (Case222CoverGE/Value, MonomialThresholdIdentity, ResolutionAtlas) are already
   downstream — verify each still resolves. Green-gate. Checkpoint.
2. **Rewire the four direct `.1` uses** (`Case222Cover:157`, `Case222CoverGE:88`+`:116`,
   `ResolutionAtlas:100`) from `(monomial_rlct d k h).1` to `monomialThreshold_eq_iInf_axisRatio d k h`.
3. **Delete** `axiom monomial_rlct` (Skeleton:120-122), the opaque `monomialOrderAnalytic` (Skeleton:101),
   and the placeholder `aoyagiTheta_eq` (Skeleton:1705). Fix the fallout: RRR prose refs, AxCheck's
   `monomial_rlct`/`aoyagiTheta_eq`/`monomialOrderAnalytic` `#print axioms` lines + comments (remove or
   re-point), any Skeleton docstrings referencing the deleted items.
4. **Green-gate S2-FREE:** full `lb` green; `git grep "axiom monomial_rlct"` = EMPTY; `git grep -nE
   "monomial_rlct|monomialOrderAnalytic|aoyagiTheta_eq"` shows only prose/removed (no live terms);
   forced `#print axioms` on the four headlines = `[propext, Classical.choice, Quot.sound]` UNCHANGED.
   Report the final axiom lines + the grep confirmation.

## What the controller does (NOT you) — the θ-seam re-home
Deleting `aoyagiTheta_eq` + the `.2` order conjunct removes the θ analytic-multiplicity placeholder.
Its CLAIM (`∃ realising (d,k,h), monomialOrder d k h = aoyagiTheta ℓ a` = the chart-count A2, Lemmas
4–5) is re-homed by the controller into `ROADMAP.md` + a statement card as a DEFERRED seam (per
standing-decision-6). In your step-3 report, quote the exact `aoyagiTheta_eq` statement + note what
prose in RRR.lean referenced the θ-order so the controller frames the seam faithfully. Do NOT write
ROADMAP/cards yourself.

## Fidelity guards
- The four headlines' `#print axioms` MUST be byte-identical before/after (clean-three) — the excise
  changes only the axiom/θ side, never the headline closures.
- Removing the sorry `aoyagiTheta_eq` REDUCES the library's sorry count (Skeleton:1705 warning gone) —
  that is expected + good (it was a placeholder). Do NOT try to PROVE it.
- If relocating a helper into `MonomialThresholdIdentity` creates an import cycle (it shouldn't —
  that file is downstream of Skeleton + the identity), report it rather than forcing.

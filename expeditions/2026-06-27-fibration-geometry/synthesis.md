# Synthesis — `fibration-geometry` (controller's internal read; flushed every tick)

Not a deliverable. Current integrative ground + drift-guard. Re-ground substrate after compaction.

## Where we are (tick 0 — setup, 2026-06-27)

Expedition stood up off merged `dev` (`origin/dev` = `06b30931`, the PR #11 theta-components merge), on
branch `expedition/fibration-geometry`. Base build is merged-green by construction. Two recon scouts
(`recon-bundle-base`, `recon-anatomy-runway`) reported; their certificates are digested into `brief.md`.
Operator chose scope **"spine, roadmap the rest"** and **skip the (2,2,2,2,2) rlct probe for now**, plus
a disposition steer: run as a large rising-sea hero arc, "no Mathlib support" ≠ blocker (see
`lessons.md`).

## The spine, as a dependency graph

```
S1 (rank-bridge keystone) ──┬──> S3 (flatness payoff) ──┐
                            └──> S4 (honest locallyTrivial) ──> S5 (reusable API, packages S3+S4)
S2 (smooth-block certificate) ────────────────────────────  (independent; RLCT-runway slab 1)
```

S1 and S2 launched in parallel as the first wave (independent modules; controller is sole merger,
append-only aggregator imports). S3/S4 unblock when S1 lands; S5 packages.

## Precise S1 target (the keystone)

`rankROpen` (`FibreBundleLocallyTrivialFull.lean:520`) is *defined* as the complement of the pivot-minor
common-vanishing locus; its docstring states `rankROpen = {rank = r}` is **not** a theorem yet (only the
point-set forward inclusion `sweepSigma_subset_chartOpen`). S1 closes the scheme-level identity via the
prime/residue-field bridge `P ∈ rankROpen ↔ rank over κ(P) = r`:
- "≥" (`P ∈ rankROpen ⟹ rank ≥ r`): some pivot minor ∉ P ⟹ unit in κ(P) ⟹ `rank_of_isUnit` +
  `rank_submatrix_le`. Largely banked machinery.
- "≤" (`rank ≤ r` on Σ̄^r ⟹ `rank over κ(P) ≤ r`): needs the **new** over-field minor criterion
  (all `(r+1)`-minors vanish ⟹ `rank ≤ r`), the **dual** of `exists_invertible_minor_of_rank`
  (RankMinorCover.lean:93). This is the genuinely-new lemma; classical, reachable.

## Drift-guard

- Keep **name = content**: the `locallyTrivial`/`Flat π` headlines must denote exactly what is proved;
  residual gluing (R1 overlap cocycle) named as open, not folded into an overclaim.
- Do **not** pre-pull roadmap items (R1–R5) into the spine to look complete; the review bar, not
  pre-emptive scope, is the filter — but also do not pre-defer reachable spine work.
- The RLCT equality itself is *cited*; this expedition does not prove it, only builds its substrate +
  hands over slab 1. Don't let S2's local model get named as if it proved `rlct = codim/2`.

## Open questions carried

- S3: atlas-routed vs cheap flatness (resolve in-tide).
- S4: is source-side local-triviality over `rankROpen` satisfying without R1's full overlap cocycle?
  (decide at S4 integration).

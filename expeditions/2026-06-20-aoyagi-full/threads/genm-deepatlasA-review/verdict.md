# Fidelity review — `genm-deepatlas` Tide A (`RouteMSJDeepAtlas.lean`)

**Reviewer:** independent fidelity (controller-spawned; not the tide author). **Function:** do the Lean
statements faithfully realise the design claims — no overclaim, no vacuity, no hidden gap?
**Target:** worktree `/home/ubuntu/workspace/deepatlasA-wt`, branch `genm-deepatlas` @ `12a7ae38a`,
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeepAtlas.lean` (uncommitted), namespace `…DeepAtlas`, 8 results.
**Spec:** `genm-deepatlas-design/design.md` §2.1 (per-level block-Schur big-cell) + §2.2 (product-layer
reduction). **Date:** 2026-07-15.

## Verdict: SURVIVED — all 8 statements FAITHFUL to the design; no overclaim, no vacuity, no hidden gap.

Independently corroborated by decorrelated Codex (gpt-5.x, xhigh, my conclusion withheld,
"argue whichever way"): `codex/fidelity-{prompt,answer}.md` → **OVERALL: FAITHFUL to design**, all 8, P1–P4 yes.

## Axiom footprint — force-fresh verified (deepatlasA's assertion confirmed independently)
Deleted `RouteMSJDeepAtlas.olean`, rebuilt the module from source via `scripts/lb` (exit 0, fresh
4.4 s compile — catches a masked type-error), then `lake env lean` on a throwaway `#print axioms` scratch
against the fresh olean. All 8: `[propext, Classical.choice, Quot.sound]` — clean-three. No `sorryAx`, no
`native_decide`. (Scratch removed; worktree left with only the two intended untracked paths.)

## Per-signature fidelity (the load-bearing checks)

- **D1 `deepLevel_bigcell_cov / _rank_eq / _rank_le_iff`** — verbatim `:=` re-exports of the banked front
  `chart5_bigcell_cov / chart5_rank_eq / chart5_rank_le_iff_reassembled`. Confirmed the block-map is exact:
  `chart5Shift (Δ,U,V) = V·Δ⁻¹·U` (def read in `RouteMSJIncidenceChart5BigCell`), so the CoV coordinate
  `W = E + chart5Shift` gives Schur `E = W − VΔ⁻¹U` and `{rank M ≤ r} = {E = 0}` — exactly design §2.1
  (a)/(b)/(c). `IsUnit Δ.det` is design's GL_r pivot, not a silent narrowing. Re-exports type-check (build
  green) ⟹ front signatures match. FAITHFUL.

- **D2 `deepReduce_skeleton`** (SCRUTINY 1) — the EXACT CUR identity on `{E=0}`:
  `fromRows Δ V · Δ⁻¹ · fromCols Δ U = [[Δ,U],[V,VΔ⁻¹U]]`. Hand-expanded `[[Δ],[V]]·Δ⁻¹·[Δ|U] =
  [[I],[VΔ⁻¹]]·[Δ|U] = [[Δ,U],[V,VΔ⁻¹U]]` (uses `VΔ⁻¹Δ = V`). `fromRows` = vertical stack = pivot COLUMNS
  `A`; `fromCols` = horizontal stack = pivot ROWS `D`. Orientation correct, **no transpose slip** (Codex
  concurs). FAITHFUL.

- **D2 `deepReduce_rank`** (SCRUTINY 2) — `rank(X·M) = rank(X·fromRows Δ V·Δ⁻¹)` on `{E=0}`; `X = B·L`
  recovers design's `rank(B·L·M)=rank(B·H)`, `H = L·A·Δ⁻¹`. A faithful GENERALISATION (any head `X`), not a
  narrowing. Rank preservation is GENUINE, not assumed: `D = fromCols Δ U` has right inverse
  `fromRows Δ⁻¹ 0` (`D·D' = ΔΔ⁻¹ + U·0 = I`, `hΔ`), fed to `rank_mul_eq_of_mul_eq_one` whose hypothesis
  `D·D'=1` is actually discharged in-proof. Correctly scoped to `{E=0}` (M = `fromBlocks Δ U V (VΔ⁻¹U)`);
  claims nothing off-stratum. FAITHFUL.

- **D2 `deepReduce_cov`** (SCRUTINY 3) — `∫⁻ L, g(L ᵥ* G) = ∫⁻ L, g L` for any `|det G| = 1`, over `Fin n`.
  `(fun i ↦ L i ᵥ* G) = L·G` (right-mult). Non-vacuous, correctly typed. Jacobian collapses correctly:
  banked `lintegral_comp_rightMulₚ` yields `ENNReal.ofReal (|det G|^m)⁻¹ · ∫⁻`, and `|det G|=1` ⟹ factor 1.
  **Deferral is SOUND:** design's `G₀` is sum-typed `Fin r ⊕ Fin(n−r)`; the `Fin n ↔ sum` reindex is
  `det_reindex_self` (`Mathlib/.../Determinant/Basic.lean:251`, verified present) — `det(reindex e e G₀) =
  det G₀ = 1`, pure det-1 coordinate plumbing, no hidden nontrivial step. FAITHFUL.

- **D2 `deepReduce_G0_det_eq_one`** — `det (fromBlocks 1 0 S 1) = 1` for any `S`, via `det_fromBlocks_zero₁₂`
  (lower block-unitriangular). Matches design's unitriangular `G₀` (`S = VΔ⁻¹`); general `S` is a valid
  generalisation. FAITHFUL.

- **helper `rank_mul_eq_of_mul_eq_one`** — `D·D'=1 ⟹ rank(X·D)=rank X`, arbitrary Fintype index. Proof is
  the genuine `le_antisymm` (`rank_mul_le_left` both ways via `X=(XD)D'`). FAITHFUL.

## Hypotheses & scope guard (SCRUTINY 4, 5)
- `IsUnit Δ.det` / `|G.det|=1` are exactly design's invertible-pivot / unit-Jacobian conditions —
  substantive, satisfiable, non-narrowing (Codex P4 concurs). Non-vacuity is witnessed IN-FILE by three
  `example` blocks at a concrete `2×2` pivot cell. No statement is trivially true.
- **F·E seam guard holds.** `loss`, `seam`, `F·E`, `spectator`, `rlct`, `frob`, `norm ‖·‖` appear ONLY in
  docstring prose (lines 23–24, 43–44), explicitly labelling them the deferred Tide-D loss-monomialisation
  phenomenon. NO theorem statement contains the `F·E` seam or any loss/rlct claim. These are pure
  rank/measure charts, loss-independent, as scoped.

## Minor precision note (non-blocking, report-only — NOT a fidelity break)
The `deepReduce_cov` docstring says "Instantiated at `G = G₀` (via `deepReduce_G0_det_eq_one`) this is the
product-layer reduction CoV." Literal instantiation at the sum-typed `G₀` still needs the deferred det-1
reindex (`det_reindex_self`) to move `G₀` to `Fin n`; the phrasing slightly understates that bridge. The
deferral is disclosed (card + controller) and sound, and the STATEMENT of `deepReduce_cov` is faithful — so
this is a wording tightening for tide B / integration, not a statement defect.

## Codex inference flags (preserved per policy)
- Sig 1: Codex flagged as *inference* that `Chart5FixedBlocks` carries the intended product measure
  (its def was withheld from Codex). **Resolved on my side:** the re-export is verbatim of the front
  `chart5_bigcell_cov`, proven over `volume` (raw-pi product Lebesgue) via `Measure.volume_eq_prod` +
  `lintegral_add_right_eq_self`. Measure is the intended one.
- Sig 6: Codex noted the sum-type application "requires only the explicitly deferred coordinate reindex" —
  matches my `det_reindex_self` finding.

# `hproducer` conjunct (b) — VERDICT: FALSE for a non-front pivot `J` (CONTROLLER DECISION REQUIRED)

Thread 31 formalisation tide, 2026-06-25. The LAST L2-binding gap (`hproducer`, the per-`w` block
producer inside `framedParams_split_eq_frame_raw`) **cannot be filled as the cert currently structures
it.** Conjunct (b) — the S4 reg-energy identity `∑ deepestEFull(split w)² = Sreg` — is FALSE for a
non-front pivot `J`. This refutes "verdict option A" (the hoped π_J cancellation) from
`hs1prime-verdict.md` / `framedbody-cert.md`.

## What was confirmed (triply, decorrelated)

1. **Exact index algebra** (Codex pass 1, `codex/hproducer-pij-answer.md`):
   ```
   reindex(rThr_row, pivotThr J_col)( colPerm_J(M) ) = reindex(rThr_row, rThr_col)( M ).
   ```
   The pivot reindex applied to the colPerm'd framed product collapses to the THRESHOLD reindex of the
   clean product. So `deepestEFull` (which reindexes `prod(framedParamsPivot)` — last layer carries
   `colPerm_J`, established by hS1') is **threshold-effective**, while the `hconj` blocks
   (`reindex(rThr, pivotThr J)(P0·(prod−B)·QL)`) are **pivot-aligned**. For a non-front `J` these
   disagree. The mismatch SURVIVES the nontrivial trailing `QL` (it mixes columns AFTER the colPerm, so
   the outer reindex cannot absorb the permutation).

2. **Numeric witness** (`codex/pij_blockcheck.py`, reproduces on clean re-run): `r=1, H0=1, H2=2, J:0↦1`,
   nontrivial `QL = [[2,1],[0,3]]`:
   - `∑ deepestEFull² = 17.98` (pivot reindex of the colPerm'd product)
   - `Sreg(hconj) = 23.65` (pivot reindex of the clean product)
   - DIFFER ⇒ conjunct (b) false. (And the FACT-2 index identity verifies True.)

3. **The cheapest repair is UNSOUND** (Codex pass 2, `codex/hproducer-repair-answer.md`, Q3 decisive No):
   compare `deepestEFull` energy to the THRESHOLD residual + assert threshold-`Sreg` = pivot-`Sreg` —
   FALSE. A column permutation crossing the `r ⊕ (n−r)` block boundary moves entries between
   `P00`/`P01`/`P11`, and the `−1` corner subtracts from the diagonal of the `r×r` block, so moving which
   columns occupy that corner changes which entries are compared to `1`. The SELECTED expression
   `∑(P00−1)²+∑P01²+∑P10²` is not invariant under the split swap (only the WHOLE-matrix Frobenius energy
   is, which is not what `Sreg` measures).

## Why this is live (not vacuous)

The caller `deepest_gauge_construction` sets `J := Jb.trans (finCongr …)` where `Jb` comes from
`deepestPoint_frame_pivot_exists` = B's pivot column set. For a generic rank-`r` `B`, `Jb` is NOT
`{0..r-1}`. So the non-front case is the generic case, not a corner. (At the deepest gauge `w0` the
deviation vanishes, `colPerm_J(0) = 0`, so hS3b / the basepoint facts are SOUND — only the general-`w`
energy identity, conjunct (b), is hit.)

## What conjunct (b) is FOR (so the controller can scope the repair)

The downstream loss bound (`deepest_loss_squeeze` → `dlnLoss_two_sided_of_frame`) needs ONLY `hconj` +
`hleak` + the folded core (d')/(e') to get `dlnLoss ≍ Sreg + Score`. The PIVOT reindex is REQUIRED there
because it normalizes `B` (`reindex(rThr, pivotThr J)(P0·B·QL) = fromBlocks 1 0 0 0`). Conjunct (b)
`∑deepestEFull² = Sreg` is used ONLY to bridge `Sreg` (the loss/hconj object) to the PIN1
reg-straightening output `deepestEFull` (so the final `Φ` is in straightening coordinates,
`hSreg_eq`). The bridge is exactly what breaks: the two sides live in different column conventions.

## Sound repairs (BOTH are headline-architecture, OUT of leaf scope)

- **R1 — make `deepestEFull` pivot-AWARE.** Read the framed last layer in pivot columns / undo
  `colPerm_J` before the pivot reindex, so `deepestEFull` targets the same object as `hconj`. Cost: a
  definition-level change to `deepestEFull` (DeepestGaugeConstruction.lean:412) that ripples into
  `deepestEFull_deriv`, `deepestEFull_coreZero`, and — critically — the PIN1 interface
  `deepestEPivot_regSlice_fderiv` (which this tide was instructed to keep `[propext, Classical.choice,
  Quot.sound]`). Best soundness, but touches the forbidden PIN1 object.
- **R2 — pre-permute `B`'s columns by `π_J⁻¹`** so the effective pivot is FRONT `{0..r-1}`; then
  `pivotThr J = rThr` everywhere and FACT 2 makes `deepestEFull` and `hconj` coincide. Sound in principle
  (rank preserved by a fixed column permutation; squared-Frobenius loss invariant under a fixed
  orthogonal column permutation if absorbed into `B`/`QL` coherently). Cost: a global convention shift;
  must relabel every appearance of `B`, `prod`, endpoint frames, and theorem statements coherently.
- **R4 — re-architect** so the final `Φ` consumes pivot-aligned coordinates directly (distinct threshold
  vs pivot residuals). Robust, broadest.

## Leaf-tide action taken

- Did NOT fabricate a proof of the false conjunct. `hproducer` stays the precisely-stated `sorry`.
- Updated the in-file note at the `hproducer` `sorry` (DeepestGaugeConstruction.lean ~2060) to record the
  CONFIRMED obstruction (replacing the now-refuted "π_J should cancel" optimism).
- Build stays green; `deepestEPivot_regSlice_fderiv` stays clean; the gate-theorem axioms are unchanged
  (`framedParams_split_eq_frame_raw` / `deepest_gauge_construction` still carry `sorryAx` from this gap +
  the 2 L≥3-interior sorries, exactly as at the merge base).

## Files
- `codex/hproducer-pij-{prompt,answer}.md` — index-algebra adjudication (FACT 2).
- `codex/hproducer-repair-{prompt,answer}.md` — repair-route ranking (R3 killed; R1/R2 sound).
- `codex/pij_blockcheck.py` — the reproducible numeric witness (FACT 3).

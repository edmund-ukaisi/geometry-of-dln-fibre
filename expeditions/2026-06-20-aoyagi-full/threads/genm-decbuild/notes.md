# genm-decbuild — the decorated (S,J) recursion → `(□)`

**Seat:** formaliser (tide). **Branch:** `genm-decbuild`. **Base:** `expedition/aoyagi-full` @ `9835fedf`.
**Goal:** prove `RouteMBoxThresholdFinite M ∀M` = `(□)` via the DECORATED recursion. Module:
`DLNFibre/DLN/RLCT/Validate/RouteMSJDecoratedRec.lean`.

---

## T0 — DONE. `(□)` PROVED MODULO one stated Prop `DecoratedPeelStep`. (checkpoint)

### Architecture decision (the re-architecture of the R1-UPPER endgame)

`decorated_peel_step` was prose only. T0 makes it a real Lean object and proves everything above it.

**The sole gap `Prop`** (stated, unproved — the ONLY open analytic content of `(□)`):

    def DecoratedPeelStep : Prop :=
      ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
        (∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') →
        DecoratedBoxThresholdFinite (SJDecoration.trivial M)

Read: for a ≥3-width chain, GIVEN box-finiteness of every ONE-SHORTER chain (the strong IH the arity
recursion supplies), the TRIVIAL decoration on `M` is finite below `carrierThreshold M = ½·minAdm M`.

**Why this shape (design rationale, for the reviewer + later tiles):**

- **Faithful / non-overclaiming.** Phrasing the conclusion `∀ D, DecoratedBoxThresholdFinite D` (any
  decoration) is FALSE — `SJDecoration` is a fully general carrier (arbitrary `Z`,`dom`,`ctx`,`jac`); a
  junk decoration diverges. So the driveable, TRUE statement quantifies the conclusion over the specific
  `trivial M` decoration only. The single-peel a/b/c decomposition lives INSIDE the eventual proof of
  this Prop, not in its statement.
- **Conclusion via `DecoratedBoxThresholdFinite (trivial M)`, not `RouteMBoxThresholdFinite M`.** Logically
  equivalent (banked `decoratedBoxThresholdFinite_trivial_iff`), but phrasing it as the decorated predicate
  is what makes the prover UNFOLD the decoration and peel it — i.e. forces the DECORATED route, not the
  gammaPeel/803 route.
- **Descends on chain arity via `redChain` (one fewer layer) — NON-circular.** The IH gives box-finiteness
  of all one-shorter chains; ONE peel at the binding cut `u★` reduces `M` (arity L+3) to `redChain u★ M`
  (arity L+2), closed by the IH. No internal recursion needed inside the proof of `DecoratedPeelStep`:
  the single peel + one-shorter IH suffices per chain. This matches the recon-map's non-circularity claim.

**Driver + composition (all sorry-free, forced-`#print axioms` clean-three `[propext, Classical.choice,
Quot.sound]`):**

- `decoratedPeelStep_imp_sjStepHyp : DecoratedPeelStep → SJStepHyp` — via banked
  `decoratedBoxThresholdFinite_trivial_iff`.
- `routeMBoxThresholdFinite_of_decoratedPeel : DecoratedPeelStep → ∀L ∀M, RouteMBoxThresholdFinite M`
  = `(□)` MODULO the Prop. Reuses the banked wrapper `routeMBoxThresholdFinite_of_step` (strong induction
  on arity; `L=1` base = banked `sjBase1_freeMatrix`).
- `gammaPeelIntegral_lt_top_of_decoratedPeel : DecoratedPeelStep → <exact 803 goal>` — via banked bridge
  `sjJointResolution_of_boxThresholdFinite`. Shows `sjJointResolution:803` OBSOLETE / retro-fillable;
  `803` itself UNTOUCHED (controller-owned route).

### Note on T5 (terminal wiring) under this shape

With `DecoratedPeelStep` phrased as above, the driver's arity-2 leaf is already the banked free-matrix
Morse `sjBase1_freeMatrix` — the single peel + one-shorter IH close each ≥3-width chain WITHOUT reaching
a monomial terminal. So the banked terminal (`sjLoss_terminal_lintegral_lt_top`, GAP 3) is needed only
INSIDE the eventual proof of `DecoratedPeelStep` if the block-split regime B produces a monomial leaf
directly (T4). GAP 3 is therefore folded into discharging `DecoratedPeelStep`, not a separate open gap.

### What's banked and USED here
- `decoratedBoxThresholdFinite_trivial_iff` (RouteMSJDecorated), `SJStepHyp`/`routeMBoxThresholdFinite_of_step`/
  `sjBase1_freeMatrix` (RouteMSJResolution), `sjJointResolution_of_boxThresholdFinite` (RouteMSJJointReduce).

### Remaining gap after T0
`DecoratedPeelStep` (one stated Prop). Later tiles: T2 analytic-`R` `rowMix`, T3 radial wiring, T4
block-split regime A/B (`c'=pq/2` boundary), which together PROVE `DecoratedPeelStep`.

# Thread 06 — R5 bundle completion (Flat π / fibre bundle over rankROpen)

**Branch:** `expedition/rlct-bridge-06-bundle-completion` (from `origin/dev` = `e2fbf7fb`), own worktree.
Build via `scripts/lb DLNFibre`. BLIND to the aoyagi `RLCT/*` effort.

## State of the art read (banked on dev)

- **S5 capstone** `FibreBundleHeadline.reducedFibre_existsOverBaseProductChartAt_rankEq`: chartwise
  over-base local product + flatness over the NAMED base map `schurToDsigAt`. Two open items spelt out:
  (i) projection compatibility — `schurToDsigAt` is the pullback of `mult`'s projection (NOT proved);
  (ii) R1 — target-side overlap cocycle for a GLOBAL Flat π / FiberBundle (NOT proved).
- **S4b** `FibreOverBaseTriv`: `schurToDsigAt = awayCongr(gauge) ∘ schurToDsig`; the over-base triv
  `chartDsigAt_schurLocTensorEquiv` and chartwise flatness `chartDsigAt_flat_over_schurLoc` are LANDED.
- **Atlas (thread 23)** `FibreBundleLocallyTrivialFull.PivotLocalProductAtlas`: scheme open-cover,
  per-pivot `LocalTrivializationDatum`, PAIRWISE BASE-SIDE overlap cocycle (round-trip, base-norm,
  overlap-restrict) + `transitionFactors` (deep chart cancels → base-algebraic). NOT target-side.

## KEY STRUCTURAL FIND (the unblocker for projection compatibility)

`schurToDsig` (top-left, `ChartPhiSubstitution`) is `IsLocalization.liftAlgHom` of
`chartPhiSchurAeval = aeval chartPhiVarSub`, and **`chartPhiVarSub` sends each Schur generator to the
matching entry of `multPoly d`** (the generic product = the comorphism of `mult`):
  - `chartPhiVarSub (Sum.inl (i,j)) = algebraMap(mk_Σ(multPoly (castLE i)(castLE j)))`
  - `Sum.inr.inl (i,b) ↦ multPoly (castLE i)(natAdd r b)`; `Sum.inr.inr (a,j) ↦ multPoly (natAdd r a)(castLE j)`.
So `schurToDsig` is intrinsically built from `multPoly`/`multComap` — projection compatibility is a
GENUINE factorization through `multComap`, reusing `multComap_X` + the existing `chartPhiVarSub` defn.
This avoids Codex's trap D (proving more theorems over schurToDsigAt that never mention multComap).

## Codex scoping verdict (xhigh, scoping-answer.md)

- A: projection compatibility reachable as a LOCAL ALGEBRA FACTORIZATION (equality of AlgHoms
  `MvPolynomial (target Schur block) → Away(chartDsig)`), via localization ext + `MvPolynomial.algHom_ext`
  on target coordinate vars. Obstruction = matching the pivot-det / Schur reconstruction to multComap
  after quotient/localization — but our find shows it's already definitional via chartPhiVarSub.
- B: target-side overlap cocycle is a DOUBLE-LOCALIZED object; reachable as PAIRWISE data, not a bundled
  triple cocycle.
- C ranking: (1) projection factorization [very high / medium] → build FIRST; (2) clean chartwise-flat
  headline naming the residual [high / low]; (3) target-side pairwise overlap [high / med-high];
  (4) global Flat π [highest / high] = roadmap ceiling.
- D trap: theorems over schurToDsigAt with no multComap = vacuous wrt the geometric projection.

## Plan

1. **Projection compatibility (PRIMARY).** New module `Core/FibreProjectionCompat.lean`:
   - `schurVarToTarget : SchurVar → MvPolynomial (Fin d_last × Fin d_0) k` (Schur block coord ↦ target
     matrix entry variable X(row,col)), an AlgHom `targetSchurEmbed`.
   - Show `chartPhiSchurAeval = (descend-localize) ∘ multComap ∘ targetSchurEmbed` (AlgHom equality).
   - Lift to `schurToDsig = localizedMultComap ∘ (targetSchurEmbed localized)`; carry to `schurToDsigAt`
     via the gauge `awayCongr`. Honest statement: `schurToDsigAt` factors through `mult`'s comorphism.
2. **Target-side pairwise overlap** (SECONDARY, if budget) — conjugate base-side overlap through the
   per-pivot trivializations to a double-localized `targetProductOverlapTransition` w/ pairwise laws.
3. **Roadmap** global Flat π as the honest ceiling.

## Log — LANDED

**Item 1 (PRIMARY): projection compatibility — CLOSED.** `Core/FibreProjectionCompat.lean`.
- `chartPhiSchurAeval_eq_comp_multComap` (crux: Φ Schur comorphism = phiSourceHom ∘ multComap ∘ targetSchurEmbed)
- `schurToDsig_comp_localizeSchur` (top-left), `schurToDsigAt_comp_localizeSchur` (every pivot)
- `ProjCompatOverBaseChart` / `projCompatOverBaseChart` (bundles projection-compat + S4b over-base triv + flatness)
- Axiom-clean `[propext, Classical.choice, Quot.sound]`; built first-try modulo a `Type u`→`Type` universe
  fix (the S4b deps pin `k : Type`).

**Item 2 (SECONDARY): target-side transition OBJECT + reusable bricks.** `Core/FibreTargetOverlap.lean`.
- `awayCongr'` (generalized localization transport across an AlgEquiv; banked `awayCongr` needs A≃A) — reusable.
- `overlapElt`/`targetChartLoc`/`overlapTriv` (base→target transport), `chartOverlapTransitionK`(+`_apply`,
  `_trans_symm`), `targetProductOverlapTransition` (the double-localized pairwise R1 transition object).
- All axiom-clean.

**Deferred (honest ceiling, NOT forced):**
- Target-side cocycle round-trip proof: math-immediate from `chartOverlapTransitionK_trans_symm` but
  Lean-infra-blocked — kernel-cost blowup on the reducible double-localized type (pointwise `ext`), and
  missing `AlgEquiv.trans_assoc`/`trans_refl`/`refl_trans` in Mathlib v4.29 (structural). Roadmap in-file.
- Global `Flat π` / FiberBundle over rankROpen — NOT claimed (needs the cocycle + triple-overlap + L2G flatness).

**Gates passed:** `scripts/sorries` = 0; full `scripts/lb DLNFibre` green (3815 jobs); `#print axioms`
(force-elaborated scratch importing full aggregator + both new modules) all `[propext, Classical.choice,
Quot.sound]`; scratch dual-import = no name clash with siblings.

**Engineering notes (for the future infra tide):**
- `restrictScalars k` of a `≃ₐ[sweepSigmaRing]` over an iterated localization triggers SLOW
  `IsScalarTower k sweepSigmaRing (awayOverlap …)` synthesis (~13–23s). Force it into a `letI tower :=
  inferInstance` once (then `restrictScalars` reuses it) + `set_option maxHeartbeats 800000`.
- `@[reducible]` on a double-localized `Localization.Away` type is needed for its instances to fire under
  `awayCongr'`, but makes the KERNEL blow up on any `ext`-style proof over it (heartbeat-invisible). The
  two pulls conflict — the proper fix is a hand-bundled (non-reducible) structure or the missing AlgEquiv
  associativity API.
- `set_option maxHeartbeats N in` goes BEFORE the docstring, not between docstring and decl.

**Files created:**
- `lean/DLNFibre/Core/FibreProjectionCompat.lean`
- `lean/DLNFibre/Core/FibreTargetOverlap.lean`
- `expeditions/2026-06-27-rlct-bridge/threads/06-bundle-completion/statement-card.md`
- `expeditions/2026-06-27-rlct-bridge/threads/06-bundle-completion/codex/scoping-{prompt,answer}.md`

**For the controller:** wire the two new modules into the single-writer `DLNFibre.lean` (append at end;
I did NOT edit it). Suggested import comments are in the report.

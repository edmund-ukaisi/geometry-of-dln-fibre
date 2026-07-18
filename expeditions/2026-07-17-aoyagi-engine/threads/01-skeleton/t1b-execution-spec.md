# T1b execution spec (architect-t02, 2026-07-18; banked verbatim by the controller)

Status at banking: T1a (Defs/Obligations split) green + merged (4211a714b). T1b is the atomic
faithful-carrier struct edit — cascade CONTAINED to 3 engine files (ResolutionTree, EngineDefs,
CanonicalWitness224); no external RootLedger consumers. Mechanical from this spec; executable by
the architect or any fresh formaliser.

## CARRIER (ResolutionTree.lean)
- StepData: ADD `divProfile : Fin numDiv → (Fin L → ℕ)`; DROP `divTilde` field.
- LeafData: already has `divProfile`; DROP `divTilde` field.
- RootLedger: parametrize `RootLedger (L : ℕ)`; fields numDiv, divExp,
  `divProfile : Fin numDiv → (Fin L → ℕ)`, cleared (DROP divTilde).
- rootLedger : ResolutionTree M → RootLedger L — divProfile from the node's divProfile.
- ADD `tildeOf {L} (T : Fin L → ℕ) : ℕ := if h : 0 < L then (haveI : Nonempty (Fin L) :=
  ⟨⟨0,h⟩⟩; Finset.univ.inf' Finset.univ_nonempty T) else 0` (VERIFIED decide-friendly).
  Derived accessors `StepData.divTilde n k := tildeOf (n.divProfile k)` (same LeafData/RootLedger)
  — `.divTilde` reads stay source-compatible.

## T-RULE in stepUpdate (EngineDefs.lean)
Exponent rule UNCHANGED (+= runLen·resCols / resRows·resCols). NEW divProfile via
`setTail T := fun p => if n.layer ≤ p.val then n.cleared else <head p>`.
LOAD-BEARING INDEXING (trace-S 1-indexed ↔ Lean layer 0-indexed): tail iff `n.layer ≤ p.val`.
Verified against ALL trace cross-checks: root case2 (layer 0)→(0,0); (3,3,4) case2 layer 1→(3,0)
[head p=0 = M p.succ = M(1)=3]; (3,3,4) merge layer 1: (1,1)→(1,0).
- case11: `if k = mergeIdx then setTail (n.divProfile k) else n.divProfile k` (head UNCHANGED).
- case12: Fin.snoc; newT head INHERITED = parent's divProfile mergeIdx (dite-guarded); tail J.
- case2: Fin.snoc; newT head = `M p.succ` (RESET to widths M^(i+1)); tail J.

## COHERENCE (the T4 brick — NOT baked in at T1b)
divExp = Mval(divProfile) at every record — verify by `decide` on witnesses:
(2,2,4) leaf (0,0)→4; (3,3,4) merge (1,1)→(1,0) 4→8; case2 (0,0)→9, (3,0)→12.

## WITNESSES (CanonicalWitness224.lean)
StepData ctors: rootNode224 vacuous; mergeNode divProfile 0 = a T with tildeOf = 2 (e.g. ![2,2]).
LeafData ledger fields stay `(stepUpdate…).field` projections + add
`divProfile := (stepUpdate…).divProfile` → rfl holds by structure-eta.
Re-verify canonicalResolution224_arithmetic (IsFullMonomialization now reads the T-rule
divProfile) + footprints clean-three.

## THEN
- T1b-ii: genDivExp field swap (`support : … → Finset` → `genDivExp : Fin numGen → Fin numDiv
  → ℕ`, support = nonzero locus).
- T1c: ConState full-T + genDivExp + chooser TYPE + strike the EngineConstruction razor
  docstring + μ-spine re-verify.

Gates (standing): μ-spine re-verified under the extended carrier; all witnesses updated;
footprints preserved (arithmetic clean-three; forecast + watch +sorryAx); full-aggregator green
before integration-ready claim; STOP-AND-SURFACE if the edit balloons.

---
# T1c execution plan (architect-t02, 2026-07-18; banked verbatim — the last T1 piece)

Contained to EngineConstruction.lean. Checkpoint state: branch clean at 904cc2921 (T1a/T1b/T1b-ii
landed + full-build-verified); nothing half-edited.

1. HOIST setTail to a top-level def (currently a local `let` in stepUpdate):
   `setTail (layer cleared) (T : Fin L → ℕ) : Fin L → ℕ := fun p => if layer ≤ p.val then cleared
   else T p`. Prove `tildeOf_setTail_le (h : layer < L) : tildeOf (setTail layer cleared T) ≤
   cleared` (tail index p₀ = last exists since layer ≤ L−1; value there = cleared; tildeOf = min ≤
   it via inf'_le). ~6 lines, STANDALONE — build FIRST, independent of the struct change.
2. ConState struct: `divTilde : Fin numDiv → ℕ` → `divProfile : Fin numDiv → (Fin L → ℕ)`
   (ConState gains L → `ConState L`); ADD numGen/genDivExp fields (field-only, match StepData).
   Derive `ConState.divTilde k := tildeOf (divProfile k)`.
3. Transitions: stepCase11 updates divProfile i via setTail (was Function.update divTilde);
   stepAppendAdvance snocs divProfile — its μ₂ descent reads only layer/cleared, UNCHANGED;
   stepRollover carries divProfile, UNCHANGED.
4. μ-descent RE-PROOF (the only real rework): pendingCount = #{k | cleared < tildeOf(divProfile
   k)}. pendingCount_stepCase11_lt reworks the erase-argument: merged divisor i leaves the pending
   set via tildeOf_setTail_le (ADD precondition layer < L) + eligibility (i was pending); others
   unchanged. Same erase-card structure as the landed 2B proof. WATCH the Finset filter
   DecidablePred desync (2B sidestep: state the inequality at ONE synthesis point, close by
   defeq). conRel_stepCase11/AppendAdvance/Rollover themselves unchanged.
5. Chooser interface TYPE (needs step-2 divProfile): `IsEligibleMinimalChoice (s : ConState L)
   (k)` = in-range ∧ tildeOf(divProfile k) = J+J₁ ∧ Def-4-minimal (∀ eligible k', divProfile k ≤
   divProfile k' componentwise). Docstring cites the depth-3 verdict: the chooser's obligation is
   COMPARABILITY-PRESERVATION, not value-protection ((2,2,2,2) node (3,0,1): wrong pick (2,1,0)
   incomparable with (1,1,1); min 3 under both). Proofs at T4.
6. STRIKE the EngineConstruction:15 razor docstring ("stores ONLY what the measure reads" + the
   derivable-data line).

GATE: μ-spine re-verify (4 conRel lemmas clean-three); full-aggregator green. FALLBACK (tripwire):
if the descent lemmas don't close in 3-4 attempts, `git checkout` the file (clean revert to
904cc2921) — no half-cascade, then STOP-AND-SURFACE.

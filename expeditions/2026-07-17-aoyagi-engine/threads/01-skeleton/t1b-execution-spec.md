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

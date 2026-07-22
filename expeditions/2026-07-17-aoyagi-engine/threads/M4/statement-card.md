# Statement card — M4: the (★) pivot-preservation family (seats L6 + M4B, 2026-07-23)

All refs `lean/DLNFibre/DLN/Aoyagi/PivotPreservation.lean`, namespace
`DLNFibre.DLN.Aoyagi.PivotPres`, @ 1faf51a14 (canonical). Status: sorry-free; every headline
force-elaborated `[propext, Classical.choice, Quot.sound]`; cordon OK; fidelity review in flight
(rev-M4).

**Claim (the (★)).** Along a real root→leaf branch of `buildTree d (conOracle d) conRoot`, the
per-step coordinate change `stepMapRaw = blockBlowupMap center pivot ∘ edgeShearRaw` (blow-up
outermost) has the property that a DEEPER step FIXES an EARLIER step's pivot corner — so in the
telescoped chart Jacobian each partial `pathMap((stepMapList).drop(i+1)) u` agrees with `u` at
that pivot. This is the producer of L5's Jacobian-collapse (`FoldRealizes` clause 3).

## Inventory (9 atoms A1→A5 + the single-step (★) + the consumer interface)

- A1 (blow-up fixed points; seat-L6): `blockBlowupMap_apply_pivot`, `_fixes_offCenter`,
  `_fixes_of_pivot_or_offCenter`.
- A2 (disjointness omega cores; seat-L6): `cornerToFlat_notMem_widthBlock`, `_rowBlock`.
- A3 (seat-L6): `divBirthInv_of_isRealBranch`.
- A2-pkg (seat-L6): `canonCenterOf_disjoint_or_pivot`.
- A4 (shear half; seat-M4B): `blockShear_fixes_of_displacement_zero`,
  `edgeShearRaw_fixes_of_displacement_zero`, `shearφ_zero_of_ledgerCorner` (clause (III)
  extracted unconditionally via `foldRegion_eq_univ`), `edgeShearRaw_fixes_ledgerCorner`.
- A4(i) persistence (seat-M4B): `divBirthCoord_persists_{stepCase11,stepRollover,
  stepAppendAdvance}`, `divBirthCoord_persists_conOracle`, `IsLedgerCorner` (def),
  `isLedgerCorner_persists_step`.
- Single-step (★) (seat-M4B): `stepMapRaw_fixes_parentLedgerCorner`.
- A5 glue / consumer interface (seat-M4B): `pathMap_fixes`, `childStateList` +
  `length_childStateList`, `isLedgerCorner_childState_persists`,
  **`foldSuffix_fixes_ledgerCorner`** (HEADLINE, form A), `canonPivotOf_isLedgerCorner_conOracle`
  (sub-fact).

## Proved / Assumed / Cited / Deferred

- **Proved (unconditional):** everything above, from the banked engine + Mathlib; blow-up and
  shear halves both discharged. The region guard `∀u∈V` collapsed to `∀u` (`foldRegion_eq_univ`).
- **Assumed (headline hypotheses, faithful):** `P.IsRealBranch e`; `IsLedgerCorner … c₀` (the
  ledger-corner restriction excluding the rollover falsity).
- **Cited:** none.
- **Deferred (named):** (i) the jacWeight telescoping = seat-L3T2's (B) adapter; (ii)
  `canonPivotOf` is-`some` at non-rollover steps (the sub-fact's hypothesis; existence side with
  seat-L3T2 — possible follow-up `canonPivotOf_isSome_of_nonrollover`); (iii) the RLCT = ½·codim
  reading stays the cited Aoyagi interface.

## Structure & ideas observed

The load-bearing invariant is birth-corner PERSISTENCE (an immutable ledger entry rides
`Fin.castSucc` through every `snoc` birth, verbatim through merge/rollover) composed with
clause-(III) shear-vanishing — making "deeper fixes earlier" a pure ledger-membership fact.
KEY FINDING: the unrestricted coordinate (★) is FALSE at rollovers (canonPivotOf = none ⟹
arbitrary stored pivot, stepMapRaw = id; a deeper blow-up can move it; harmless only because
rollover jexp = 0). Robust forms: the ledger-corner-restricted coordinate (A) [built] and the
jacWeight-level (B) [the consumer adapter]. Route: R2 bridge-free; persistence extracted from
DivBirthInv_conOracle_stepChildren's mechanism.

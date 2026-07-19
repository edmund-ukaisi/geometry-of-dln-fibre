# Statement card — o5_core §4: tStar realized as a t̃=0 leaf divisor

**Status:** sorry-free (awaiting reviewer fidelity check).
**Pinned commit:** `423a5c547` (branch `expedition/aoyagi-engine--t06-s4`).
**File:** `lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean`.
**Axioms:** `tStar_realized`, `o5_core_realized` both `[propext, Classical.choice, Quot.sound]`
(forced `#print axioms`, clean-three, no `sorryAx`).

## Claim (cert-o5-realization.md §4 + §3 composed)

The `Mval`-minimizer `tStar M` (proven `Clearable M (tStar M)` in §3) appears as a `t̃ = 0` analytic
divisor profile at some leaf of the deterministically built tree, PROVIDED all widths are positive.
Composing with the §3 read-off, `minAdm M` is a divisor exponent of some leaf (`o5_core_realized`, the
move-at-landing target for `o5_core`).

**A HYPOTHESIS WAS ADDED (accepted finding).** The statement is FALSE at a zero width: `hMpos : ∀ i, 0 < M i`
is required. Witness `M = ![2,2,0]`: `tStar M = (2,0)` but `widthMinUpto M 2 = 0` forces immediate rollover
at layer 1, so the only `t̃=0` divisor is `(0,0)`; `(2,0)` is never realized (verified: integer sim + the
Lean `conOracle` trace; two decorrelated Codex consults found the same, witness `![1,1,0]`). `hMpos` matches
the divergence half's form (`RouteMAchieverFullHNoFree`) verbatim. Downstream re-signature (`o5_core`,
`o5_realization`, `resolutionOf`) joins the move-at-landing batch (controller ruling, tick post-195).

## Lean signatures

```lean
theorem tStar_realized (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divProfile k = tStar M

theorem o5_core_realized (M : Fin (L + 1) → ℕ) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divExp k = minAdm M
```

## English gloss

- `tStar_realized`: the chosen `Mval`-minimizer `tStar M` is a `t̃=0` leaf-divisor rank profile of the
  built tree (`tStar M ∈ realizedProfiles M`), when widths are positive. MINIMIZER-ONLY: this is `tStar`,
  NOT general `Clearable-Adm` (that is R7, `realizedProfiles_eq_clearableAdm`).
- `o5_core_realized`: `minAdm M` is an accumulated divisor exponent of some leaf — the value the RLCT
  payoff needs. Follows from `tStar_realized` via `IsFullMonomialization` (`divExp = (Mval·).toNat`) +
  `Mval_tStar_eq` (`Mval (tStar M) = minAdm M`).

## Proof architecture (cert §4, both decorrelated Codex consults)

A single `conRel`-WF induction (`realize_aux`) carrying the 3-phase invariant `SteerInv M a s :=
OracleInv ∧ NumDivInv ∧ (SteerPre ∨ SteerAnchored ∨ SteerDone)`:
- **SteerPre** (pre-birth): head is the running-min envelope; `cleared ≤ a^layer`; levels `< cleared` occupied.
- **SteerAnchored** (post-birth): the anchor `A` has profile `cut a layer q` (head `= a`, flat tail `q`);
  the whole suffix is strictly below the envelope; **every level `≤ a^layer` is occupied (LowCover)** — the
  load-bearing strengthening over the cert's anchor-only form, both consults; `a^layer ≤ q < widthMinUpto layer`;
  `A` is landed (`q = a^layer`) or pending (`q = a^{layer-1} > a^layer`, `cleared ≤ a^layer`).
- **SteerDone** (terminal): the anchor's profile IS `a`, level `0`.
- Steering: at a case-1 node take case-1(1) iff target `> a^layer`, else case-1(2); rollover/case-2 forced.
- Pull brick (case-1(1), `f = A`): `A` is pending; LowCover forces `cleared = a^layer` (else level
  `cleared+1 ∈ occ` undercuts `target = min occ`); `setTail` lands `A` as `cut a layer (a^layer)`. NOT
  `step1_dominates` — the o4 domination machinery is used only indirectly via `OracleInv` preservation.

## Supporting lemmas (all sorry-free, same file)

`leafOfState_carries` (t̃=0 divisor → analytic leaf profile), `childLeaves_subset` (existential navigator),
`widthMinUpto_pos`, `clearable_suffix_lt_runMinWidth` (post-birth suffix `< envelope`), `cut`, `cut_succ_self`,
`SteerPre`/`SteerAnchored`/`SteerDone`/`SteerInv` (defs), `conOracle_terminal_le` (cone-good terminal ⟹
`L ≤ layer`), `SteerInv_conRoot` (base), `exists_steered_child` (phase-maintenance: rollover / case-2 /
case-1(1) / case-1(2)), `realize_aux` (the WF fold).

## Hypotheses / scope

- `hL : 0 < L`, `hMpos : ∀ i, 0 < M i` (both genuinely needed; `hMpos` new — see above).
- MINIMIZER-ONLY (naming pin honored: `*_realized`, never `*_complete`/`*_eq_Adm`). Claims only that
  `tStar` (the minimizer) is realized, NOT `realizedProfiles = Adm` (false) or `= Clearable-Adm` (R7).
- The `⊆` lower bound (`minAdm_le_terminalExponents`) is unaffected by `hMpos` — width-free.

## Fidelity check for the reviewer

1. `tStar_realized`'s statement is `tStar M ∈ realizedProfiles M` (an ∃-leaf carrying `tStar M` as
   `divProfile`) — verify it matches cert §4's minimizer-only ⊇ claim, not the full R7.
2. `hMpos` is genuinely required and correctly scoped (the `![2,2,0]` counterexample) — verify the
   hypothesis is neither too weak (statement false) nor gratuitously strong.
3. `SteerInv`'s three phases + LowCover faithfully transcribe cert §4 / the consults — verify the
   invariant is not vacuous and the landed/pending disjunction + LowCover are the intended machinery.
4. `o5_core_realized` composes via `isFullMonomialization_buildTree_conRoot` + `Mval_tStar_eq` — verify
   the arithmetic chain `divExp = (Mval tStar).toNat = minAdm`.
5. Reused banked lemmas (`OracleInv_conOracle_stepChildren`, `NumDivInv_conOracle_stepChildren`,
   `chooseMin_spec`, `conOracle_terminal_leaf`, `divTilde_stepAppendAdvance_*`, `tildeOf_setTail_eq`) are
   the banked defs — verify no redefinition.

## Composition note (move-at-landing, controller-owned)

`o5_core` (`EngineConstruction:2608`) and `o5_realization` (`EngineObligations:64`) are stated at general
`M` + `hL` only; they need `hMpos` threaded (the achievability half is false at zero widths). This is the
move-at-landing batch: `o5_core` migrates here (its sorry deleted), `EngineObligations` imports
`O5Realization`, and `o5_core`/`o5_realization`/`resolutionOf`/the driver re-signature with `hMpos` — one
atomic batch under the full-batch gate. Controller-owned (this seat does not edit those files).

# P2.d capstone — reviewer verdict (decorrelated audit + Phase-2 boundary re-gate)

**Reviewer:** controller-spawned decorrelated audit (fidelity + soundness), blind to `expedition/aoyagi-full`.
**Targets (committed `7b43aaef`):**
- `lean/DLNFibre/Core/RingTheory/Determinantal/LocalTriviality.lean` — the abstract predicate.
- `lean/DLNFibre/Core/FibreZariskiLocalTriviality.lean` — the DLN instance + new cover lemma.
**Decorrelated Codex (gpt-5-codex, xhigh):** `threads/p2d-review/codex-fidelity-{prompt,answer}.md` — independent PASS-WITH-NITS, converged on the same two substantive points.

## VERDICT: PASS-WITH-NITS

Sound and faithful. Lean axiom-clean, the new cover lemma correct on both inclusions, no silent global-bundle
over-claim. The two nits are **prose-precision** (report-only, no signature change); one is shared verbatim with
the sibling `FibreBundleHeadline`. No fidelity or soundness defect.

## Independent re-gate (the distinct deliverable) — GREEN

- **Full aggregator:** `scripts/lb DLNFibre` → `Build completed successfully (3834 jobs)`, exit 0 (warm-replay
  confirm against unchanged source `bde23630`; only `longLine` style warnings, no errors). Earlier from-scratch
  run this session also hit 3834 green.
- **Sorries:** `scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- **Axioms:** `#print axioms reducedFibre_isZariskiLocallyTrivialAffineProduct` and
  `#print axioms Algebra.IsZariskiLocallyTrivialAffineProduct.overlapTransition_trans_symm` each →
  `[propext, Classical.choice, Quot.sound]`. (Also checked: `…overlapTransition_symm`,
  `iUnion_pivotDatum_basicOpen_eq_rankROpen` — same clean set.)
- Box note: a sibling aoyagi build was on the box (load ~9–16); the warm `.lake` let the confirm **replay**, not
  rebuild — no contention, no manual `pkill`, no `cp -al` warm (lessons DA1/DA2).

## Per-question findings

### Q1 — name = content / fidelity. FAITHFUL (one NIT + one clarity NIT)
- Predicate has exactly three fields (`ι`, `chart`, `cover`). "Zariski" (principal opens `D(f)` in
  `PrimeSpectrum`), "affine product" (`M = SchurLoc ⊗_k sweepFibreRing`, literal tensor algebra; per-chart
  `≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre`), "locally trivial" (principal-open cover + per-chart trivializations) each
  justified by the actual data.
- **NIT (Base vs BaseLoc):** confirmed `Base = sweepSigmaRing = O(Σ^r)` is the **total/source** ring
  (`Spec Base = Σ̄^r`), `BaseLoc = SchurLoc` the fibration base direction. By standard AG convention "Base" for
  the total space is misleading. NOT a math defect — `AtlasTransition`/`LocalTriviality`/instance docstrings all
  explicitly flag the distinction. A cleaner name is `TotalRing`/`AmbientRing` — but renaming the predicate
  parameter is a **signature change = fidelity edit, escalate to operator**, not a silent simplification. Keeping
  the documented name is acceptable.

### Q1c — derived cocycle is on the `trivK`/`M` presentation, NOT the over-base `fibreModel.triv` product
- **Confirmed (verified at the instance level).** `AtlasFibreChart` carries `trivK : ≃ₐ[k] M` and
  `fibreModel.triv : ≃ₐ[BaseLoc] BaseLoc ⊗_k Fibre` as **independent fields** — nothing in the structure ties
  `trivK` to the `k`-restriction of `fibreModel.triv`. In the DLN instance they are two distinct named equivs:
  `trivK = chartDsigAt_tensorEquiv` (bare `≃ₐ[k]`), `fibreModel.triv = chartDsigAt_schurLocTensorEquiv`
  (`≃ₐ[SchurLoc]`). The derived `overlapTransition` conjugates through `trivK` only, so the cocycle lives on the
  `M`/model side.
- **Does the lemma docstring oversell? NO.** `LocalTriviality.lean:113-114` says the round-trip is on the
  "**target/model overlap presentations**" — which correctly names the `trivK`/`M` side; it does **not** claim an
  over-`BaseLoc` cocycle or that `fibreModel` participates. So no false statement.
- **Actionable (additive clarity, controller's call):** the controller may add one line to the
  `overlapTransition_trans_symm` docstring (`LocalTriviality.lean:112`) stating the cocycle is on the bare-`k`
  `trivK`/`M` presentation and is **decoupled** from `fibreModel.triv` (the over-`BaseLoc` product), so a reader
  does not assume the cocycle is an over-base-product cocycle. Report-only; not required for PR.

### Q2 — non-vacuity. REAL as "predicate satisfiable / structure inhabited"; "geometric witness/realized" wording risks the nonempty-open reading (NIT)
- Verified the instance type-checks at **`U = rankROpen d r`** (not `∅`, not `⊤` — the `cover` field's type is
  `rankROpen d r = ⋃ …`, confirmed by a type-pin probe) and **`ι = PivotDatum d r hp hq`** (not `Empty`, by
  `rfl`). The degenerate `ι = Empty, U = ∅` reading is excluded for this instance.
- The instance is an **unconditional term** (no `(P, hP)` hypothesis), so it genuinely proves the predicate's
  structure type is inhabited / satisfiable — axiom-clean. Legitimate "the predicate is non-vacuous."
- **NIT — Q2a precision.** There is **no in-file/nearby proof that `rankROpen ≠ ∅`** (grep: only the rank-locus
  bridge `mem_rankROpen_iff_rank_universalMatrixResidue_eq`, no `∃ P, P ∈ rankROpen`). The **sibling**
  `FibreBundleHeadline.lean:289-293` draws exactly this line ("do NOT exhibit … a nonempty `rankROpen` … not an
  existential non-vacuity proof"); the capstone's "geometric witness / realized" wording blurs the same line.
  Honest reading: *axiom-clean inhabited instance ⟹ the predicate is satisfiable; nonemptiness of `rankROpen`
  (that the local triviality is over a nonempty open) is not proved here.* For `r = 0`, `rankROpen = ⊤` (empty
  minor det `= 1`), nonempty iff the spectrum is; for generic feasible `r` a rank-`r` normal-form prime should
  witness it — neither formalized.

  **Instance-file docstring file:lines to soften** (`FibreZariskiLocalTriviality.lean`) — controller applies:
  - **L15:** "as a genuine, **non-vacuous** instance of it" → "as a genuine instance of it" (or "an axiom-clean
    inhabited instance").
  - **L39:** section header "## **Non-vacuity** (the point)" → "## Inhabitation / satisfiability".
  - **L44–45:** "the genuine **geometric witness** that the abstract predicate is **non-vacuous** — '…' is
    **realized** by the DLN bundle." → "an axiom-clean **inhabited instance**: the abstract predicate is
    **satisfiable** by the DLN bundle (nonemptiness of `rankROpen` is a separate, unproved claim)."
  - **L129:** "(P2.d capstone, **non-vacuity witness**)" → "(P2.d capstone, inhabited-instance witness)".
  - **L135–136:** "the **genuine geometric witness** that the abstract predicate is **non-vacuous**." → "an
    axiom-clean inhabited instance: the predicate is satisfiable by the DLN bundle."
  - **L152:** section header "## **Non-vacuity** witnesses" → "## Inhabitation witnesses".
  (The predicate file `LocalTriviality.lean` has NO "non-vacuity"/"geometric witness" wording — clean.)

### Q3 — new cover lemma `iUnion_pivotDatum_basicOpen_eq_rankROpen`. SOUND
- Both inclusions check out. `≤`: each `PivotDatum I`'s chart element is literally the selector chart at
  `(I.s, I.t)` (`subset_iUnion_of_subset`). `≥`: `p ∈ basicOpen (chartDsigAt st.1 st.2)` lifts via
  `pivotDatumOfMemBasicOpen` to `I` with `pivotElt I = chartDsigAt st.1 st.2`, then `pivotElt I = chartDsigAt
  I.s I.t` (**genuinely `rfl`, probe-confirmed**) places `p` in `I`'s chart.
- **Non-injective selector handling correct:** `pivotDatumOfMemBasicOpen` takes no injectivity hypothesis — a
  non-injective selector forces `chartDsigAt = 0` (repeated row/col ⟹ det `= 0`), so its `basicOpen` is empty and
  no PivotDatum is requested; injectivity is *derived* from membership
  (`injective_of_mem_basicOpen_chartDsigAt`). The result honestly equals `rankROpen` (built from the banked
  selector cover `iSup_pivot_basicOpen_eq_rankROpen`), not a weaker set.

### Q4 — over-claim check. CLEAN
- No field/theorem asserts a global `Flat π`, triple-overlap cocycle, or scheme-level gluing. Only the **2-fold**
  derived round-trip (`overlapTransition_trans_symm` / `_symm`). Docstrings accurately disclaim the global
  `Flat π` / triple-overlap (`FibreZariskiLocalTriviality.lean:60-61`, "stays roadmapped"), and the
  not-a-Mathlib-`FiberBundle` (topological) point. The `U`-load-bearing / "bundle over the closure is false"
  caveats are correct.

### Wording scrub (banned list)
- Zero banned-wording hits in either target file. ("(the point)" at L39/L103 is object-level framing, not the
  banned "the whole point is" selling phrase — though L39's header is folded into the Q2a softening above.)

## Recommendation
**PASS-WITH-NITS — no fix required before PR; the two nits are report-only precision.** If hardening before the
Phase-2 PR (cheap, prose-only, no signature change for Q1c/Q2a):
1. Soften the six `FibreZariskiLocalTriviality.lean` "non-vacuity / geometric witness / realized" sites (L15, 39,
   44–45, 129, 135–136, 152) to the inhabited/satisfiable reading + co-locate the "`rankROpen ≠ ∅` not proved
   here" caveat (mirroring `FibreBundleHeadline:289-293`).
2. Optionally add one decoupling line to `overlapTransition_trans_symm`'s docstring (`LocalTriviality.lean:112`).
3. The `Base → TotalRing` rename is a **signature change** — escalate to operator if desired; not a silent edit.

No Lean edited / no commit / no PR. Only files written: this note + the two Codex consult artefacts under
`threads/p2d-review/`.

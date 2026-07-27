# Synthesis — `aoyagi-engine` (CLOSE-OUT)

_Close narrative for the `(3,3,4)` landing. Branch `expedition/aoyagi-r2ov-integration` @ `4399f4c7a`._

## THE RESULT

The paper's headline **`rlct = ½·codim`** ("DLNs are mildly singular") is established in honest Lean at
the coupled `(3,3,4)`, `B = 0` instance, **cite-free and monument-free**, kernel-gated clean-three:

> `dln_rlct334_eq_half_codim : rlctGlobal (lossDLN ![3,3,4] 0) = ½·(codimRealFibre ![3,3,4] 0).toNat`
> — and `= 4`, since the geometric codimension is `8`.

Both halves are built from the geometry, neither from a citation:

- **≤ (upper)** — `dln_rlct334_le_half_codim`: a **single certified change-of-variables chart** (`chart334`)
  gives `rlctAt ≤ chartMin/2 = 4`. This is the Watanabe universal `rlct ≤ ½·codim` for the built object,
  proved from ONE chart (no atlas, no cover, no `θ`). It **replaces** the `cited_watanabe_upper_ax` cite:
  the axiom does not appear in the cone (verified in the `#assert_banked_clean_batch`).
- **≥ (lower)** — `dln_rlct334_ge_four`: the geometric V-lower over the whole-conjugate folded fan (288
  charts covering a neighbourhood of `0`), each chart integrable for every exponent `< 4`. This replaces
  the Aoyagi exact-value cite.
- **transport** — `measurePreserving_eWrap` (the transpose-flatten is a coordinate permutation) discharges
  the sole un-banked input of `coreReduction`, so the equality is on the **actual DLN square-Frobenius
  loss** `lossDLN ![3,3,4] 0`, not only on the core loss.

`le_antisymm` of the two halves is the equality. Axiom footprint of every `(3,3,4)` root is
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `@[cited]` axiom — enforced by the batch gate
in `DLN/RLCT/AxCheck.lean` (a forced `collectAxioms` over each registered root, not a docstring claim).

The whole-cone fidelity review and the equality fidelity review both SURVIVED (Codex-corroborated;
independent recomputation of `codim = 8`).

This is the cite-free `(3,3,4)` INSTANCE of the `aoyagi_learning_coefficient` payoff, obtained **without**
the general `exists_coreResolution` resolution monument (which the general-name payoff still carries).

## SCOPE (elder verdict — stated plainly)

This is a `(3,3,4)` **instance** — a milestone, not the general-`d` destination (charter §0/§1).

- **"monument-free" means the coupled monument was BYPASSED at `(3,3,4)`**, not that Object B was built at
  full generality. The ≥-half reached the value via a from-below sandwich over the folded fan (a
  regular-sequence / sum-of-squares lower bound at the over-vanishing leaves, a single-survivor chain
  bound at the clean leaves) — without the two-sided principal normal form. The general resolution
  `exists_coreResolution` remains `sorryAx` (informational `#print axioms` in AxCheck, off the `(3,3,4)`
  cone). The general-name `aoyagi_learning_coefficient_via_engine` still carries that one `sorryAx`.
- **`(3,3,4)` is `minAdm = 8`, coupled-only** (the value `8` is achieved only on a coupled Kostant
  partition; a row-wise flatten returns the wrong min — settled fork F4). It exercises the corank-2
  coupling but is one dimension vector at `L = 2`, one recursion step. Do NOT read it as general-`d`.
- The equality is **one coupled instance** of `rlct = ½·codim`, not the theorem for all `d`.

## THE ROUTE / ENGINE (reusable, for the next expedition)

The `(3,3,4)` ≥-half was built as a stack whose lower layers are network-free and reusable:

1. **SoS / Tonelli analytic core** — `Core.Aoyagi.MonomialSumSqRLCT`
   (`Core/Aoyagi/MonomialSumSqRLCT.lean`). The RLCT of a monomial-squared times a nondegenerate
   sum-of-squares over disjoint coordinate blocks: `rlctAt(vm²·∑_{j∈Z} u_j²) = min(threshold(vm²), |Z|/2)`,
   via disjoint-block Tonelli (`MeasurableEquiv.piEquivPiSubtypeProd`) + `RLCT.SumSq`. The `|Z|/2 = r/2`
   term is invisible to the divisibility-chain engine and is what makes the over-vanishing leaves reach
   `4`. Network-free, clean-three; the reusable Core deliverable.
2. **Mechanism-agnostic membership spine** — `Corank2OverVanishAssembly334`
   (`.rlctAt_coreGen334_ge_four_of_perchart_integrable`). Abstracts per-chart-per-point integrability of
   the weighted pulled-back loss as ONE hypothesis `hint`, so the two leaf mechanisms (clean via the
   single-entry survivor + chain engine; over-vanishing via the SoS engine) discharge it uniformly. A
   refactor of `mem_localAdmissible_of_sandwich_lt`'s area-formula spine. (Its file docstring still reads
   "STEP-6 SKELETON / tracked hole" — stale text; the theorem is fully proved, which the clean-three gate
   confirms. A close-out doc nit, flagged below.)
3. **Whole-conjugate folded fan cover** — `Corank2NativeFan334` (the born-native fan `nativeFan`, its
   `native_hcover`, the flat leaf family `gFin`) + `Corank2FoldedFamily334` (the folded family `gFold` +
   the 16-way `IsClean` classifier + the `σ_{p1}` per-type straightening). The fan is the whole loss-symmetry
   conjugate of the born blow-up (`blockBlowupMap_conj`), so it is value-correct on all 288 leaves and
   transport-free (W3-clean: no K-orbit / gauge in the RLCT engine).
4. **The two discharge leaves** — `folded_hg_inj` (a.e.-injectivity of the folded chart off its null
   critical set) + `folded_hint` (per-chart integrability over all 288 clean+over-vanishing charts).
5. **The ≥-half** — `OverVanishHeadline334.rlctAt_coreGen334_ge_four` wires (2)–(4).
6. **The ≤-half** — `rlctAt_sumSqFam_le_chartMin_half` (the general single-chart CoV upper) instantiated at
   `chart334`; cite-free.
7. `le_antisymm` → the core equality; `measurePreserving_eWrap` + `coreReduction` transport it to the DLN
   loss.

## RUNWAY

**General-`d` cite-free (headline for all `d`).** Priced SOUND and MONUMENT-FREE at full generality
(compass F13/F14): both monuments are bypassed by the same "one scalar pivot per node" principle — the
VALUE via the pivot-cross single-entry survivor (`Pmat[0][0] = E`, corank-insensitive), the COVER via a
triangular det-1 block-shear (no rational `k×k` inverse). This is **de-risked to detail-at-scale, NOT
built and NOT Lean-inhabited** ("monument-free" ≠ "nearly done"; ~10–16 tides estimated). The inferred,
not-proven surface is a 3-item ledger (charter §3 / compass F14):

- **L1** — the VALUE born-α fed-form invariant (pivot `= E`; the ideal-preservation leaves).
- **L2** — the general-`d` cover completion (the per-leaf native born-α carried in the fan; remaining =
  a per-pivot box-containment brick, engine-native).
- **L3** — the resolution's next-center-coordinate-block realization condition (shares leaves with L1;
  the exact L1 = L3 identity is itself a to-adjudicate item — keep both).
  L1 and L3 are both load-bearing (a snag in either hits the headline) — the build's primary audit target.

The ONE localized residual risk is **step COMPOSITION** (F13): the pivot-adapted fed form is verified at
`(3,3,4)` (one step) and one instance `(3,3,3,2,2)`, but the multi-step / rollover entanglement is
inferred, not derived from the actual `stepUpdate`. General-`d` is gated behind a composition probe (a
deeper-`L` adversarial rollover) + the α-uniformity probe; CLEAN ⟹ detail-at-scale, ENTANGLES ⟹
objects-only general-`d` landing (with the `(3,3,4)` witness). This decision is operator-gated.

**The cited-axiom kill.** The endpoint is `aoyagi_learning_coefficient` cite-free AND sorry-free. Today
`via_engine` is cite-free (no `cited_aoyagi_lower_ax` / `cited_watanabe_upper_ax` in its cone) but carries
`sorryAx` from `exists_coreResolution`. Building L1–L3 (or the narrow k=1 induction, cited only if the
general-`L` induction bites) discharges that one monument and deletes the cite.

**Standing tripwires (carry into the next expedition — each caught a real defect here):**

- **The cert's direction — from-below, not toric.** A toric-LP / Newton-polytope / monomial-ideal reading
  is an UPPER bound on the true rlct (SoS-RLCT is monotone increasing under ideal inclusion), so it does
  NOT certify a lower bound. The `(3,3,4)` over-vanishing "≥ 4" was once double-certified with a toric-LP
  half; the direction was wrong. Corrected to the regular-sequence genuine lower bound. For any rlct/codim
  LOWER bound, verify the cert is from-below (resolution / regular-sequence), never a relaxation.
- **The engine reads the shape, not the name.** A from-below sandwich delivers what its integrability
  engine reads. The divisibility-chain wire collapses `∑bₖ² = b_{k₀}²·U` (`U ≥ 1`) and reads only
  `threshold(b_{k₀}) = ½` — it discards the SoS vanishing. Feeding it the over-vanishing residual caps at
  `½`, not `4`; the `r/2 = 4` lives entirely in the SoS block. Match the RHS shape to the engine
  (chain-shaped → chain wire; product-shaped regular sequence → the SoS/Tonelli engine).
- **The ledger is not the geometry.** The engine hardcodes `resRank := 0`; that a ledger field is `0` is
  not that the geometry is unit-residual. Faithfulness lives in the actual pulled-back loss
  `K∘g = monomial²·unit` with `unit(0) ≠ 0` — derive `bexp`/`k₀` from the concrete pullback, never read
  them off the hardcoded field. A hard `hpull` (a Morse/degenerate residual the ledger does not reflect)
  is the general-`d` summit-fidelity concern.

## LESSONS (from the arc)

**Mathematical / fidelity (caught and closed):**

- **The chain-wire ½-cap** — the "engine reads the shape" tripwire above, caught by ground-truthing
  `MonomialRLCT.lean` against the over-vanishing RHS before feeding it; corrected to the SoS engine.
- **The cover-atom label** — the toric-LP direction miss (the "cert's direction" tripwire), caught by a
  decorrelated Codex red-team of the pen-and-paper's own prior certificate. A "double-certified" verdict
  can still be unsound in a subtle direction; the decorrelated hunt is what exposes it.
- **The eWrap measure-preservation core-vs-DLN gap** — the single-chart upper (`Corank2CiteFree334`) and
  the reduction both carried `MeasurePreserving eWrap` as an unproven hypothesis, so the DLN-loss claim
  was conditional. Closed by `Corank2EwrapMeasure` (route B: a concrete combinator flatten `cFlat`, the
  scattered coordinate permutation `piSymm` matched by `fin_cases`/`rfl`, avoiding the opaque
  `Fintype.equivFin`). The named caveat ("linear coordinate reindex, carried as a hypothesis") sat next to
  the claim until it was discharged — then the unconditional forms landed.

**Process / operational:**

- **A worktree collision** — a seat was spawned into an already-occupied worktree. Isolated worktrees
  per seat is the standing rule; verify a target worktree is free before dispatching.
- **Cold-worktree semaphore-starvation** — a fresh worktree spun up for a tiny task contended on the
  shared build semaphore. Match worktree/build weight to task size; reuse a warm worktree for small edits.
- **The API-death resume** — an agent lost its API connection mid-build; the work resumed from its pushed
  branch. Reinforces the standing rule: push a substantial artifact's branch to `origin` ON COMMIT (a
  backup, integration review unchanged) — an unpushed branch is not banked.
- **The stalled-seat controller take-over** — a stalled build seat was taken over by the controller to
  land the piece. Calibrate on ground truth (re-run the build, `#print axioms`), do not wait indefinitely
  on a silent seat.

**Doc-hygiene nit (for the committing controller):** `Corank2OverVanishAssembly334.lean`'s module + theorem
docstrings still describe the STEP-6 spine as a "skeleton / tracked hole". The theorem is fully proved
(clean-three-gated). The stale status line should be de-staled at commit.

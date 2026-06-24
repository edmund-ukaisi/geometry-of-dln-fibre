# L2 gauge-chart integration map (#120 EPivot correction)

**Thread 21 — scout (read-only git archaeology).** Drives a soundness-sensitive merge the controller
performs. cwd = repo root. Snapshot: `origin/expedition/aoyagi-full` HEAD `82f11058` (2026-06-24).

Register key: **data** = what the diffs/`git` show; **interpretation** = my reading.

---

## TL;DR (the recommendation)

- The two base sorries are **NOT filled on any candidate branch** in the literal base form. PIN1
  (`= id`) is **false-as-stated** and PIN2 is a bare `sorry`. The *completed* lane-work lives on the
  **#120-corrected** branch family (`fm2/deepest-gauge-chart-sub34` and its `fm/deriv-frame-resume`
  descendant), which **restructures** the proof: it changes `framedLayer`, `framedParamsReg`,
  `deepestEPivot` (frame args `P,Q`), and `regResidualPack` (opaque → transparent).
- **SOUNDNESS RISK (confirmed, decorrelated):** the base `deepestEPivot_regSlice_fderiv_id` `= id`
  with the **opaque `Fintype.equivFin` pack** is **not provable as stated**. Any "fill" that proves
  the literal base `= id` against the opaque pack would be **unsound**. The fix is structural (#120),
  not a missing tactic.
- **Cleanest path:** merge **`origin/fm2/deepest-gauge-chart-sub34`** onto the expedition branch. A
  real `git merge-tree` dry-run yields **exactly ONE textual conflict** — `DeepestTelescoping.lean` —
  and it is the *same* `endpoint_telescoping` lane at two completion stages; **take sub34's
  (sorry-free) version**. After the merge, L2 is reduced to **two genuine analytic sorries** (PIN1's
  `deepestEPivot_regSlice_fderiv` #91 frame-sandwich, and PIN2's `framedParams_split_eq_frame_raw`
  cert) — both **in-flight on `fm/deriv-frame-resume`**, both correctly stated.

---

## 1. The two base sorries — who fills them?

Base file `lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean` @ `82f11058`:
**bare `sorry` at line 435** (`deepestEPivot_regSlice_fderiv_id`, PIN1) and **line 530**
(`deepest_loss_squeeze`, PIN2). Confirmed unchanged from the `9e3ce697` snapshot the brief named.

### Scan result (data)

No branch has `DeepestGaugeConstruction.lean` with **fewer than 2** bare sorries at these theorems.
A full scan of every `origin/*` branch found **zero** sorry-free `deepestEPivot_regSlice_fderiv_id`
or `deepest_loss_squeeze` anywhere.

| branch | file present | bare sorries | `deepestEPivot` form | `regResidualPack` |
|---|---|---|---|---|
| `expedition/aoyagi-full` (base) | yes (665 ln) | 2 (435,530) | **OLD** (no frames) | **OPAQUE** (`Fintype.equivFin`) |
| `fm/regslice-id` | yes (665 ln) | 2 (435,530) | OLD | opaque |
| `fm/deriv-pin1` | yes (624 ln) | 2 | OLD | opaque |
| `fm/deriv-pin2` | yes (665 ln) | 2 (435,530) | OLD | opaque |
| `crux2/pin2-prodaux-cast` | yes (341 ln) | 2 | (skeleton) | — |
| `fm-pin1-regabsorb-ift` | yes (271 ln) | 3 | (skeleton) | — |
| `fm2/deepest-gauge-chart-sub34` | yes (907 ln) | 2 (456,632) | **#120** (`P,Q`) | **TRANSPARENT** (`regPivotFinEquiv`) |
| `fm/deriv-frame-resume` | yes | 2 (443,624) | #120 | transparent |
| `fm/deriv-frame-resume-cont` | yes | 2 (443,624) | #120 | transparent |
| `fm/deriv-spec` | yes | 2 (440,544) | (staged) | — |
| `fm2/deepest-gauge-chart`, `fm2/split-reindex`, `g213-pin1-de0`, `g150-*`, `fm2/l2-product-reduction`, `g173-l2-general-v` | **ABSENT** | — | — | — |

**Interpretation.** The `fm/regslice-id`, `fm/deriv-pin*`, `crux2/*` branches are **OLD-form ancestors**
of the base, not fills — they carry the same opaque-pack skeleton and the same sorry. The real fills
were done on the **#120 family** (`sub34` / `fm/deriv-frame-resume`), which moved the geometric content
into new objects. So "the fills exist on un-integrated branches" is true only for the **#120-restructured
form**, never for the literal base statements.

### Where the #120 sorries actually sit (data)

- **PIN1** on `fm/deriv-frame-resume`: `deepestEPivot_regSlice_fderiv` (note: renamed from `_id`) —
  stated as `∃ F : ≃L, HasStrictFDerivAt (reg-slice) F 0` (an **invertible frame factor**, NOT `id`).
  Sorry at line 443 is the genuine **#91 frame-decorated Leibniz sandwich** (analytic atom, in
  progress — recent commits `174cc3f6 prodAux_regSlice_through_first GREEN`, `0067b647 devXZ_mul_corner`).
- **PIN2** on both `sub34` and `fm/deriv-frame-resume`: `deepest_loss_squeeze` is **sorry-FREE** (full
  arithmetic squeeze chain closed), reduced to a single upstream cert
  `framedParams_split_eq_frame_raw` (the "ONE geometric input"), which is the remaining `sorry`
  (line 632 sub34 / 624 frame-resume). Its 4-step fill is documented in-comment: round-trip
  `framedParams(split w) = P·paramsSymm·Q`, `endpoint_telescoping`, B gauge-normalisation,
  `core_comparability_squeeze` (#54).

**Base-vs-branch divergence.** All branches are far from the expedition HEAD (merge-base distances:
exp is **273–462 commits ahead** of each branch's merge-base). They are old lane branches; the merge
question is about *content compatibility*, decided in §3, not raw commit distance.

---

## 2. The #120 EPivot shear-CLE correction + the dE(0)=id fix — what it changes

The correction is **two coordinated structural changes**. It is carried by the `sub34` /
`fm/deriv-frame-resume` family (consolidated by commit `d9c4f780` "#120-complete DeepestSplitReindex +
GaugeConstruction onto fm2"; the verdict commit is `12846aae` "DECISIVE reg-slice-id verdict
(false-as-stated, needs #120 structured-equiv)" and the obstruction cert `2c9c492f`
"regSlice_fderiv_id unprovable as stated (opaque packs)").

### Part A — frame conjugation of `framedLayer` (`DeepestFramedProduct.lean`)

**OLD (base):**
```
framedLayer … X Y Z T  :=  reindex (fromBlocks (1+X) Y Z T)
```
**#120:**
```
framedLayer … P Q X Y Z T  :=  reindex (fromBlocks 1 0 0 0)
                                + P * reindex (fromBlocks X Y Z T) * Q
```
i.e. the deviation `(X,Y,Z,T)` is now **frame-conjugated** by per-layer matrices `P,Q` (added to the
corner base). This threads through `framedParamsReg` (gains `P Q` args) and `deepestEPivot` (gains
`Pf Qf` args). The frames are instantiated at `deepestFrameFamilyP/Q H r B …` = the `deepestPoint`
boundary frames.

**Consequence for the derivative.** Under the frame-conjugate layer, the gauge-zero reg-slice
derivative is **NO LONGER `id`** — it is the **constant invertible frame factor** `F` (boundary
`Pf_first` / `Qf_last` `r`-corner action). Hence PIN1's honest statement is
`∃ F : ≃L, HasStrictFDerivAt (reg-slice) F 0`, and the generic shear-CLE consumer
`regStraightenTotalCLM_equiv_of_regBlock_id` is relaxed from "reg-block = id" to "reg-block =
IsUnit/invertible" (commits `416d76bf`, `9d6dc21c`, `b580ba85`: "_deriv spec corrected from =fst to
the shear-CLE").

### Part B — pack dissolution: `regResidualPack` opaque → transparent (`DeepestGaugeConstruction` + new `DeepestSplitReindex`/`DeepestRegPivotEquiv` atoms)

**OLD (base):** `regResidualPack := (finCongr …).trans (Fintype.equivFin _).symm` — an **arbitrary
cardinality bijection** (the base docstring itself says "the specific index alignment is the open
`_deriv` obstruction (crux2's fork)").
**#120:** `regResidualPack := regPivotFinEquiv H r hr` — a **transparent** `finSumFinEquiv /
finProdFinEquiv` enumeration that routes each `Fin nReg` index to its **actual boundary pivot**
(X_first / Y_last / Z_first). New sorry-free atoms (`DeepestRegPivotEquiv`, commit `b859f0f8` "GREEN,
sorry-free, clean axioms"): `BoundaryPivotIdx`, `card_boundaryPivotIdx`, `regPivotFinEquiv`,
`regBoundaryToRegGauge` (+ `regGaugeDecode` left-inverse for injectivity). With these, "reg-coords ARE
the boundary pivots **by construction**", so `regSlice_fderiv = F` reduces by the cancel + the #91
sandwich (commit `607d5cc1` "step 2: regResidualPack := regPivotFinEquiv (transparent pack)").

### The ~5 consumers of the corrected version (data — `git grep`)

The #120 objects appear ONLY on the #120 family (base file count = 0):
`deepestFrameFamilyP/Q`, `dlnLoss_two_sided_of_frame`, `deepestEPivot_sq_sum_eq_blocks`,
`framedParams_split_eq_frame_raw`, `regPivotFinEquiv`, `regBoundaryToRegGauge`. The corrected
`deepestEPivot`/frame-conjugation is consumed by:

1. **`deepestEPivot_deriv`** — assembles `_contdiff` + the reg-slice derivative (now `F`, not `id`) +
   the relaxed shear-CLE (`regStraightenTotalCLM_equiv_of_regBlock_id` weakened to invertible reg-block).
2. **`deepest_regAbsorb_exists`** — consumes `deepestEPivot` + `deepestEPivot_deriv` to build
   `regStraighten` (the IFT/peel; `e := clmShearEquiv N` invertibility).
3. **`deepest_loss_squeeze`** (PIN2) — `hregval` now reads `deepestEPivot … (deepestFrameFamilyP)
   (deepestFrameFamilyQ) (q.1,q.2.2)`; uses `deepestEPivot_sq_sum_eq_blocks` + `dlnLoss_two_sided_of_frame`.
4. **`framedParams_split_eq_frame_raw`** (PIN2 cert) — identifies the loss matrix's regular blocks
   with the **frame-conjugated** `framedParamsReg` product (instantiated at `deepestFrameFamilyP/Q`).
5. **`endpoint_telescoping`** (`DeepestTelescoping.lean`) — strengthened with `IsUnit P0 ∧ IsUnit QL`
   (boundary-frame invertibility) for the conjugation comparability the squeeze needs.

(`deepest_gauge_construction` / `deepest_gauge_chart_construct` wire all of the above; they are the
ultimate consumers but are form-agnostic given the corrected sub-lemmas.)

---

## 3. Divergence / conflict assessment

The expedition base has the **merged RouteMLayer* + R1-cover + RRR work** layered on top of a shared
ancestor with the #120 family. **Shared merge-base** of `expedition/aoyagi-full` ↔ `sub34` is
**`7e1ab44c`** (2026-06-23 09:57, "#44c/#123 FOLD3: reindex_mul_distrib kernels"), and it **is an
ancestor of the current expedition HEAD**.

### The decisive finding (data): the conflict surface is ONE file

`git diff --numstat 7e1ab44c origin/expedition/aoyagi-full` over the 7 files the #120 work touches:

| #120 file | expedition diverged from `7e1ab44c`? |
|---|---|
| `Core/Matrix/RankNormalForm.lean` | **UNCHANGED** |
| `DLN/…/DeepestFrame.lean` | **UNCHANGED** |
| `DLN/…/DeepestFramedProduct.lean` | **UNCHANGED** |
| `DLN/…/DeepestGaugeBlocks.lean` | **UNCHANGED** |
| `DLN/…/DeepestGaugeConstruction.lean` | **UNCHANGED** |
| `DLN/…/DeepestSplitReindex.lean` | **UNCHANGED** |
| `DLN/…/DeepestTelescoping.lean` | **changed (+89/−15)** |

So the expedition base **never touched** the 6 critical #120 files since the shared ancestor — the
RouteMLayer/RRR/cover work lives in *other* modules. A real `git merge-tree --write-tree`
(`expedition` ← `sub34`) produces **exactly one** `CONFLICT (content)`: `DeepestTelescoping.lean`.
(`fm/deriv-frame-resume` ← `expedition` gives the same single conflict.)

### The single conflict is a stage-mismatch, not a design divergence

- **Expedition side:** `DeepestTelescoping.lean` was touched **only** by commit `e6dcab00`
  "WIP checkpoint before VM rotation" — a partial `endpoint_telescoping` with `hPunit/hQunit`
  hypotheses + unconditional `IsUnit P0 ∧ IsUnit QL`, but a **"REMAINING SYNTACTIC FILL"** comment
  (one-mul-on-defeq-1 friction, unfinished).
- **sub34 side:** the **same** `endpoint_telescoping` lane, **finished** (commit `f449c923`
  "FOLD3 COMPLETE: endpoint_telescoping SORRY-FREE", + 8 more), with a *conditional* IsUnit packaging
  `∀ (hP0 hQL), IsUnit P0 ∧ IsUnit QL`. **The whole file is sorry-free on sub34.**

**Interpretation.** These are the same proof at two completion stages — the expedition WIP is a strictly
*earlier* state of what sub34 completed. **Resolution: take sub34's version wholesale.** Verified safe:
`endpoint_telescoping` has **no call site** on the expedition base outside `DeepestTelescoping.lean`
itself (its only real consumer, `framedParams_split_eq_frame_raw`'s proof, comes in from sub34 too).
The slight signature difference (conditional vs unconditional IsUnit) therefore breaks nothing on the
expedition side.

---

## 4. The cleanest single integration path (recommendation)

**Merge `origin/fm2/deepest-gauge-chart-sub34` into `expedition/aoyagi-full`.**

Order / mechanics for the controller:

1. `git merge origin/fm2/deepest-gauge-chart-sub34` (onto expedition branch).
2. **One conflict — `DeepestTelescoping.lean`: resolve by taking sub34's side** (`git checkout
   --theirs …` then re-stage, or hand-resolve to sub34's sorry-free `endpoint_telescoping`). Rationale
   §3: sub34's is the completed version of the same lane; the expedition WIP is superseded.
3. Build. The expected residual after merge is **two genuine analytic sorries**, both correctly stated:
   - **PIN1:** `deepestEPivot_regSlice_fderiv` — the #91 frame-decorated Leibniz sandwich (the
     invertible frame factor `F`). NOT a tactic gap; the banked sub-pieces are on
     `fm/deriv-frame-resume` (which is sub34 + 7 #91 commits / − 11 sub34 commits; merge-base
     `1a21b45f`). **If the controller wants the latest #91 progress, prefer `fm/deriv-frame-resume`**
     over `sub34` as the merge source — same single conflict, more analytic fill banked.
   - **PIN2:** `framedParams_split_eq_frame_raw` — the geometric frame-bridge cert (4 documented
     sub-steps). PIN2's squeeze chain `deepest_loss_squeeze` itself is already sorry-free given this cert.

**Alternative cherry-pick path (NOT recommended).** The #120 atoms are spread across `fm/deriv-spec`
(`DeepestRegPivotEquiv`, `b859f0f8`) + `fm/deriv-pin1` (`DeepestFramedDeriv`, `426a6b87`) +
`sub34`/`frame-resume` (the wiring). `sub34` already **consolidates** all of these (`d9c4f780`), so a
single merge is cleaner than reconstructing the atom set by cherry-pick.

---

## 5. Soundness risk — flagged

**RISK 1 (the named one, CONFIRMED).** A fill that proves the **base** `deepestEPivot_regSlice_fderiv_id`
**`= id`** against the **OLD opaque `Fintype.equivFin` pack** would be **unsound / not honestly
provable**. The base `regResidualPack` is an arbitrary cardinality bijection with no relation to the
physical block coordinates; the product-residual derivative is the identity *in physical block
coordinates*, but expressed through an opaque relabeling it does not reduce to the literal `id` CLM —
it is `id` only "up to the (opaque) `regResidualPack` relabeling", which does **not** close by `rfl`
for `Fintype.equivFin`. The repo's own commits already record this (`2c9c492f` "unprovable as stated",
`12846aae` "false-as-stated, needs #120 structured-equiv").

> **Decorrelated check (local Codex, gpt-5.1-codex-max, high):** independently confirmed. "Under
> Version A the statement is generally not derivable… conjugating the block-wise identity by an
> unknown permutation… definitionally the identity only when the equiv is the canonical block
> enumeration… Version B (`regPivotFinEquiv`) fixes this so it reduces by `rfl`. Accepting a Version-A
> proof would be unsound unless the theorem is weakened to 'identity up to the relabeling'." No hole
> found in the reasoning.

**Mitigation:** the #120 family is the sound form **by construction** (transparent pack + frame
factor). Merging `sub34`/`frame-resume` is therefore the *soundness-positive* move — it replaces the
flawed statement, it does not paper over it. **Do NOT** merge or cherry-pick any OLD-form fill of the
literal `= id` (none exists sorry-free anyway, but guard against one being produced).

**RISK 2 (watch, low).** After the merge the base's other consumers
(`deepestEPivot_deriv`, `deepest_regAbsorb_exists`, `deepest_gauge_construction`) must be the **sub34**
versions (they already call `deepestEPivot … Pf Qf` and the relaxed shear-CLE). Since all six critical
files come in from sub34 unchanged-on-base, this is automatic — but verify the build has **no leftover
OLD-signature call** (e.g. a stray `deepestEPivot H r hr hL (q.1, q.2.2)` without frames). A green
build with exactly the 2 expected analytic sorries is the gate.

**RISK 3 (verify post-merge).** Total `sorry` count is a coarse proxy: base lean tree ≈ 95, sub34 ≈ 53,
frame-resume ≈ 56 occurrences. The merge should *reduce* the L2-region sorries to 2 and not silently
introduce others from the incoming modules; confirm with a sorry audit of the `Validate/Deepest*`
files specifically, not just the global count.

---

## Reflection

- **Most likely to advance the expedition:** merging `fm/deriv-frame-resume` (sub34 + banked #91
  progress) — it is a one-conflict merge that swaps the unsound `= id` skeleton for the sound
  frame-factor form and leaves L2 reduced to two *correctly stated* analytic sorries.
- **Most likely to break:** PIN1's `deepestEPivot_regSlice_fderiv` #91 frame-sandwich — it is a
  genuine analytic atom still open (not a wiring gap), and the frame-decoration makes it harder than
  the pre-frame `= id` it replaced.
- **Next computation that would clarify:** an actual `git merge` + Lean build on a scratch worktree to
  confirm "exactly 2 analytic sorries, no OLD-signature leftovers, no new sorries from the incoming
  `Validate/Deepest*` modules" — turning the merge-tree dry-run (data) into a verified build (the gate
  for Risk 2/3). That is the controller's job (write-side); this map is the read-side terrain.

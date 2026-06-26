# Thread 23 — L2 PIN1 design: the B-determined pivot permutation fix

Seat: pen-and-paper (adjudication). Direction: validate-or-refute (soundness-sensitive; 2 prior fixes refuted).
Object: `deepestEPivot_regSlice_fderiv` invertibility (`DeepestGaugeConstruction.lean` ~line 432).

## Verdict: the permutation fix SURVIVES — but only when read correctly (NOT as an output-coordinate permutation)

The brief's literal phrasing ("permutation of the residual pack's **output coordinates**") is REFUTED as
written (it is inert). The fix SURVIVES under the correct reading: a `B`-determined permutation of the
**last-interface COLUMN SPLIT** (which `H_L` columns are "pivot"). With that reading it is sound and
unrestricted. Detail below.

## The F block-structure (decorrelated re-derivation, sympy `pin1_F.py`)

Confirmed the recorded structure independently. In residual-block order `(P11−I, P12, P21)`, after the
quadratic cross term is killed (strict derivative 0 at 0):

    F(X,Y,Z) = ( A11·X + A12·Z + Y·B21 ,  Y·B22 ,  A21·X + A22·Z )

(`A := reindex(Pf first)`, `B := reindex(Qf last)`, `r ⊕ (·−r)` blocks; `A` invertible from `hPf`.)
Codex's independent derivation matched (it found the same block map and the same determinant).

`det F = (det A)^{H_L−r} · (det B22)^{r}` (block-triangular, sympy `pin1_Finv.py` + Codex part (a)).
So **F invertible ⟺ A invertible (whole) ∧ B22 invertible**. `A` is always a whole unit (asymmetry:
`pin1_firstcheck.py`), so the SOLE failure point is `B22` at the LAST interface.

## (a) The permutation DOES give B22 invertible — but it must permute the COLUMN SPLIT, not F's output

- **Output-coordinate permutation is INERT** (sympy `pin1_perm.py`, Codex (b)): a permutation of F's
  residual outputs is left-mult by a permutation matrix `Pσ`; `det(Pσ·F) = ±det F`. It cannot turn a
  singular F into an invertible one. **The brief's literal "output coordinates" reading is refuted.**
- **Column-split permutation is non-inert and works** (`pin1_pivotalign.py`, `pin1_structure.py`):
  `B22` invertible ⟺ `V`'s first `r` columns independent (`V` = last-interface rank-`r` row factor).
  Choosing a pivot column set `J` (size `r`, `V_J ∈ GL_r`, always exists) and the permutation `Π_J`
  moving `J` to the front gives `V·Π_J` with independent first-`r` cols, hence `B22` invertible.

## (b) Handles ALL rank-`r` B without restriction (unlike refuted fix 2)

Refuted fix 2 FIXED the pivot at "first `r`", forcing `B`'s first `r` columns independent (a restriction).
The permutation is `B`-DETERMINED: `Π_J` depends on `B`'s actual pivots, and **a pivot column set always
exists** for a rank-`r` matrix. Killer counterexamples cleared (`pin1_coupling.py`):
- `r=1, B=[0,b]`: pivot col = 1; `Π_J` swaps `0↔1`; `B·Π_J=[b,0]` normalizes with `B22` free → invertible.
- `V=[0,0,1]` (`pin1_structure.py`): pivot col 2 → front; `B22'` free → can be `I_2`.

## (c) Genuinely measure-preserving + RLCT-preserving (`pin1_rlct.py`, `pin1_core.py`)

`B` is FIXED in the statement ⟹ `Π_J` is a FIXED permutation matrix (constant, not varying with the chart
point). A column permutation of the `H_L` interface = right-multiply product and target by an orthogonal
`Pπ`; Frobenius norm is orthogonally invariant ⟹ unit-Jacobian, measure-preserving (same
`rlctAtOn_comp_homeomorph` mechanism `coreAbsorb` already uses). Permutation-invariants verified:
`nReg = r(H_0+H_L−r)` (dim count), `deepestM` dims `(H_s−r)` (dim count), `lambdaCore` (reduced-core RLCT,
orthogonal-invariant), tail-rows-vanish at last layer (a ROW property, untouched by COLUMN perm),
tail-cols-vanish at layer 0 (on `H_1`, disjoint from `Π_J` on `H_L`). **No RLCT-level damage.**

## (d) Consistency (Codex (d), `pin1_coupling.py`): the SAME Π_J works in all three places

`Π_J` must be used wherever the `H_L` split appears: the last-layer right-normal-form frame, the residual
block split (`rThresholdSplit r (H last)` inside `roleSplitIdx`/`deepestEPivot`), and the target-`B`
normalization `reindex(P0·B·QL) = diag(I_r,0)` in `framedParams_split_eq_frame_raw`. CONSISTENT because
`B = U·V` with `U` injective ⟹ pivot cols of `B` = pivot cols of `V` (`rank(B_J)=rank(U V_J)=rank(V_J)`).
So a single shared `J` pivot-aligns the frame AND the target. **Soundness gate: this must be SHARED data**
(if the frame and the target normalization independently choose pivots, they may disagree — Codex (d)).

## Why it is a re-architecture, not a localized clause

The "first r" threshold is baked into `rThresholdSplit → layerEntrySplit → roleSplitIdx → deepestM /
RegGaugeIdx / regResidualPack / the slot read / the energy lemma`. Inserting `Π_J` at the last interface
ripples through all of them (the threshold also defines which entries are CORE vs reg/gauge). The dimension
counts and RLCT survive, but the wiring is coordinated. This matches the note's assessment.

## Implementation spec (the precise change-set)

**Π_J is NECESSARY, not optional** (`pin1_implroutes.py`): for the UNPERMUTED last interface, `B22` is
FORCED singular whenever `B`'s pivot column index `≥ r` (`pin1_freedom.py` — no choice of frame `Q`
escapes it; the constraint `V·Q = [I_r|0]` zeroes `B22`'s rows). So the note's option (b) "add `hB22`
hypothesis and discharge at the call site" is UNSATISFIABLE for general `B` without `Π_J` — it would be
refuted-fix-2 in disguise. The permutation must happen.

**Shared data:** package a pivot column set `J ⊆ Fin H_L`, `|J|=r`, with `(reindex V)_J` invertible
(`V` = the last-interface rank-`r` row factor; exists since `rank V = r`). `Π_J : Fin H_L ≃ Fin H_L`
moves `J` to `{0,…,r−1}`. Constant (B fixed).

**Minimal sound placement (Route B'):** the CORE slot / `deepestM` dims / `lambdaCore` are
permutation-INVARIANT (dimension counts; orthogonal-invariant RLCT), so `roleSplitIdx`'s CORE half is
UNTOUCHED. `Π_J` need only reach the three objects that read `B`'s columns as "pivot":
1. **`regResidualPack` at the last interface** (`DeepestSplitReindex`): the `P11`-vs-`P12` column split
   (`Fin r` vs `Fin (H_L−r)`) must be `Π_J`-twisted, so the residual blocks align with the chosen pivots.
   `deepestEPivot`'s `toBlocks₁₁/₁₂` reads, and the energy lemma `deepestEPivot_sq_sum_eq_blocks`, stay
   valid (the energy lemma uses the pack only as a SUMMING bijection — value-irrelevant, asserted in its
   own docstring; `pin1_energy.py`).
2. **the last-layer frame** (`deepestPoint_frame` / `rank_normal_form_right_only`): construct the frame
   against `V·Π_J` (pivot cols leading), giving `B22` invertible (the explicit
   `Q' = [[V_J⁻¹, −V_J⁻¹V_K],[0, I]]` gives `B22=I`, but the proof needs only invertibility — Codex (e)).
3. **the target normalization** in `framedParams_split_eq_frame_raw`: `reindex'(P0·B·QL)=diag(I_r,0)` must
   use the SAME `Π_J`-twisted split. CONSISTENT because pivot cols of `B` = pivot cols of `V`
   (`rank(B_J)=rank(U·V_J)=rank(V_J)`, `U` injective; Codex (d)).

**Then `deepestEPivot_regSlice_fderiv` CLOSES** via the existing consumer
`regStraightenTotalCLM_equiv_of_regBlock_isUnit` (already takes `F : ≃L`): build `F` from `A` (whole
unit, from `hPf`) + `B22` invertible (from the `Π_J` frame), via the block-triangular inverse
`det F = (det A)^{H_L−r}·(det B22)^r` (`pin1_Finv.py`). The reachable product-value + quadratic-deriv-0
half (`prodAux_regSlice_through_first`, `framedParamsReg_regSlice_{first,last,interior}`, `readY_…`,
`devXZ_corner_devY`) is unchanged.

**Ripple to consumers:** `deepest_loss_squeeze` (PIN2) consumes `hregval` (reg-output = `deepestEPivot`)
+ `hcoreabs` — both stay; the squeeze constants are split-relabel-invariant (`pin1_energy.py`). The
`deepest_gauge_construction` assembly threads the `Π_J`/`J`-data into both `deepestEPivot_deriv` and the
cert. `deepest_gauge_chart_construct` and `deepest_regular_core_normal_form_of` are downstream of the
bundled existence and need no change beyond the new shared data flowing through.

**Symmetry note:** ONLY the last interface needs `Π_J` (`pin1_firstcheck.py`). `A = reindex(Pf first)`
is a WHOLE unit ⟹ the `(X,Z)→(P11,P21)` block of `F` (left-mult by full `A`) is always invertible. The
first interface needs no permutation.

## Build plan (lemma-granularity) — coordinated PIN1+PIN2 tide

The objective: thread one B-determined pivot set `J` so the last-interface `Fin (H_L) ≃ Fin r ⊕ Fin (H_L−r)`
split is `Π_J`-twisted *identically* in the three places that read B's columns as "pivot", and the rest of
the architecture inherits it. References below are to real signatures (verified in-repo this tide).

### (1) The shared `LastPivot` datum

A single threaded object (pass it everywhere; never re-derive a pivot set downstream):

    structure LastPivot (H : Fin (L+1) → ℕ) (r : ℕ) where
      J     : Fin r ↪ Fin (H (Fin.last L))          -- the r pivot column indices (an embedding)
      hpiv  : -- the chosen r columns of the last-interface factor V are independent
              -- (equivalently: (reindex V).submatrix id J has rank r / is column-injective)

Building-block obligation (Core, network-free; standard "column rank = rank"): for a rank-`r` matrix
`V : Fin r × Fin c`, `∃ J : Fin r ↪ Fin c, (V.submatrix id J) ∈ GL_r`. Likely a small new
`Core.Matrix` lemma — `Matrix.exists_pivot_cols_of_rank` — Mathlib has `Matrix.rank` ↔ column-span
finrank (`rank_eq_finrank_span_cols`) but not the packaged embedding; ~30-50 lines. NOT a soundness gap
(the fact is elementary); flag it as the one genuinely-new brick.

Derive `Π_J : Fin (H_L) ≃ Fin r ⊕ Fin (H_L − r)` from `J` — `J`'s image to `Fin r`, complement to
`Fin (H_L − r)` (an `Equiv.Set.sumCompl`-style construction; the *replacement* for `rThresholdSplit r (H_L)`
at the last interface). Call it `pivotThresholdSplit r (H_L) J`. At `J = id` it is `rThresholdSplit` (so the
unpermuted case is the existing behaviour — a clean specialization, good for the L=1 / pivot-already-front path).

### (2) Threading `Π_J` to the three objects

**(2i) `regResidualPack` last-interface split.** `BoundaryPivotIdx` (`DeepestSplitReindex:218`) hard-codes
the Y-block as `Fin r × Fin (H_L − r)`; `regResidualPack := regPivotFinEquiv` (`:238`) and `deepestEPivot`'s
`toBlocks₁₂` read against `rThresholdSplit r (H_L)`. Replace `rThresholdSplit r (H_L)` by
`pivotThresholdSplit r (H_L) J` in: `deepestEPivot`'s `P` reindex (the `toBlocks₁₁/₁₂` column side); the
`regBoundaryToRegGauge` Y-arm `finCongr` (`:273`) becomes the `Π_J` relabel. `regPivotFinEquiv`'s sum-type
*shape* is unchanged (still `(r×r)⊕((r×(H_L−r))⊕((H_0−r)×r))` — `Π_J` only changes which physical column an
index points to). So `card_boundaryPivotIdx` and `deepestNReg` are untouched (the `nReg` count is `Π_J`-blind).

**(2ii) the V·Π_J frame** (B22 invertible). `deepestPoint_frame_exists` (`DeepestFrame:39`) calls
`rank_normal_form_right_only` (`RankNormalForm:361`) on the deepest last layer (tail rows vanish). Re-target it
at `(reindex-by-Π_J of the last layer)`: feed `rank_normal_form_right_only` the *column-permuted* matrix
`A_last · Pπ` (pivots front), so the resulting `Q'` has `(reindex Q')₂₂` invertible. Concretely the explicit
frame `Q' = fromBlocks (V_J⁻¹) (−V_J⁻¹ V_K) 0 I` realizes `B22 = I`, but
`rank_normal_form_right_only`-on-`A_last·Pπ` already gives invertible `B22` (the kernel-graph argument,
`pin1_structure.py`) — the proof needs only invertibility. New frame fact:
`deepestPoint_frame_lastBlock_isUnit … (J) : IsUnit ((reindex (pivotThresholdSplit … J) (Qf last)).toBlocks₂₂)`.
The asymmetry holds: NO change to layer-0 / the first interface (`A = reindex(Pf first)` is a whole unit).

**(2iii) the target normalization** `reindex(P0·B·QL) = fromBlocks 1 0 0 0` in
`framedParams_split_eq_frame_raw` (`DeepestGaugeConstruction:629`, step (3) of its sorry). Use the SAME
`pivotThresholdSplit r (H_L) J` for the column reindex of `B`. CONSISTENT because pivot(B)=pivot(V): `B=U·V`,
`U` injective, `rank(B_J)=rank(U·V_J)=rank(V_J)=r` (so `J` valid for both). The corner target stays
`fromBlocks 1 0 0 0`.

### (3) How `deepestEPivot_regSlice_fderiv` then CLOSES

Statement stays as-is (still `∃ F : ≃L, HasStrictFDerivAt (reg-slice) F 0`) — the `J` flows in via the
`Pf/Qf` it already takes (now the `Π_J`-frame). The reachable half is unchanged: `prodAux_regSlice_through_first`
+ `framedParamsReg_regSlice_{first,last,interior}` + `readY_regSlice_last` + `devXZ_corner_devY` give the
linear part `F(X,Y,Z) = (A11 X+A12 Z+Y B21, Y B22, A21 X+A22 Z)` (quadratic-deriv-0 from
`hasStrictFDerivAt_sum_mul_zero`). Build `F` from:
- `A` whole-unit (from `hPf` — existing `deepestPoint_frame_invertible.1`);
- `B22` invertible (the NEW `deepestPoint_frame_lastBlock_isUnit … J` from 2ii);
then hand to the EXISTING consumer `regStraightenTotalCLM_equiv_of_regBlock_isUnit`
(`DeepestRegSliceFderiv:554`) — it already takes `F : ≃L` whose coercion is `D_E.comp regInCLM`. The
block-triangular inverse is `det F = (det A)^{H_L−r}·(det B22)^r` (`pin1_Finv.py`): solve `Y` from `P12`
via `B22⁻¹`, subtract `Y·B21` from `P11`, recover `[X;Z]` via whole-`A⁻¹`. So `deepestEPivot_deriv`
(`:512`) — which already assembles `D_E.comp regInCLM = ↑F` and calls
`regStraightenTotalCLM_equiv_of_regBlock_isUnit` — needs NO structural change; it just receives an
invertible `F` instead of a `sorry`.

### (4) The PIN2 consistency obligation (the one non-negotiable)

PIN2's energy identification `hSreg_eq` (`deepest_loss_squeeze`, `DeepestGaugeConstruction:789`) chains
`hregval → deepestEPivot_sq_sum_eq_blocks → h00/h01/h10`. For it to stay valid, the residual blocks
`(P11,P12,P21)` of `deepestEPivot` (2i) and the framed blocks `(P00,P01,P10)` of the cert
`framedParams_split_eq_frame_raw` (2iii) must refer to the SAME column decomposition — i.e. the SAME `J`.
- `deepestEPivot_sq_sum_eq_blocks` (`:583`) is `Π_J`-STABLE: its proof uses `regResidualPack` only as a
  summing bijection (`Equiv.sum_comp`; value-irrelevant, per its own docstring). ✓ unchanged.
- The block-energy reindex-invariance is `frobenius_sum_reindex` / `frobenius_sq_eq_blocks`
  (`DeepestGaugeBlocks:481/500`) — invariant under ANY index equiv, so `Π_J`-stable. ✓
- The cert's `dlnLoss_block_squeeze` (`DeepestGaugeBlocks:516`) takes the block split `e₂` as a parameter;
  pass `e₂ := pivotThresholdSplit r (H_L) J` (the SAME as `deepestEPivot`'s). ✓
- **Obligation to STATE explicitly:** `framedParams_split_eq_frame_raw`'s `h01` (the `P01 = (reindex
  (pivotThresholdSplit … J) (prod (framedParamsReg …)))₁₂`) and `deepestEPivot`'s `toBlocks₁₂` use the
  IDENTICAL `pivotThresholdSplit … J`. If a future edit lets them diverge, `hSreg_eq`'s `rw [h01]` fails to
  typecheck (the column index types differ) — a compile-time tripwire, not a silent unsoundness. Make `J`
  a single value passed to both `deepestEPivot_deriv` and `framedParams_split_eq_frame_raw` from
  `deepest_gauge_construction` (`:862`) so divergence is unrepresentable.

### Build order (suggested)
1. Core: `Matrix.exists_pivot_cols_of_rank` (the one new brick) + `pivotThresholdSplit` + its `J=id` spec.
2. Frame: `deepestPoint_frame_lastBlock_isUnit … J` (re-target `rank_normal_form_right_only`).
3. PIN1: close `deepestEPivot_regSlice_fderiv` (build `F`, hand to the existing isUnit consumer).
4. PIN2: thread the SAME `J` into `framedParams_split_eq_frame_raw` (step (3) of its sorry) + `e₂`.
5. Assembly: thread `J` through `deepest_gauge_construction`; verify `hSreg_eq` typechecks (the tripwire).

## Artefacts
- sympy: `/tmp/pin1_F.py`, `pin1_B22.py`, `pin1_freedom.py`, `pin1_structure.py`, `pin1_perm.py`,
  `pin1_pivotalign.py`, `pin1_Finv.py`, `pin1_coupling.py`, `pin1_rlct.py`, `pin1_core.py`,
  `pin1_firstcheck.py`.
- Codex decorrelated consult: `codex/permfix-prompt.md` + `codex/permfix-answer.md` (agreed on F det,
  output-perm inertness, consistency-as-shared-data).

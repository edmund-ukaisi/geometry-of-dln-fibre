# Statement card — STEP-3 unit block-elimination (general widths)

Thread `genm-sjclose` (tide, off `origin/genm-sjcarrier` @17970751). Branch `genm-sjclose`.
Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJStep3.lean` @ `9c49b57f`.

> **Claim.** Aoyagi's `(S,J)` STEP-3 "Z-independent unit block-elimination", at general (opaque
> `Fintype`) widths: an arbitrary block matrix with invertible pivot factors into two det-1 unit
> factors (depending only on the block, not on any downstream) and a block-diagonal core; the unit
> factors are absorbed into the adjacent upstream/downstream factors of a Frobenius-loss product;
> the block-diagonal core row-splits into a pivot energy + a corank residual; and — only through a
> literal downstream identity channel — the pivot-column block enters isotropically.
>
> - **Lean:** `DLNFibre.DLN.RLCT.step3_blockFactor`, `frobSq_step3_absorb`, `frobSq_blockDiag_split`,
>   `frobSq_identityChannel`, `frobSq_col_split`, `det_invSchurLeft`, `det_invSchurRight`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJStep3.lean` @ `9c49b57f`)
> - **Gloss.**
>   - `step3_blockFactor` : `fromBlocks A B C D = invSchurLeft A C * fromBlocks A 0 0 (schurCompl A B C D) * invSchurRight A B`,
>     with `invSchurLeft A C = [[1,0],[C·⅟A,1]]`, `invSchurRight A B = [[1,⅟A·B],[0,1]]`, `A` a `t×t`
>     invertible pivot, `Γ = schurCompl A B C D = D − C·⅟A·B` the `a×b` corank block.
>   - `det_invSchurLeft/Right` : both unit factors have determinant `1` (no Jacobian).
>   - `frobSq_step3_absorb` : `frobSq (P · fromBlocks A B C D · Z) = frobSq ((P·invSchurLeft A C) · (fromBlocks A 0 0 Γ) · (invSchurRight A B · Z))`
>     — the left unit rides into the upstream `P`, the right into the downstream `Z`.
>   - `frobSq_blockDiag_split` : `frobSq (fromBlocks A 0 0 Γ · W) = frobSq (A · W_top) + frobSq (Γ · W_bot)`
>     (`W_top/W_bot` the pivot/non-pivot row blocks) — the corank block `Γ` stays COUPLED to `W_bot`.
>   - `frobSq_identityChannel` : `frobSq (A₀ · fromBlocks 1 0 0 Z) = frobSq (A₀_left) + frobSq (A₀_right · Z)`
>     (`A₀_left/A₀_right` the pivot/non-pivot column blocks) — the ISOTROPIC `frobSq (A₀_left)` shape
>     the pure peels (`RouteMSJCorankPure`) consume.
>   - `frobSq_col_split` : the column-block companion of the banked `frobSq_row_split`.
> - **Proved.** All seven, unconditionally, as exact pointwise real-matrix-algebra identities
>   (`Invertible A` where a pivot inverse appears; `DecidableEq` on the block index types for the `1`
>   matrices). Non-vacuity witnessed in-file (`t=a=b=Fin 1`). `#print axioms` = `[propext,
>   Classical.choice, Quot.sound]` (clean-three) for every declaration; S2-free; no `monomial_rlct`.
> - **Assumed.** none beyond the pivot invertibility / decidable-eq the statements carry.
> - **Cited.** none (rides only the banked `schur_cov`, `frobSq_row_split`, `fromBlocks_*`, all
>   in-repo, all clean-three).
> - **Deferred.** The `SJState` recursion carrier and `sjJointResolution` (`RouteMSJResolution.lean:803`)
>   are UNTOUCHED. STEP-3 is one exact pointwise step; driving it down the layers with the accumulated
>   `∏uⱼ²` radial monomial, the chart transitions, and the terminal integrability is the deferred
>   carrier (the multi-week mountain).
> - **Route.** Controller's pure-route spec (`chart-lemma-probe.md` step 3): lift the `(2,2,2)`
>   `Case222Resolution.blockForm`/`blockForm_step3` block-elimination to general widths. Realised here
>   as the inverse of the banked `schur_cov` (both unit factors are the inverses of `schurLeft`/
>   `schurRight`; recombine).
> - **Status.** sorry-free (awaiting fidelity review).

## ROUTE-CORRECTION FINDING (escalate to controller) — decorrelated Codex xhigh corroborated

The mission's piece-1 claim that STEP-3 "turns corankStep's residual into `‖pivot rows‖²` = the
isotropic Morse block `frobSq Δ` (which the pure peels consume)" is **mathematically inaccurate**.
STEP-3 is a corank-DECREMENTING block-diagonalisation with unit absorption; it does NOT isotropise:

- `corankStep`'s residual is `frobSq (C·Q̃_p + Γ·Q_b)` (banked `frobSq_schur_block_split`). Expanding,
  `frobSq (X + Γ·R) = frobSq X + 2·tr(Γ·R·Xᵀ) + tr(Γ·(R·Rᵀ)·Γᵀ)` — the corank block `Γ` is isotropic
  (`= frobSq Γ + Γ-free`) **only** when `R·Rᵀ = 1` and the cross term vanishes, i.e. only when the
  downstream carries a literal identity channel. This is FALSE for a general downstream product `Q`.
  (This is also the OWN admission of the `RouteMSJCorankResidual`/`RouteMSJCorankPure` headers: they
  are the isotropic special case, needing the anisotropy pre-removed.)
- The unit-triangular STEP-3 factors do NOT remove this anisotropy: for the LEADING factor (no
  upstream `P`, exactly `gammaPeelIntegral`'s case) the left unit `L(γ)` cannot be absorbed and remains
  in the norm, reproducing the same cross-coupled residual `frobSq (C·Q̃_p + Γ·Q_b)` one corank lower.
- Consequently the **pure peels `matBox_corank_dominates_absZ_lt_top` / `matBox_corank_residual_absZ_le`
  do NOT consume corankStep's coupled residual**. They consume only the identity-channel form
  `frobSq_identityChannel`. On the general degenerate strata (no identity channel) the recursion
  terminates on the **`monomial × (unit ≥ 1)`** endpoint — the actual `(2,2,2)` mechanism
  (`blockForm_step3` + `step3_unit_ge_one` + `integrableOn_monomial_mul_unit_iff`), NOT a final pure
  peel.

**Precise remaining step for the controller to re-decide.** Either (a) route the carrier's terminal
through the `monomial × unit` endpoint (lift `blockForm_step3`/`step3_unit_ge_one` to general widths;
the pure peels then serve only the identity-channel / full-rank sub-charts), or (b) confirm the pure
peels are intended only for the deepest free-matrix layer (`sjBase1_freeMatrix`-like) reached after
the deeper chain is resolved to an identity channel. The STEP-3 brick banked here is correct and
route-agnostic under either decision; the carrier bookkeeping (multi-week per Codex) is unchanged.

Codex consult artefacts: `codex/step3-{prompt,answer}.md` (this thread).

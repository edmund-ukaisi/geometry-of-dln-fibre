# §-note: ideal-preservation on the BAKED def — matched-node Gröbner (elder §7(1), corrected)

Elder §7(1) gate, the DECISIVE datum for the model round (route-adoption vs skeleton-revision).
Supersedes the `(1b)` of `recoord-adjudication-note.md`. Scripts (exact sympy + Gröbner, exit 0):
`verify/recoord_ideal_matched.py`, `verify/recoord_path_unipotency.py`. Decorrelated Codex (xhigh,
hypothesis withheld) corroborates all three verdicts and sharpened two (folded in below).

## Correction to my own prior (1b) — a NODE MISMATCH
`recoord_adjudication.py` (1b) compared `baked` (3 edges: case2 δ1 → case2 δ0 → rollover) against
`honest_residual` (ONE honest clear of ed1 only). Different nodes. Its "both inclusions FALSE" conflated
the node mismatch with the recoord defect and is **not** clean evidence. Below is the like-for-like
matched comparison, one common ring, same node.

## The matched-node setup (re-derived, exact)
At the ed1 clear of pivot `(0,0)` at layer `S=0`, `δ=1` (pivot→1), the baked shear and the faithful full
Schur peel produce the **SAME** recoordinatized deeper factor `W = A_{S+1}·Q₁⁻¹` and the **SAME** Schur
exceptional `e₂ = u₀₁₁ − u₀₁₀·u₀₀₁` (and `e₃` for a 3-row block). They differ ONLY in the layer-0 residual
block `B` (the pivot-column entries `u_{0,r,0}`, `r>0`):

    baked:     B[r][0] = u_{0,r,0}   (guard `row≠a` excludes the pivot cross ⟹ uncleared)
    faithful:  B[r][0] = 0           (Q₁ row-op clears it)

`{A₂, W, u₀₀₁, u₀₁₀, u₀₂₀, e₂, e₃}` is an invertible relabel of the original entries ⟹ algebraically
independent ⟹ a legitimate common ring. Both residuals are polynomials in it.

## (1) ⟨baked⟩ ≠ ⟨faithful⟩ as IDEALS — on all three witnesses
Gröbner grevlex, `(2,2,2,2)` / `(2,3,2)` / `(2,3,2,2)`, matched ed1 node: **both inclusions FALSE** for
baked-vs-faithful-with-U AND baked-vs-faithful-no-U. NOT a unit-multiple; genuinely different ideals.

- **The difference is exactly one term, `∝ the uncleared pivot-column coord `u₀₁₀` (and `u₀₂₀`),** landing
  ONLY in the column-0 residual entries `M[0], M[2]`. The column-1 entries `M[1], M[3]` are **identical**.
- **faithful `M` does not contain `u₀₁₀`/`u₀₂₀` at all** (relocated into `Q₁`); baked `M` does. So faithful is
  **rank-reducing** (drops the pivot-column coords — Jacobian has zero rows), baked keeps them.
- **Radicals also DIFFER** (closes the decorrelated-Codex flag "equal radicals not ruled out"): a concrete
  point on `(2,3,2)` (`u₀₁₀=1, w₀₁=1, w₀₀=−1`, rest tuned) makes all baked entries `0` but `faithful M[0]=−1`.
  So `V(⟨baked⟩) ≠ V(⟨faithful⟩)` set-theoretically.

## (1′) …BUT the baked step PRESERVES the RLCT of the zero-fibre — VALID-BUT-DIFFERENT, not broken
The Gröbner inequality **alone does not mean broken** — an invertible coordinate change also breaks
ideal-equality while preserving everything that matters. The discriminator is whether the baked map is
invertible. It is:

- Every shear on the path to case11 (`ed1` case2 δ1, `ed2` case2 δ0; rollover = id) is **`det J ≡ 1` AND
  structurally triangular** (each modified coordinate's increment depends only on UNMODIFIED coordinates)
  ⟹ a **globally invertible** polynomial automorphism, not merely `det = 1` (this defeats the
  Jacobian-conjecture worry). So the baked fold = **(legit blow-ups/quotients) ∘ (invertible shears)**
  applied to `⟨mult⟩`.
- Invertible coordinate changes preserve the RLCT; a blow-up is proper birational and preserves it **when
  the total transform + the Jacobian discrepancy + all charts are bookkept** (decorrelated-Codex caveat —
  exactly the `M_{s,k}` / chart-fan discipline; `M_{s,k}` HOLDS, check (3) below). ⟹ the baked chart
  computes the correct RLCT **of the original**. **Route-VALUE safe.**
- The RLCT equivalence is to the **ORIGINAL** via baked's own invertible shear — NOT to the faithful chart
  (faithful is rank-reducing, cannot be an automorphism; baked-vs-faithful automorphic equivalence is
  therefore UNDECIDED and, by the radical separation, the varieties genuinely differ). The two are
  different residual **presentations** of the same original problem.

## (2) MONOMIALISATION — FAILS on the baked def (report-immediately item, confirmed)
The baked cleared layer-0 block is `[[1, u₀₀₁],[u₀₁₀, e₂]]` (Schur `(1,1)=e₂` formed, pivot row/col
off-diagonals `u₀₀₁,u₀₁₀` NOT cleared), NOT the clean `diag(1,e₂)`. Same root cause as (1): the missing
pivot-column clear `Q₁`.

## (3) M_{s,k} — HOLDS
The baked shear is det-1 ⟹ adds nothing to the `blockBlowupMap` Jacobian `u^{|center|−1}`; the exceptional
exponent ledger is shear-independent. (This is the Jacobian-discrepancy bookkeeping the RLCT-preservation in
(1′) relies on.)

## The route call (for the elder's model round)
- **NOT a monument-reopening ideal-preservation failure.** The baked step preserves the RLCT of `⟨mult⟩`
  (value-safe). Aoyagi's mathematics (with the full clearing) is valid; what fails is the **Lean shear
  encoding** — the shear framework `u ↦ u+φ` cannot express the rank-reducing clearing, and the baked
  unipotent shear is the best invertible approximation, which does not monomialise. This is the
  **SKELETON-REVISION** lane seat-L4D already identified (12th catch), corroborated, not a wider blast.
- **It IS a genuine StepInv-invariant failure:** the inductive hypothesis "clean `diag(1,e₂)` residual block"
  is FALSE on the baked def; the actual residual block is `[[1,u₀₀₁],[u₀₁₀,e₂]]`.
- **The single open fact that decides the resolution** (Codex point 3, `[plausible-unverified]`): whether the
  recursion on the actual block `[[1,u_row],[u_col,e]]` strictly decreases a well-founded complexity measure
  and reaches normal crossings without the pivot-row/col clearing. This is the def-side / model question —
  seat-L4D + elder own it. Two ways forward: (a) RESTATE the StepInv invariant to the non-diagonal
  unit-determinant block and prove downstream termination, or (b) move the clearing INTO the blow-up map (the
  rank-reducing operation, not shear-representable) — the model surgery.

## Completed-candidate re-run (pending seat-L4D's def)
When seat-L4D specifies a completed candidate def (if DEF-EDIT-3-REPRESENTABLE), I re-run all of (1)/(2)/(3)
on it. Elder-pinned green bar: the baked `foldResid` must carry the **ruled field** (extra-block coeff =
`m_k·β`, the row's active-divisor `b`-monomial product — `honest_clear`'s coeff-0 is the trivial-`b`
special case) on BOTH wide witnesses, traced on the completed def; any residual leftover (coeff 1 or 2) =
still unpaired, still false.

# Consult: the case1(1)-boost δ=1 divisibility in Aoyagi's DLN resolution (Lean formalisation)

## Contract
Adjudicate ONE truth-value with a mechanism, in one direction:

> **Q.** In the one-step preservation leaf below, is conjunct-1 (the `StepInv` divisibility)
> for the **case1(1)-boost sub-case at δ=1** PROVABLE from the stated hypotheses
> (`hinv` at the parent + `hbranch : (p.extend ed).IsRealBranch e`), and if so BY WHAT MECHANISM?
> In particular: does it require `foldB p` to carry the birth-pivot coordinate as a factor
> (a PATH-HISTORY invariant), and is that derivable from `p.IsRealBranch e`? Or is the leaf
> UNPROVABLE as stated (needs a strengthened carried invariant)?

Answer with: VERDICT (provable-as-stated / needs-new-path-invariant / unprovable-as-stated),
the precise mechanism (or the precise obstruction), and — if a new lemma is needed — its
cleanest statement.

## Setup (exact defs)

Coordinates: `u : Fin D → ℝ` (`D = flatDim d`). A resolution path `p` accumulates:
- `foldG p : (Fin D→ℝ)→(Fin D→ℝ)` — root ↦ id; step ↦ `foldG p ∘ stepMap`.
- `foldB p : (Fin D→ℝ)→ℝ` — root ↦ 1; step ↦ `(u_pivot)^δ · foldB p (stepMap u)`, `δ = [cleared=0]`.
- `foldResid p : Fin nR → (Fin D→ℝ)→ℝ` — root ↦ `coreGen` (the entries of the matrix product
  `mult d (e u)`); non-terminal step at δ=1 ↦ `foldResid p (cast j) (qm u)` where
  `qm u k = if k = pivot then 1 else (edgeShear u) k`; at δ=0 ↦ `foldResid p (cast j) (stepMap u)`.
- `stepMap = blockBlowupMap center pivot ∘ edgeShear`, `blockBlowupMap S p w j = if j=p then w_p
  else if j∈S then w_p·w_j else w_j`. For a **case1(1)** edge `edgeShear = id`, so
  `stepMap u = blockBlowupMap center pivot u =: Bu`.

`StepInv` (conjunct-1) at path `p`, witness `q`: for all `i`,
`(coreGen i ∘ foldG p) u = ∑_j q i j u · (foldB p u · foldResid p j u)`, plus continuity and
`(coreGen i ∘ foldG p) 0 = 0`.

The carried invariant `FoldStepInvAt (supportAt parent) p` = (this `∃q, StepInv`) AND
(conjunct-2: each `foldResid p j` is degree-1 supported on `supportAt parent`, i.e.
`foldResid p j u = ∑_{s∈S_full} c_s(u)·u_s` with `c_s` continuous — the ∃c part; plus a per-layer
affine grade).

## The case1(1)-boost δ=1 sub-case, precisely

- Parent `cleared = 0` (δ=1). `supportAt parent = blockCoords d S` =: `S_full` (the FULL layer-`S`
  residual block, columns capped by `widthMinUpto`).
- The oracle's case1(1) transition (`stepCase11`) KEEPS `(layer, cleared)` — only mutates a divisor's
  rank profile. So **child cleared = 0, child support = `S_full` (unchanged)**.
- `center` (pinned `canonCenterOf` for case1(1)) = `{pivot} ∪ (PARTIAL block: cols ∈ [0, runLen))`
  with `runLen < widthMinUpto`. So `center ∩ S_full = partial block ⊊ S_full`.
- `pivot` (pinned `canonPivotOf` for case1(1)) = `s.divBirthCoord[mergeIdx]` = the IMMUTABLE birth
  corner of a divisor born at an **EARLIER layer** `S' < S`. So **`pivot ∉ S_full`** (different layer).

The child conjunct-1 to prove (with `edgeShear = id`, so child residual `= foldResid p (cast j) (qm u)`,
`qm u k = if k=pivot then 1 else u k`):
`(coreGen i ∘ foldG p)(Bu) = (u_pivot · foldB p (Bu)) · ∑_j q' i j u · foldResid p (cast j) (qm u)`.

## My obstruction analysis (pressure-test this)

Since `foldResid p j` is degree-1 on `S_full` and `pivot ∉ S_full`, `qm` (which only changes the
pivot slot) leaves the residual unchanged: `foldResid p (cast j)(qm u) = foldResid p (cast j) u`
("residual stays") — IF the ∃c coefficients also ignore the pivot slot (do they? c_s are general
continuous fns; unclear).

Try witness `q' = q ∘ Bu`. Suffices (dividing the common `foldB p (Bu)`):
`∑_j q i j (Bu) · foldResid p j (Bu) = u_pivot · ∑_j q' i j u · foldResid p (cast j) u`.

Evaluate the LHS at `u_pivot = 0`: `Bu|_{pivot=0}` zeroes ALL of `center` (pivot slot → 0, and
partial-block coords → 0·u = 0), leaving `S_full ∖ partial` coords untouched. Since the residual
reads those untouched coords, `foldResid p j (Bu|_{pivot=0}) ≠ 0` in general, so the LHS at
`u_pivot=0` is generally NONZERO — but the RHS is `u_pivot·(…) = 0` there. So the identity FAILS
with `q'=q∘Bu` UNLESS `(coreGen i ∘ foldG p)(Bu)` (equivalently `foldB p(Bu)·∑q·foldResid p(Bu)`)
vanishes at `u_pivot=0`.

That vanishing would follow if **`foldB p` carries the `u_pivot` factor** — i.e. `foldB p(Bu)` → 0 as
`u_pivot → 0`. `foldB p = ∏_{edges e'} (u_{pivot_{e'}})^{δ_{e'}} ∘ pullbacks`. The case1(1) pivot is a
REUSED birth corner: `divBirthCoord[mergeIdx]` = the `(layer,cleared)` corner recorded when that
divisor was BORN at an earlier case1(2)/case2 edge — whose pinned pivot (`canonPivotOf`) was exactly
that corner, at δ=1, so `foldB` gained a `(u_pivot)^1` factor there. So `foldB p` PLAUSIBLY carries
`u_pivot` — but this is PATH-HISTORY, encoded (if at all) only via `p.IsRealBranch e`, NOT via `hinv`.

## Questions
1. Is my obstruction correct — does `q'=q∘Bu` fail, and does the leaf genuinely need `foldB p(Bu)`
   to vanish at `u_pivot=0`?
2. Is "`foldB p` carries the birth-pivot factor" the right mechanism, and is it derivable from
   `p.IsRealBranch e` (which pins every earlier edge's pivot to `canonPivotOf` and gives the full
   parent branch recursively)? What is the cleanest inductive statement of that path-invariant?
3. Is there a SIMPLER route I'm missing (e.g. the "residual stays" + a different `q'`, or a fact
   about `coreGen ∘ foldG` vanishing on the center-zero locus that follows from `hinv` alone)?
4. If it genuinely needs a new path-invariant, is that faithful to Aoyagi's construction (the reused
   exceptional divisor IS the earlier blow-up's exceptional coordinate), or a sign the one-step leaf
   statement is mis-scoped and should carry a `foldB`-divisibility conjunct?

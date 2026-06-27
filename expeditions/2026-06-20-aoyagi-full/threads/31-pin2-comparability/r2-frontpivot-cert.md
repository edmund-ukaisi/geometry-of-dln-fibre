# hproducer (b) repair — VERDICT: option A (comparability) is SOUND; the contained fix

The 6th L2 catch: `hproducer` conjunct (b) `∑deepestEFull²(split w) = Sreg(w)` is FALSE as an EQUALITY
for a non-front pivot `J` (banked `hproducer-verdict.md`, FACT 3 witness `17.98 ≠ 23.65`). The controller
asked: (A) does the COMPARABILITY `∑deepestEFull² ≍ Sreg` hold (the contained repair), or (B) must we do
the front-pivot WLOG? **Verdict: A HOLDS — comparability is sound, the contained repair applies, no
headline restructure, no PIN1 touch.** Decorrelated Codex (xhigh) independently reached the same verdict.

## A — comparability HOLDS (the floor refutation was incoherently based)

The apparent refutation (`deepestEFull → const > 0` while `Sreg → 0`) compares the pivot-normalized
target against a threshold-normalized `−1` corner WITHOUT transporting the basepoint. But the basepoint
IS transported — banked fact `deepestEFull_base : deepestEFull 0 = 0` (`DeepestGaugeConstruction.lean:1412`).
Both `deepestEFull²(w)` and `Sreg(w)` are continuous and VANISH at `w0`. A path `w → w0` therefore CANNOT
keep one bounded below while the other → 0 (Codex's trap, decisive here).

**Why both vanish coherently (the structural reason, from the def).** `framedParamsPivot`'s last layer
(`DeepestFramedProductPivot.lean:116`) is `reindex(rThr.symm, pivotThr(pivotJSucc J).symm)(fromBlocks 1 0 0
0)` [corner] `+ P·reindex(rThr.symm, pivotThr(pivotJSucc J).symm)(fromBlocks readX readY readZ T)·Q`
[deviation]. **The corner AND the deviation reads go through the SAME `pivotThr.symm` column reindex** —
so `deepestEFull`'s residual at `w0` is the pivot corner (residual 0), and away from `w0` the deviation
is in the same column convention, transported coherently.

**The exact certificate.** Near `w0` both energies are positive-definite QUADRATIC FORMS in the
deviation `dev` (no constant — corner residual 0, subtracted exactly in both): `deepestEFull² = ‖A·dev‖²`,
`Sreg = ‖B·dev‖²`, where `A, B` are the two column conventions (`A` = colPerm∘QL∘thr-reindex, `B` =
QL∘piv-reindex). Both `A, B` are products of an INVERTIBLE `QL` and a column PERMUTATION ⇒ both Gram
forms `AᵀA, BᵀB` are positive-definite with TRIVIAL (equal) kernel. So:

    c₁·Sreg(w) ≤ deepestEFull²(w) ≤ c₂·Sreg(w),  [c₁,c₂] = the generalized eigenvalues of (AᵀA, BᵀB).

Exact (r=1,H0=1,H2=2, J:0↦1, `QL=[[2,1],[0,3]]`): both Gram eigenvalues `{3.394, 10.606}` (identical
spectra), generalized eig `[c₁,c₂] = [0.5195, 1.9250]`. The FACT-3 witness `17.98/23.65 = 0.760 ∈
[0.52,1.93]` ✓ — consistent (it shows equality fails, NOT comparability). This is the SAME mechanism as
S5c (a bounded-invertible reparametrization → comparable quadratic norms); CONTRAST the original PIN2
failure where the T=0 reg energy had a genuine KERNEL mismatch (the gauge direction `Y0`), which a
column permutation does NOT have.

**Difference from the dead option-2:** there the two energies were the T=0 vs FULL product (DIFFERENT
matrices, kernel mismatch). Here they are the SAME product under two INVERTIBLE column reindexings — the
permutation/QL preserve the kernel, so the forms are uniformly comparable.

## The contained build-ready repair (NO headline restructure, NO PIN1 touch)

Restate `hproducer` conjunct (b) from the EQUALITY to the two-sided COMPARABILITY:

    -- WAS (false for non-front J):
    --   ∑ i, (deepestEFull … (split w)) i ^ 2 = Sreg
    -- NOW (sound):
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      c₁ * Sreg ≤ (∑ i, (deepestEFull … (split w)) i ^ 2)
        ∧ (∑ i, (deepestEFull … (split w)) i ^ 2) ≤ c₂ * Sreg

This is EXACTLY the shape `deepest_loss_squeeze` already folds (it consumes the core via
`core_comparability_squeeze`'s two-sided `c₁/c₂`, NOT an equality). The squeeze's `c₁/c₂` arithmetic
absorbs the reg comparability constants into the existing endpoint-frame constants — the SAME folding the
core arm already does. **`deepest_loss_squeeze` needs `∑deepestEFull² ≍ Sreg`, never the equality
(`hSreg_eq`'s `=` was the over-strong phrasing).**

**Build-ready atom (the comparability lemma):**

    theorem deepestEFull_sq_comparable_Sreg (H r hr hL J Pf Qf …) (w ∈ U) :
      ∃ c₁ c₂, 0 < c₁ ∧ 0 < c₂ ∧
        c₁·Sreg ≤ ∑(deepestEFull (split w))² ∧ ∑(deepestEFull (split w))² ≤ c₂·Sreg

Proof route: both = `‖(column-reindex)(residual-deviation product)‖²_reg` with the residual product
shared (the S2 telescope: `prod(framedParamsPivot) = P0·prod(paramsSymm w)·QL`, hS3b normalizes the
corner). The two column reindexings differ by a fixed permutation `π_J` composed with the invertible
`QL`; `conjugation_frobenius_comparable`-style (the banked `dlnLoss_two_sided_of_frame` leaf already has
the invertible-conjugation comparability machinery) gives the two-sided bound. The constants are the
operator-norm bounds of `π_J·QL` and its inverse — bounded since `QL` is a unit frame.

## Scope / caveat (HONEST — the one residual)

- The PD/comparability certificate is EXACT at **r=1, H0=1, H2=2** (generalized eigenvalues, both forms
  PD). The STRUCTURAL argument (corner+deviation share `pivotThr.symm`; both vanish at w0; the two
  column reindexings are invertible ⇒ kernel-equal ⇒ comparable) is convention-uniform and does NOT
  depend on the sizes. But I did NOT symbolically enumerate H0>r (the `P10` block present) — a hand
  numeric model that mis-placed the corner (colPerm'd it) spuriously FAILED, confirming the result is
  SENSITIVE to getting the corner placement right (corner via `pivotThr.symm`, NOT colPerm'd). The
  formaliser must read the corner off the SAME `pivotThr.symm` as the deviation (as the def does) — then
  the comparability is the banked invertible-conjugation machinery. **Recommend: confirm the comparability
  lemma's proof uses the SHARED-`pivotThr.symm` structure (corner + deviation), not a colPerm of the
  whole product** — that is the soundness-critical point.

## If A is ever found to fail (the fallback — B, validated)

Codex independently validated R2 (front-pivot WLOG) as ALSO sound, should A's general-H proof snag:
- B1 (MP): `A_{L-1} ↦ A_{L-1}·Π` is a coordinate permutation, `|det|=1` ⇒ rlctAt-invariant. ✓
- B2 (loss identity, EXACT — I verified symbolically): `‖∏A − B‖²_F = ‖∏(A·Π) − BΠ‖²_F` (Π orthogonal,
  `∏(A·Π last)=(∏A)Π`). ✓ (`dlnLoss H B at A = dlnLoss H (BΠ) at (A with last·Π)`).
- B3: `rank(BΠ)=rank(B)=r`; BΠ's pivots = front ⇒ `pivotThr=rThr` ⇒ (b) holds. **Caveat (Codex): Π must
  be absorbed into the endpoint frame coherently — `QL` need not commute with Π.**
- B4: does NOT touch PIN1 (only a fixed output-basis relabel; derivatives conjugate covariantly).
B is a global convention shift (relabel every `B`/`prod`/frame/statement) — MORE disruptive than A. Prefer
A; B is the validated fallback.

## Net
**Option A (comparability) is SOUND — the contained repair.** Restate `hproducer` (b) as `≍`, prove via
the banked invertible-conjugation comparability (corner + deviation both `pivotThr.symm`-aligned), fold
the constants into the squeeze (which already accepts a two-sided core). No headline restructure, no PIN1
touch. The one soundness-critical point: the proof must use the SHARED-`pivotThr.symm` corner placement.
The verdict's `17.98≠23.65` refuted the EQUALITY (correctly) but not the COMPARABILITY. B (front-pivot
WLOG) is the validated fallback if A's general-H proof snags.

## Files
- `/tmp/a_correct.py`, `a_faithful.py`, `a_final.py`, `a_kernel.py`, `a_general.py`, `a_fail_b_verify.py`
  (one-off; the corner-placement sensitivity is the lesson — `a_kernel.py` has the PD certificate).
- `codex/r2-frontpivot-{prompt,answer}.md` (answer file polluted by Codex's file-cat exploration; the
  verdict prose is the last ~50 lines); `/tmp/s5c_codexclean/answer.md` (the clean comparability consult).

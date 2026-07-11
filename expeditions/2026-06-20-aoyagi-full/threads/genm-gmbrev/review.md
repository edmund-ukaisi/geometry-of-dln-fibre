# Review — RouteMSJGramMinorBound (single-minor Gram lower bound)

Reviewer: genm-gmbrev (independent fidelity/soundness audit).
Target: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGramMinorBound.lean`
(worktree `agent-ad18a3af1acad2526`, ~208 LoC).

## Verdict: PASS

Both results denote exactly what they claim; statements faithful, proofs sound,
forced axioms clean, non-vacuity genuine. One minor (non-blocking) simplification note.

## Forced axiom check (did NOT trust the leaf's own claim)

Copied the module verbatim into a self-contained scratch (`/tmp/scratch_gmb.lean`, no
import of the module → immune to stale-olean `sorryAx` masking) and fresh-elaborated with
`lake env lean` (exit 0). `#print axioms`:

- `det_submatrix_sq_le_det_gram` → `[propext, Classical.choice, Quot.sound]`
- `det_le_det_of_posSemidef_le`  → `[propext, Classical.choice, Quot.sound]`
- `one_le_det_of_one_le`         → `[propext, Classical.choice, Quot.sound]`
- `real_dotProduct_gram`         → `[propext, Classical.choice, Quot.sound]`

Full `scripts/lb` build of the module also green (2627 jobs, exit 0). No sorry/axiom.

## (1) Fidelity — `det_submatrix_sq_le_det_gram` : PASS

`(M.submatrix id S).det ^ 2 ≤ (M * Mᵀ).det`, `M : Matrix (Fin b) (Fin q) ℝ`,
`hS : Function.Injective S`, `S : Fin b → Fin q`.

- `M.submatrix id S` has entries `M (id i) (S j) = M i (S j)`: rows unchanged, columns
  reindexed by `S` → a genuine `b×b` column-submatrix. Injective `S` ⟹ `b` distinct
  columns; for a `b×q` matrix every `b×b` minor uses all `b` rows, so this ranges over
  ALL `b×b` column-minors. Faithful to "square of ANY b×b column-minor ≤ det(Gram)".
- `M * Mᵀ` is the `b×b` Gram. `^2` is the square. No sign issue (det squared).
- `b ≤ q` is not stated separately but is FORCED by `hS` (pigeonhole); when `b > q` no
  injective `S` exists, so the theorem is unusable there — expected, honest vacuity, and
  the docstring notes "Injectivity of S forces b ≤ q." No hidden weakening hypothesis.
- Name = content: says `≤` (single-term lower bound), not `=` (full Cauchy–Binet). The
  docstring correctly frames it as dropping all-but-one nonnegative Cauchy–Binet term.
  No overclaim.

## Non-vacuity : GENUINE (in-file, confirmed)

Two in-file `example`s, both elaborate green in the fresh build:
- applies the theorem to concrete `M = !![1,2,3; 0,1,4]` (2×3), `S = ![0,1]` (injective
  `by decide`);
- proves the selected minor `det = 1` (nonzero).

Hand-check: minor `[[1,2],[0,1]]` det `= 1`; `M Mᵀ = [[14,14],[14,17]]`, det `= 238−196 =
42`. Bound reads `1 ≤ 42` — a real, non-trivial constraint (LHS positive, not the trivial
`0 ≤ det`).

## (2) Soundness — `det_le_det_of_posSemidef_le` : PASS

`(hA : A.PosSemidef) (hsub : (B − A).PosSemidef) : A.det ≤ B.det`, general `n`.
Hypotheses correctly encode Loewner `A ⪯ B` (A PSD ∧ B−A PSD). Case split complete:
- `B` PSD from `(B−A) + A` (`PosSemidef.add` + `sub_add_cancel`).
- A-singular (`det A = 0`): `0 ≤ det B` via `hB.det_nonneg`. Correct.
- A-PosDef (`det A ≠ 0` ⟹ PD via `posDef_iff_isUnit`): `C = W B Wᵀ` with `W = A^{−1/2}`;
  `C − 1 = W (B−A) Wᵀ` PSD (via `PosSemidef.conjTranspose_mul_mul_same Wᵀ`, `(Wᵀ)ᴴ = W`);
  `1 ≤ det C` (`one_le_det_of_one_le`); `det C = (det A)⁻¹ · det B`; so `det B = det A ·
  det C ≥ det A`. Correct.
- `one_le_det_of_one_le`: `det C = ∏ eigenvalues`; each eigenvalue `μ` has `μ − 1 ∈
  spectrum(C−1)` (valid: `algebraMap(μ−1) − (C−1) = algebraMap μ − C` by `abel`, then
  `spectrum.mem_iff`), and spectrum of the PSD `C−1` is `≥ 0`. So `μ ≥ 1`, `∏ ≥ 1`. Valid.

Confirmed Mathlib lemma semantics used (v4.29): `of_dotProduct_mulVec_nonneg`,
`conjTranspose_mul_mul_same (hA) (B) : PosSemidef (Bᴴ*A*B)`,
`posSemidef_iff_isHermitian_and_spectrum_nonneg`, `IsHermitian.det_eq_prod_eigenvalues`,
`PosSemidef.det_sqrt` — all match the proof's usage.

## `gram_normalizer` (private) : PASS

For `A` PD: `W = (CFC.sqrt A)⁻¹` is symmetric, `W A Wᵀ = 1` (via `sqrt·sqrt = A` and
`nonsing_inv`), `det W ≠ 0`, `|det W| = (√ det A)⁻¹` (via `det_sqrt` = `√ det A > 0`).
Internally sound. It is an inlined verbatim copy of the banked
`RouteMSJGramSqrt.exists_gram_normalizer` (kept for self-containment); the docstring flags
this for controller dedup on integration. Correct, does not need to be identical.

## Simplification (non-blocking)

- `obtain ⟨W, hWsymm, hWAW, hWdet_ne, hWdet_abs⟩` in `det_le_det_of_posSemidef_le` binds
  `hWsymm : Wᵀ = W` and `hWdet_ne : W.det ≠ 0` but neither is used (the proof derives
  `(Wᵀ)ᴴ = W` independently, and gets `(det W)²` from `|det W|`). Both `_` these binders to
  quiet the linter — cosmetic, and legitimate given `gram_normalizer`'s shared 4-field
  signature. No correctness impact.
- 208 LoC is reasonable: it builds PSD-cone det-monotonicity AND the single-term
  Cauchy–Binet bound from scratch, both absent from Mathlib v4.29. No dead theorems.

## Decorrelated Codex read (xhigh, `codex/gmb-answer.md`)

Independent, quoted verbatim:

> 1. sound … `M.submatrix id S` is exactly the selected-column minor; `hS` is the right
>    `b ≤ q` witness, no sign issue because the determinant is squared.
> 2. sound … singular A gives det A = 0 ≤ det B since B is PSD, and nonsingular PSD A is
>    PD; conjugating by A^{-1/2} reduces to eigenvalues of C all at least 1.
> 3. sound … `xᵀ(PPᵀ)x = ‖xᵀP‖²` correct, injectivity of S makes the selected terms a
>    genuine subset sum of nonnegative squares.
> 4. sound … CFC square root is symmetric, invertible, squares to A; inverse satisfies
>    WAWᵀ = 1 and |det W| = (sqrt det A)⁻¹.
> 5. sound … only note is naming scope: "general square real matrices" is fine because the
>    PSD hypotheses force the relevant symmetry/Hermitian structure; no vacuity or
>    overclaim beyond the expected vacuity when no injective selector exists.
>
> OVERALL = PASS-WITH-NOTES

Codex is decorrelated on the math (reasoned from statements, not the tactic proof) and
lands the same verdict. Its "naming scope" note matches my finding: the only vacuity is
the expected `b > q` case, which is honest.

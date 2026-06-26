# Joint-Ψ keystones — (a) W⁻¹/⅟P00 cutoff smoothness + (b) E2 reg-preservation

The two keystone closed-form design certs gating the formaliser's Ψ-wiring tide (E1 = the LDU core-algebra
is being built in parallel). Input: `h2-diffeo-bridge-cert.md` (the joint (T1,Y1) Ψ, verified ~1e-17).
Both verified exact (sympy + numpy); the load-bearing Mathlib/banked dependencies confirmed present.
Read-only.

## (b) E2 reg-preservation — `deepestEFull ∘ Ψ = deepestEFull` (EXACT, the keystone)

`deepestEFull(x)` reads the THREE reg blocks `(P00−1, P01, P10)` of the full framed product (the reg
energy `Sreg_E`). The joint Ψ moves `(T1, Y1) ↦ (T1', Y1')`. **CLAIM: all three reg blocks are FIXED, so
`deepestEFull ∘ Ψ = deepestEFull` EXACTLY.** Verified: `|ΔP00| = |ΔP10| = 0` (machine zero), `|ΔP01| ~
5e-17`, `|ΔSreg_E| ~ 5e-17` (all r,M shapes incl. rect M0=2,M1=2,M2=1).

**The EXACT closed-form "why" (the load-bearing identity, sympy-verified, T1'-independent):**
- `P00 = A0·A1 + Y0·Z1` and `P10 = Z0·A1 + T0·Z1` contain NEITHER `T1` NOR `Y1` ⇒ **fixed automatically**
  (Ψ touches only `T1,Y1`; `A0,A1,Y0,Z0,Z1,T0` are untouched reg/spec/other-core reads).
- `P01 = A0·Y1 + Y0·T1` DOES contain both. But the Ψ closed form `Y1' = Y1 + A0⁻¹·Y0·(T1 − T1')` is
  PRECISELY the E2 solution: compute
  ```
  P01' − P01 = A0·(Y1'−Y1) + Y0·(T1'−T1)
             = A0·[A0⁻¹·Y0·(T1−T1')] + Y0·(T1'−T1)     [substitute Y1'−Y1]
             = Y0·(T1−T1') + Y0·(T1'−T1)               [A0·A0⁻¹ = I]
             = 0.                                       EXACT, ∀ T1'.
  ```
  The mechanism: `Y1`'s correction `A0⁻¹·Y0·(T1−T1')`, after left-multiplication by `A0`, EXACTLY
  cancels the `Y0·(T1'−T1)` that moving the core injects into `P01`. The `A0·A0⁻¹ = I` cancellation is
  the heart. So **moving the core `T1` is COMPENSATED by `Y1` to hold `P01` fixed** — by the DEFINITION
  of `Y1'`, regardless of `T1'`.

**Difficulty: EASY-to-CONTAINED (the keystone is the LIGHTEST piece).** The reg-preservation is an EXACT
algebraic identity (`A0·A0⁻¹=I` + block linearity) — NOT germ, NOT O(read), NOT cutoff-restricted. It
holds on the WHOLE chart where `A0` is invertible (where `Y1'` is well-defined). In Lean: `P00'=P00`,
`P10'=P10` by `rfl`/`congr` (T1,Y1 don't appear); `P01'=P01` by the one-line `A0·A0⁻¹=I` cancellation
(`mul_inv_cancel`-style + `Matrix.mul_add`/`add_sub`). The block-read = `deepestEFull` value is the
`regResidualPack` packing (banked). **~tens of LoC, the easiest of the joint-Ψ pieces.** The load-bearing
fact is just that `Y1'` is DEFINED as the E2 solution — which the diffeo-bridge cert's closed form is.

## (a) W⁻¹ / ⅟P00 cutoff inverse-smoothness

`W := I_{M1} + Z1·A1⁻¹·A0⁻¹·Y0` (M1×M1), `⅟P00`, `P00 := A0·A1 + Y0·Z1` (r×r). Both used in the Ψ closed
form (`T1' = W⁻¹·[…]`, `K = Z1·⅟P00·Y0`).

**The invertibility locus (exact):** at `wstar` (all reads 0): `A0=A1=I`, off-pivot reads `=0` ⇒
**`W(wstar) = I` and `P00(wstar) = I`** (both invertible). So the common locus
`U_inv = {det(1+X0)≠0} ∩ {det(1+X1)≠0} ∩ {det W ≠ 0} ∩ {det P00 ≠ 0}` is an OPEN nbhd of wstar (each det is
continuous, `=1` at wstar). Verified: `min|det W|, min|det P00| → 1` as scale → 0.

**The cutoff construction (reuses the banked `schurCutoffShift` pattern):** χ a `ContDiffBump` with χ=1 on
a ball `B(wstar, δ1) ⊂ U_inv`, `tsupport χ ⊂ U_inv`. Define
`W⁻¹_χ := I + χ·(W⁻¹ − I)` (= `W⁻¹` on χ=1, = `I` off `tsupport χ`), similarly `⅟P00_χ`. Globally
`ContDiff ⊤` because: (i) `W⁻¹`, `⅟P00` are `ContDiff` ON `U_inv` (matrix inverse smooth where det≠0); (ii)
χ a smooth bump; (iii) the cutoff stitches to the constant `I` off-support (`continuous`/`contDiff_of_tsupport`).

**Load-bearing Mathlib/banked deps (CONFIRMED present):**
- `ContDiffAt.inv` (Mathlib `Analysis/Calculus/ContDiff/Operations.lean:807`, scalar) + the matrix-entry
  route (`nonsing_inv` = adjugate/det, each entry polynomial/det ⇒ `ContDiffAt` where det≠0).
- The per-layer `(1+readX_s)⁻¹` `ContDiffAt`-on-`unitSet` is ALREADY BANKED (`DeepestSchurSmooth.lean:117`),
  and `contDiff_schurCutoffShift` (`:208`, the χ-cutoff to global `ContDiff⊤`) is the EXACT pattern.

**Difficulty: MODERATE — the heaviest sub-piece is the COMPOSITE inverse-smoothness.**
- `W = I + Z1·A1⁻¹·A0⁻¹·Y0` is a COMPOSITE of the banked `(1+X_s)⁻¹` + reads ⇒ `ContDiff` on `U_inv` by
  `ContDiff.mul` of the banked pieces; then `W⁻¹` by `ContDiffAt.inv`-on-matrices (det W ≠ 0 on U_inv).
- `⅟P00 = (A0·A1 + Y0·Z1)⁻¹` is a SINGLE r×r inverse of a smooth matrix, det≠0 on U_inv ⇒ `ContDiffAt.inv`
  / `nonsing_inv` smooth-where-unit. (Note: the `⅟P00` cutoff smoothness may ALREADY be needed by S5a's
  `eventually_P00_invertible` / the leak bound — check if it's banked there; if so, reuse.)
- **Heaviest:** the matrix-inverse `ContDiff`-where-unit for `W⁻¹` and `⅟P00` (the per-layer one is banked,
  these are the COMPOSITE / product-pivot extensions) + the χ-cutoff to global. ~1 tide (the
  `DeepestSchurSmooth` pattern + 2 new composite-inverse lemmas). NOT a wall — the primitive + the pattern
  are banked; the work is the composite + the cutoff plumbing.

## Honest difficulty ranking (the two keystones)
- **(b) E2 reg-preservation: EASY-CONTAINED (~tens of LoC).** An EXACT identity (`A0·A0⁻¹=I` cancellation
  + T1,Y1-freedom of P00,P10). The lightest piece — the keystone is NOT the bottleneck. Load-bearing
  conceptually (it's WHY the bridge works), trivial mechanically.
- **(a) W⁻¹/⅟P00 cutoff smoothness: MODERATE (~1 tide).** Heaviest sub-piece = the composite/product-pivot
  matrix-inverse ContDiff-where-unit (the per-layer `(1+X)⁻¹` is banked; `W⁻¹`,`⅟P00` extend it) + the
  χ-cutoff (the `schurCutoffShift` pattern, banked). NOT new mathematics — the primitives + pattern exist.

## Scope / caveats (honest)
- (b) is EXACT and shape-general (sympy + numpy all shapes). The one in-Lean subtlety: `deepestEFull`'s
  value is the `regResidualPack`-packed reg-block energy, so `P00'=P00 ∧ P01'=P01 ∧ P10'=P10` ⇒
  `deepestEFull∘Ψ = deepestEFull` needs the packing-respects-blocks step (banked, `deepestEPivot_sq_sum_eq_blocks`-style).
- (a)'s cutoff is the standard `ContDiffBump`; the only confirm is that `ContDiffAt.inv` lifts to the
  matrix `nonsing_inv` cleanly at v4.29 (the per-layer banked lemma already does this for `(1+X)⁻¹`, so
  the route is proven; `W`,`P00` are the same shape of argument on a composite/sum). Low risk.
- Both are L2-producer-local; the L≥3 gap is separate (the diffeo-bridge cert's scope).

## Net
Both keystones are build-ready. **(b) is the EASY one** (exact `A0A0⁻¹=I` identity, ~tens of LoC — the
"why P01 is fixed" is a one-line cancellation, the keystone is conceptually load-bearing but mechanically
trivial). **(a) is MODERATE** (~1 tide — the composite/product-pivot matrix-inverse ContDiff-where-unit +
the χ-cutoff, reusing the banked `DeepestSchurSmooth`/`schurCutoffShift` pattern + `ContDiffAt.inv`). No
new mathematics; the load-bearing primitives are confirmed present. These + E1 (in build) wire the joint Ψ.

## Files
- `/tmp/h2joint/keystone.py` ((b) all-blocks-fixed, all shapes), `exact_b.py` ((b) the exact `P01'−P01=0`
  closed-form identity), `smooth_a.py` ((a) U_inv + cutoff + the heaviest sub-piece). Banked deps:
  `DeepestSchurSmooth.lean:117/208` (the (1+X)⁻¹ cutoff pattern), Mathlib `ContDiffAt.inv`. Input:
  `h2-diffeo-bridge-cert.md` (the joint Ψ closed form).

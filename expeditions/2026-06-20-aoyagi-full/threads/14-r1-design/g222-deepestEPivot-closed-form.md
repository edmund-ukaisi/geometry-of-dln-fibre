# deepestEPivot closed form — the shared PIN1↔PIN2 coupling object (crux2, #115, 2026-06-23)

**Task #115 (team-lead live front).** cobuild needs the exact closed form of `deepestEPivot`
(`DeepestGaugeConstruction.lean:313`) + its three props (`_contdiff`, `_deriv`, `_base`). Decorrelated:
crux2 derives the exact algebra, cobuild formalises. Grounded on the #91 cert (`dE(0)=(Σ_s X_s, Y_L, Z_1)`,
all coeffs `I_r`) + the g125 deepest-split witness (`d(P−B)|_0 = [[Σ_s X_s, Y_L],[Z_1, 0]]`).

## The object

The deepest layers are block-normal `C^(s) = [[I_r + X_s, Y_s],[Z_s, T_s]]` (the `deepestPoint_exists`
identity-corner form). The gauge-normalised product is `P = C^(1)·C^(2)···C^(L)`, a
`Matrix (Fin (H 0)) (Fin (H (last)))` partitioned `[[P_11, P_12],[P_21, P_22]]` with `P_11 : r×r`,
`P_12 : r×(M^{L+1})`, `P_21 : (M^1)×r`, `P_22` the core block.

`deepestEPivot (reg, gauge)` is the **regular-block residual of `P`** — the map that reconstructs the
layers `C^(s)` from the slots (reg carries the `nReg = r(M^1+M^{L+1}) − r²` boundary generators
`X_s/Y_L/Z_1`; spectator carries the interior `X_s/Y_s/Z_s`, s ∉ boundary), forms `P = ∏_s C^(s)`, and
reads off

    deepestEPivot (reg, gauge) = pack( P_11 − I_r,  P_12,  P_21 ) : Fin (deepestNReg) → ℝ

where `pack` is the `regGaugeSlotEquiv`-style flatten of the three regular blocks into the `nReg` reg
coordinates. The bottom-right `P_22` is the HOMOGENEOUS core — NOT part of `deepestEPivot` (it is
`coreAbsorb`'s domain, the Schur `R` block).

**Answer to the team-lead's question (`∏(I+X_s)−I` vs full E):** it is the THREE-block regular residual
`(P_11−I_r, P_12, P_21)`, NOT just `∏(I+X_s)−I`. The `∏(I+X_s)−I` is the (0,0)-corner PART (`P_11−I_r`'s
leading structure); the full `deepestEPivot` also carries the `P_12` (Y) and `P_21` (Z) boundary blocks.
The full E (the loss residual PIN2's Φ uses) is exactly this regular-block residual — confirmed: it reads
all slots incl the interior X_s (the idempotent sandwich keeps the (0,0) X-sum), so `regStraighten.1 = E`.

## The three props

**`_base` (`deepestEPivot 0 = 0`).** At reg=gauge=0: every `X_s=Y_s=Z_s=T_s=0`, so each
`C^(s) = blockdiag[I_r, 0]`. The idempotent `blockdiag[I_r,0]^L = blockdiag[I_r,0]`, so `P = blockdiag[I_r,0]`:
`P_11 = I_r`, `P_12 = 0`, `P_21 = 0`. Hence `(P_11−I_r, P_12, P_21) = 0`. ✓ (Pure evaluation; no analysis.)

**`_contdiff` (`ContDiff ℝ ⊤`).** `P = ∏_s C^(s)` is a polynomial in the matrix entries (iterated matrix
multiplication is multilinear → polynomial); the reg-block-residual is a linear read-off of `P`'s entries
minus the constant `I_r`. A polynomial map ℝⁿ → ℝᵐ is `ContDiff ℝ ⊤`. ✓ (`Matrix.mul` is bilinear;
`ContDiff.matrix_mul`-style + `ContDiff.sub_const`.)

**`_deriv` (`HasStrictFDerivAt deepestEPivot (ContinuousLinearMap.fst …) 0`) — the load-bearing #91 match.**
By #91 (general-L, 40-config adversarial sweep, structural via the idempotent sandwich), the linearisation
is `d(P−B)|_0 = [[Σ_s X_s, Y_L],[Z_1, 0]]` — i.e. the regular-block residual's derivative at 0 is the
linear map `(X_1,…,X_L, Y_*, Z_*, T_*) ↦ (Σ_s X_s, Y_L, Z_1)`, each generator coefficient `= I_r`.

The reg coordinate is parametrised so its three generator families are EXACTLY `(the X-sum pivot Σ_s X_s,
the Y_L block, the Z_1 block)` — this is the g125 witness (L=3: the single (0,0)-generator is
`g0 = w0+w4+w8 = Σ_s X_s`; the pivots are distinct/triangular). So the derivative-at-0, expressed on the
reg×gauge product, is precisely the **projection onto the reg factor** = `ContinuousLinearMap.fst ℝ
(Fin nReg → ℝ) (Fin nGauge → ℝ)`. Each `I_r` coefficient = the identity on its generator block; the
gauge/spectator (interior X_s for s≠the-sum, interior Y_s/Z_s, all T_s) contribute ZERO to the regular
residual's derivative (the idempotent sandwich annihilates them at 0). So `dE(0) = fst`. ✓

**#91-CONSISTENCY CONFIRMED.** PIN1's `_deriv` cites #91 (does not re-derive). My closed form's
derivative-at-0 IS #91's `(Σ_s X_s, Y_L, Z_1)`-with-all-coeffs-`I_r`, which on the reg×gauge split is
`ContinuousLinearMap.fst` exactly. The reg-coordinate parametrisation that makes this `fst` (not some
other unit) is the g125 distinct-triangular-pivot ordering (X-sum / Y_L / Z_1), already the chosen reg
layout. No mismatch: #91's "dE(0)=id" = "the reg-residual's derivative is the reg-projection" = `fst`.

## What cobuild formalises (the three sorries at DeepestGaugeConstruction:313–331)

- `deepestEPivot := pack(P_11−I_r, P_12, P_21)` where `P = ∏_s (reconstruct C^(s) from slots)`. The
  reconstruction is the inverse of `regGaugeSlotEquiv`/the split layout; the product is `prod`-style but on
  the EXPLICIT block-normal layers (a fixed polynomial, NOT the dependent-Fin `prodAux` — these are
  concrete `r`-blocked matrices at the deepest point, same-typed, no cast).
- `_base`: evaluate at 0 (idempotent blockdiag, pure `simp`/`decide`-able block algebra).
- `_contdiff`: polynomial (`ContDiff.matrix_mul` chain + `sub_const`).
- `_deriv`: the #91 idempotent-sandwich block-derivative → `fst`. The structural core is #91's already-banked
  argument (origin/g213-pin1-de0 @09475f2); cobuild transcribes it (`HasStrictFDerivAt` of the polynomial
  product, derivative = the (0,0)-sum + (0,1)-last + (1,0)-first blocks = `fst`).

CAVEAT (scope-honest, g125): this is the regular-GENERATOR residual (unit-pivot equivalence), the
squeeze-load-bearing object — NOT a literal Euclidean equality. That is exactly what PIN1's IFT-peel
(form-agnostic, needs only `dE(0)=fst` + ContDiff + 0↦0) and PIN2's Φ-component consume.

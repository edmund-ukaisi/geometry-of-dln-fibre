# Cert — the (2,2,2) `hnode` Schur presentation (fm3, 2026-06-23)

The exact-algebra certificate for the (2,2,2) anchor `hnode` (the producer input
`RouteMNodeDescent.ofNodePresentation` consumes). Derived with sympy (exact ℚ/symbolic, verified
`core − G2 = 0`). This is the "write the full calculation by hand before formalising" step — the
formalisation transcribes this, it does not re-derive it.

## Setup

`myF222 (x) = ‖A·B‖²`, `A = [[x0,x1],[x2,x3]]`, `B = [[x4,x5],[x6,x7]]` (Case222Resolution.lean:34).
Step-1 A-pivot blow-up (chart `φ₁`, pivot `a00 = y0`): `a00=y0, a01=y0·y1, a10=y0·y2, a11=y0·y3`;
`B` passes through. So `A = y0·Â`, `Â = [[1, y1],[y2, y3]]`.

## The factorization (verified)

```text
myF222 ∘ φ₁ = y0² · core,    core = ‖Â·B‖²
```

`y0²` is the regular blow-up monomial axis (the `|det| = y0³` Jacobian feeds the cover, not the squeeze).
The residual `core` is the per-node Schur object.

## The Schur `hnode` data (the `∑Erow² + ‖bcol·Erow + SΓ‖²` form)

With pivot block `= 1` (top-left of `Â`):

```text
Erow = [x4 + y1·x6,  x5 + y1·x7]          -- the pivot-row product (row0 of Â·B); nReg = 2 squares
bcol = y2                                  -- the pivot column Â[1:,0]; the m−1 = 1 lower row
S    = y3 − y2·y1                           -- the Schur complement (d − b·c)
SΓ   = S · [x6, x7] = [(y3−y2y1)·x6, (y3−y2y1)·x7]   -- the reduced core
```

VERIFIED (sympy, `core − [∑Erow² + ∑(bcol·Erow + SΓ)²] = 0`):

```text
core = (∑_{k} Erow_k²) + (∑_{k} (bcol·Erow_k + SΓ_k)²)
```

This is EXACTLY the `hnode` conjunct `flatCore w = (∑_j w.1_j²) + (∑_{i,j} (bcol·w.1_j + SΓ)²)` with
`w.1 = Erow` the `nReg = 2` regular coords, the single lower row `i ∈ {*}` (`Mblk` a singleton).

## The reduced core `G² = ‖SΓ‖²`

```text
G² = ∑_k SΓ_k² = (y3 − y2·y1)² · (x6² + x7²)
```

This is the reduced `(1,1,2)`-node loss: the `1×1` Schur complement `(y3 − y2y1)` against the `B`-row
`[x6,x7]` — a `dlnLoss ![1,1,2] 0`-shaped object after the reindex (the `ReducedTransport` target). Its
RLCT is `lambdaCore(1,1,2) = ½·minAdm(1,1,2) = ½·1 = 1/2` (numeric check).

## `nReg = 2`, confirmed THREE independent ways

1. **Schur derivation** (this cert): `Erow` has 2 components → 2 regular squares → `nReg = 2`.
2. **Numeric `minAdm`**: `nReg = minAdm(2,2,2) − minAdm(schurState(2,2,2)=(1,1,2)) = 3 − 1 = 2`.
3. **descentStep arithmetic**: `lambdaCore(2,2,2) = 3/2 = nReg/2 + lambdaCore(1,1,2) = 2/2 + 1/2`. ✓

The committed `case222_rlctAtOn_eq = 3/2` matches.

## What this de-risks (the anchor-through-`RouteMNodeDescent`)

The `hnode` presentation (the Explore-scan's MISSING item 5) is now derived. The remaining anchor
plumbing: (i) the `bcol`/`SΓ` as Lean functions of `Y = Fin 8 → ℝ` (or the post-blow-up coords) + the
`flatCore` def; (ii) the `ReducedTransport` instance (the det-1 MP reindex of `(y3−y2y1)·[x6,x7]` to
`Params ![1,1,2]`); (iii) the neighbourhood `hnode` proof (the `core − Schur = 0` identity above,
transcribed + the `∑bcol² = y2² ≤ T²` bound on a nbhd of the deepest point `y2 → 0`).

The C1 mechanism (hard-pivot, defect in `bcol·Erow`) is exactly this (2,2,2) shape. C5 (partial-drop)
is the SAME structure with different field values (pp-rstar #134). So the anchor derivation is the
template the general producer instantiates.

## The `ReducedTransport` target (concrete; the genuine remaining subtlety)

`Params ![1,1,2]` (L=2) `= (Fin 1×Fin 1 → ℝ) × (Fin 1×Fin 2 → ℝ)` — layer 0 a scalar `α`, layer 1 a
row `[β0,β1]`. So `dlnLoss ![1,1,2] 0 A = ‖prod A‖² = (α·β0)² + (α·β1)²` (Loss.lean:55, `prod = α·[β0,β1]`).

Matching the Schur core `G² = (y3−y2y1)²·(x6²+x7²)`: set `α = (y3 − y2·y1)` (the 1×1 Schur complement),
`[β0,β1] = [x6,x7]` (the B-row). Then `dlnLoss ![1,1,2] 0 = (α β0)² + (α β1)² = G²` — the `hredCore`
identity holds by this algebra.

**The subtlety (Explore-scan item 3, the non-trivial piece):** `redEmbed` must be a measure-preserving
`≃ₜ`, but `(y1,y2,y3,x6,x7) ↦ (α=(y3−y2y1), [x6,x7])` is NOT injective on the full `Fin 8 → ℝ` (it
forgets the regular coords `Erow`/`y2`). So the `ReducedTransport` `Y` is the POST-PEEL reduced ambient
(after the regular block `Erow` is absorbed by `schur_straighten_squeeze_of_data`'s `nReg/2` and the
pivot-column `y2` shear straightens `(y3−y2y1) ↦ y3'`). The MP shear `δ' = δ + (regular)` (the C5-style
straightening, but here for C1's Schur complement) is a det-1 transvection — measure-preserving by
`mp_schur_transvection_vec` (crux2's banked fact). After the shear, `α = y3'` is a single reduced
coordinate and `[x6,x7]` pass through, so `redEmbed : Y ≃ₜ Params ![1,1,2]` is the coordinate
identification `(y3', x6, x7) ↦ (α=y3', [x6,x7])` (the remaining `Y`-coords are the child's deeper layers,
recursed). `hzero : redEmbed 0 = 0` and `hmp` follow.

This is the one genuinely-new construction in the anchor (NOT mere transcription): the post-peel reduced
ambient `Y` + the det-1 MP shear. The rest (the `hnode` identity, `flatCore`, `bcol`/`SΓ`) IS transcription
of the verified algebra above.

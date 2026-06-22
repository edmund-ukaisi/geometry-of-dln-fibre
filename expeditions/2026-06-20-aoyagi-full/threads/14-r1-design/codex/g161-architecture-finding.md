# g161 — CONFOUND: the `DeepestGaugeChart` bundle's `loss_squeeze` is FALSE with a raw `split` regular slot

**Status:** CONFIRMED (Codex xhigh, decorrelated; sympy/numpy verified). Structural fix required to
crux2's single-writer `DeepestGaugeChart` + cobuild-sub34's `deepest_gauge_construction` bundle.

## The claim under test

The bundle `deepest_gauge_construction` (and the structure field `DeepestGaugeChart.loss_squeeze`)
asserts a two-sided squeeze near the deepest point `w0`:

    c₁·Φ(w) ≤ dlnLoss H B (flat⁻¹ w) ≤ c₂·Φ(w),   Φ(w) = ∑ (split w).1 ²  +  deepestCoreF (coreAbsorb (split w)).2.1

with `split` MEASURE-PRESERVING (`split_mp`). Because `split` is MP it is (per crux2's
`deepestSplit_exists`) a LINEAR reindex (`Fintype.equivOfCardEq` + translation), so its regular slot
`(split w).1` is a linear selection of RAW gauge coordinates (the `X_s, Y_s, Z_s` entries).

## The confound

`∑ (split w).1 ²` = ∑ (raw gauge entries)² is NOT two-sidedly comparable to the loss near `w0`.
The residual `E` that the loss actually sees is the NONLINEAR product residual, and `dE(w0)` has a
kernel (internal gauge): the loss is flat along gauge orbits that move raw coordinates.

**Explicit counterexample** (`L=2`, `H=(2,1,2)`, `r=1`; `C_1=[[1+x1],[z1]]`, `C_2=[[1+x2, y2]]`,
target `B = diag(1,0)`):

    y2 = z1 = 0,  x1 = ε,  x2 = 1/(1+ε) − 1   ⟹   ∏C = diag(1,0) exactly ⟹ loss = 0,

while the raw norm `x1² + x2² = Θ(ε²) > 0`. So the LOWER bound `c₁·(∑raw² + core) ≤ loss` fails for
every `c₁ > 0`. (numpy: loss = 0.000e+00, rawnorm = 1.83e-02 at ε=0.1; ratio → 0.) The core is empty
here (`M=(1,0,1)`, `flatDim M = 0`), so the failure is purely in the regular slot.

## The correct regular coordinates (and why the squeeze IS true with them)

The honest regular residuals are the NONLINEAR `E`:

    e = (1+x1)(1+x2) − 1,   y = (1+x1)·y2,   z = z1·(1+x2)

and then (sympy-exact, verified)

    dlnLoss = e² + y² + z² + (z1·y2)²,

with `(z1·y2)²` the reduced-core term (the `(1,1)` block; here `M`'s only nontrivial product). Near
`w0`: `e²+y²+z² = Θ(|w|²)` dominates, `(z1·y2)² = O(|w|⁴)` is higher-order ⟹ the two-sided squeeze
`loss ≍ ∑E² + core` holds. The 1-dim spectator is the gauge orbit (scale `C_1` by `t`, `C_2` by
`1/t`); loss and `e,y,z` are all invariant under it ⟹ zero-set compatibility (loss vanishes iff
`E=0 ∧ core=0`).

## The fix (option (e), symmetric with `coreAbsorb`)

Add a **`regAbsorb`** field to `DeepestGaugeChart`: a self-homeomorphism of `DeepestSplit` that

- FIXES the core slot `.2.1` and the spectator slot `.2.2` pointwise (mirror of `coreAbsorb`'s
  reg+spec fix);
- turns the RAW regular slot `.1` into the nonlinear residual `E` — a LOCAL diffeo at `0` (its
  derivative `dE(w0)` is an iso onto the regular directions: Codex confirms `E(w) = U(w)·r` with
  `U(0)` invertible in the right coordinates);
- has a bounded-unit Jacobian at `0` (`= 1` at the basepoint), so `regAbsorb_rlct` peels via crux2's
  `rlctAtOn_boundedUnit_localHomeomorph` (#72) — same machinery as `coreAbsorb_rlct`.

Then `loss_squeeze` and the RLCT-peel fields use `regAbsorb (split w)` in the regular slot:

    Φ(w) = ∑ (regAbsorb (split w)).1 ²  +  deepestCoreF (coreAbsorb (regAbsorb (split w))).2.1

(`coreAbsorb` and `regAbsorb` commute on slots since each fixes the other's target — `coreAbsorb`
acts on `.2.1`, `regAbsorb` on `.1`.) With the nonlinear regular slot the squeeze is TRUE, and the
RLCT factors `rlctAtOn(Φ) = rlctAtOn(∑raw² + core)` via TWO bounded-unit peels (reg then core).

## Why this is a structural change, not a build-around

`loss_squeeze`/`coreAbsorb_rlct` are FIELDS of crux2's single-writer `DeepestGaugeChart`, and they
hard-code `(split w).1` (raw). cobuild-sub34 cannot make these fields TRUE without the `regAbsorb`
indirection. So the structure needs the `regAbsorb` field (+ its basepoint/core-fix/spec-fix/rlct
companions) and the two `loss_squeeze`/peel fields re-spelled through it. crux2 owns the structure;
cobuild-sub34 supplies `regAbsorb` (the IFT local diffeo, `dE(w0)=id` after the linear-iso
straightening) and the matrix squeeze. `deepest_squeeze_transport` (sub-5) must re-derive through the
extra peel — a one-line `rw [Γ.regAbsorb_rlct]` after the existing `rw [Γ.coreAbsorb_rlct]`.

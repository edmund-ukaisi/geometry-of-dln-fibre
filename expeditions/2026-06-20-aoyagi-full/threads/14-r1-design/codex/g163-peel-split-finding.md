# g163 — the two gauge-absorption peels split cleanly: coreAbsorb → #71 (global), regAbsorb → #72 (local)

The two RLCT-peel fields (`coreAbsorb_rlct`, `regAbsorb_rlct`) are NOT symmetric in difficulty. The
core side is a GLOBAL shear (trivial peel); only the regular side is a genuine local diffeo.

## coreAbsorb is a GLOBAL shear (det = 1 everywhere) ⟹ #71, not #72

`coreAbsorb` turns the raw core `T_s` into the Schur complement `S_s = T_s − Z_s(I+X_s)⁻¹Y_s`. As a
map on the split coords it is the additive shear (`coreShearHomeo`)

    (reg, core, spec) ↦ (reg, core + shift(reg, spec), spec),   shift = −Z(I+X)⁻¹Y,

which is a GLOBAL homeomorphism of `DeepestSplit` (inverse `core ↦ core − shift(reg,spec)`), smooth
everywhere the gauge correction `−Z(I+X)⁻¹Y` is defined. Its Jacobian is block-lower-triangular with
identity diagonal blocks (reg fixed, spec fixed, `∂core_out/∂core_in = I`), so **det = 1 everywhere**
(numerically confirmed: `det = 1.0000…` on a random nonlinear shift).

⟹ `coreAbsorb_rlct` discharges via crux2's **#71** `rlctAtOn_boundedUnit_homeomorph` (the GLOBAL
peel, already PROVEN), with the trivial det-bound `a = b = 1`. NO IFT, NO bi-invariant `V`, NO local
machinery. (Caveat: `shift = −Z(I+X)⁻¹Y` is defined where `I+X` is invertible — a nbhd of `w0`; off
it the shear is extended/irrelevant since `rlctAtOn` is a germ. The honest object is a homeomorphism
agreeing with the shear near `w0`; det = 1 on that nbhd suffices for `hbdd`.)

## regAbsorb is a genuine LOCAL diffeo (det ≠ ±1) ⟹ #72 + bi-invariant V

`regAbsorb` turns the raw gauge coords into the nonlinear residual `E` (L=2: `e=(1+x1)(1+x2)−1`,
`y=(1+x1)y2`, `z=z1(1+x2)`). With spectator `= x1` (the orbit coord), the Jacobian determinant is

    det J = −(1+x1)²(1+x2),

so `|det J(w0)| = 1` (bounded-unit at `w0`) but `det → 0` as `x1 → −1` or `x2 → −1` — NOT a global
diffeo, the inverse (`x2 = (E−x1)/(1+x1)`, `z1 = Z(1+x1)/(1+E)`) has poles. So `regAbsorb` genuinely
needs the LOCAL peel **#72** + the bi-invariant `V` adapter (the seam under discussion).

## Consequence for the architecture

- `coreAbsorb_rlct` = #71 applied to `coreShearHomeo` with `hbdd = ⟨nbhd, 1, 1, …⟩` (det = 1). The
  `hderiv` (global) holds since the shear is smooth; `hdetmeas` from continuity. STRAIGHTFORWARD.
- `regAbsorb_rlct` = #72 applied to the IFT local diffeo, via the bi-invariant-V adapter (the one
  hard remaining seam, crux2's #72 producer contract).

So `boundedUnit_fderiv_det` (my det-bound bedrock) is for the regAbsorb side; the coreAbsorb side
needs only `det = 1` (even simpler). Also corrects a docstring overclaim: the peel needs `|det| = 1`
at `w0` (bounded-unit), NOT `dE(w0) = id` — `boundedUnit_fderiv_det` handles any CLE derivative.

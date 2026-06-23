# fm3 route-check: the blow-up→squeeze coordinate bridge does NOT compose as specified

**Status:** STOP / surface (per the prompt's "genuine design gap, not just labor" clause).
**Decorrelated:** Codex xhigh (`codex/route-check-{prompt,answer}.md`) + explicit sympy
(`/tmp/check_residual.py`, reproduced below). Codex and the algebra agree.

## The assignment's premise

Discharge the squeeze toolkit's `hnode` (in `GeneralR1Recursion.lean:610`,
`schur_straighten_squeeze_exists`) by proving `dlnLoss M 0` composed with the banked blow-up chart
`pivotBlowupOn` (`S1G5Charts.lean:384`) presents in the additive Schur form
`flatCore w = ∑ Erowⱼ² + ‖b·Erow + SΓ‖²`, deriving the layout from the blow-up construction.

## The gap (two divergent normal forms)

**(A) What `hnode` demands** — additive, positive-constant squeeze, NO Jacobian:
`flatCore = (∑ E²) + ‖b·E + SΓ‖²`, squeezed by `Φ = ∑E² + ‖SΓ‖²` with `0<c₁≤c₂`, yielding the
ADDITIVE split `rlctAtOn = nReg/2 + rlctAtOn(G²)`. Zero-locus `{E=0 ∧ SΓ=0}` (intersection).

**(B) What the banked blow-up actually produces** — the banked theorem `myF222_step1A`
(`Case222Resolution.lean:48`) for the 2-factor loss `‖A·B‖²`:
`myF222(step1A y) = y0² · Q(y)` — a PRODUCT, (pivot)²·(residual), monomial Jacobian `|y0|³`, feeding
the project's `monomialThreshold` cover lane (`g5_pivotNode`, `⨅ monomialThreshold`). Zero-locus
`{y0=0} ∪ {Q=0}` (union).

Product-vs-sum / union-vs-intersection: a regular local change of variables cannot turn `y0²·Q` into
`y0² + Q` up to positive constants near 0 (different vanishing geometry). The entire banked (2,2,2)
RLCT result (`= 3/2`) is computed through the monomial route; nothing in the atlas presents the loss
in form (A). **The squeeze toolkit is a PARALLEL resolution strategy, not a downstream consumer of
the blow-up atlas.** "Blow-up THEN squeeze on the pulled-back loss" is not supported by what is banked.

## The one salvage, and why it is ALSO not banked

The residual `Q = ‖Â·B‖²` (hard pivot `Â[0,0]=1`) DOES satisfy the Schur row-decomposition
identity (sympy-confirmed): with `Erow = ` row-0 of `Â·B`, `b = Â[1:,0]`, `S = D − b·a`,
`Q = E0² + E1² + (b·E0+SG0)² + (b·E1+SG1)²` exactly. So the squeeze could in principle apply to the
RESIDUAL `Q`, not the full pulled-back loss — `flatCore := Q`, with the pivot factor `y0²` + Jacobian
still handled by the monomial machinery.

BUT the toolkit's `hnode` regular block is `∑ⱼ (w.1 j)²` — the `nReg` regular **coordinates**
directly. The actual `Erow = (E0,E1) = (y4+y1·y6, y5+y1·y7)` are FUNCTIONS, not coordinates, and the
map `(y4,y5,y6,y7) ↦ (E0,E1,SG0,SG1)` has Jacobian RANK 2 (det 0) at the deepest point `y=0` (the
`SΓ` block degenerates to first order). So even the residual-level squeeze needs an additional, NOT
banked theorem: a coordinate straightening identifying `(E0,E1)` as `nReg=2` regular coordinates with
a complementary chart for the `Y`-factor carrying `G²=‖SΓ‖²`. That is a genuine pivot-stripping /
residual-normal-form construction, not labor on top of the atlas.

## RIGOROUS (2026-06-22, 3rd pass — the order-of-vanishing proof, after testing the literal-blowup reading)

The controller corrected: `dlnLoss M 0 ∘ pivotBlowupOn = ‖Â·A2‖²` is meant with `Â` the LITERAL
blown-up first factor (entries carry the pivot `y0`), so conjunct 1's regular block `∑w.1²` is the
blown-up pivot ROW, not the de-homogenized residual. Under THAT reading conjunct 1 holds as a bare
functional equality (sympy: with `w.1 = Erow = `row-0 of `Â·B = (y0(b00+y1b10), y0(b01+y1b11))`,
`bcol = y2`, `SΓ = y0(y3−y1y2)(b10,b11)`, `L∘blowup = ∑Erow² + ∑(bcol·Erow+SΓ)²` EXACTLY). So my
"off by x_p²" framing was the wrong defect — the equality CAN be made to hold.

BUT the defect is real and DEEPER (decorrelated: Codex xhigh + sympy, `codex/reading3-{prompt,answer}.md`):
the resulting `∑w.1²` is NOT a regular smooth block, so the toolkit's `smooth block ⟹ nReg/2` step is
UNSOUND. The clean PROOF (order of vanishing), valid for ANY split, not just mine:

> `L∘blowup` vanishes to ORDER 4 at the deepest point — every entry of `Â·B` is `y0·(B-linear)`, so the
> loss is `∑(y0·linear)² = ` order-4, with NO quadratic part. If any `w_j` were a genuine regular
> (centered, submersive) coordinate, `w_j²` contributes a nonzero QUADRATIC term to `∑w.1²`; the RHS is
> a sum of squares so that quadratic term cannot cancel. The LHS has no quadratic part. CONTRADICTION.
> Hence NO `nReg=2` regular coordinate block can satisfy conjunct 1 exactly near 0.

So conjunct 1 is dischargeable ONLY with a NON-regular `w.1` (here `Erow`, Jacobian rank 0 at 0), and
then `rlctAtOn(∑w.1²)(0) = rlctAtOn(E0²+E1²)(0) = 1/2`, NOT `nReg/2 = 1` (Codex exact: `E0²+E1² =
y0²(u0²+u1²)` after the analytic diffeo `u=(b00+y1b10, b01+y1b11)`; `∫|y0|^{-2λ}` binds at `λ<1/2`).
Feeding this into `schur_recursion_step_squeeze` (which hard-codes `nReg/2` for the block) OVERCOUNTS the
regular part by `1/2` per node — unsound, and exactly the gap between a dimension-conserving recursion
(→ ambient/2 = 4) and the true `3/2`.

ROOT CAUSE (unchanged, now rigorous): homogeneity. The blow-up makes the whole A-row a multiple of the
pivot ⟹ the pulled-back loss has no quadratic part ⟹ no regular smooth block can present it. The
squeeze datum needs a regular `∑(coord)²` block; the blow-up cannot supply one.

## SHARPENED (2026-06-22, after controller pinned hnode + re-tasked discharge-on-`dlnLoss M 0 ∘ pivotBlowupOn`)

The controller pinned hnode (3 conjuncts) and re-tasked (b1) as: PROVE the 3 conjuncts for
`flatCore := dlnLoss M 0 ∘ pivotBlowupOn` (the hard-pivot Â[0,0]=1 blow-up). This is FALSE, and the
obstruction is now pinned to its ROOT CAUSE — HOMOGENEITY (decorrelated: Codex + 3 sympy checks):

- `dlnLoss M 0` is homogeneous degree-2 in the A-block. `pivotBlowupOn active p` scales the WHOLE
  active block by the pivot `x_p` (`x_p ↦ x_p`, `x_j ↦ x_p·x_j`). So `A(blowup) = x_p · Â`
  (`Â_p = 1`), hence `dlnLoss M 0 (pivotBlowupOn …) = x_p² · ‖Â·B‖² = x_p² · Q`. The `x_p²` is FORCED
  by homogeneity — appears for ANY A-pivot `p` (verified `p = a00` AND `p = a11`). There is NO A-pivot
  chart in the atlas for which `dlnLoss ∘ pivotBlowupOn` is the bare residual `Q`.
- hnode conjunct 1 wants `flatCore w = ∑ⱼ w.1ⱼ² + ∑ᵢⱼ (bcol·w.1 + SΓ)² = Q` (the residual, a SUM).
- So conjunct 1 holds for `flatCore := Q` but is OFF BY THE FACTOR `x_p²` for
  `flatCore := dlnLoss ∘ pivotBlowupOn`. The two differ by the exceptional monomial.

CONSEQUENCE for the squeeze datum: `schur_recursion_step_squeeze` concludes
`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn(G²) 0` with NO monomial weight. The actual loss carries
the `x_p²` factor, whose RLCT contribution is exactly what the `monomialThreshold` cover lane computes
(the banked (2,2,2) `x³`-Jacobian gives `3/2`, NOT `ambient/2`). Feeding `flatCore := dlnLoss ∘ blowup`
into the squeeze datum would DROP the monomial factor's RLCT — unsound.

So the squeeze datum applies to the RESIDUAL `Q` (where my proven `schur_node_loss_presentation`
discharges conjunct 1 — `‖Â·A2‖² = ∑E² + ‖bE+SΓ‖²`, green, clean-three), NOT to the pulled-back loss.
The residual route still owes (i) the `x_p²` exceptional-factor RLCT accounting (monomial lane, OR a
monomial-weight field on `IsSchurStraightenSqueeze`), and (ii) the coordinate-straightening making
`Erow` the regular coords (Jacobian rank-2 at the deepest point, above).

## Minimal honest message to surface

The banked blow-up atlas (`pivotBlowupOn`) does NOT determine the additive Schur layout `hnode`
demands; it produces a monomial exceptional factor times a residual, feeding the monomial/cover lane.
`hnode` is therefore NOT dischargeable from the atlas without a new pivot-stripping/residual-coordinate
theorem. The (b1) loss-form-in-coords and (b2) RLCT-transport tasks rest on a coordinate layout the
construction does not produce. Decision needed from the controller: (i) abandon the squeeze toolkit as
the per-node route and let the monomial/cover lane (already banked, already gives 3/2) carry the
recursion; or (ii) commission the residual coordinate-straightening theorem as a distinct piece of
work, after which the squeeze toolkit applies to the residual `Q` (not the full loss).

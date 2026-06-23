# PIN 1 analytic crux — general-L `dE(0) = id` (the regular-residual derivative at the deepest) (pp-hall, 2026-06-23, #91)

**Gates #82's `regAbsorb_rlct` (PIN 1, the regStraighten/regAbsorb).** Certifies, GENERAL-L and exact: the
derivative at the deepest of the regular residual `E : (gauge blocks) → ℝ^nReg` is the **IDENTITY**
(`dE(0) = id`, an invertible CLE, `|det dE(0)| = 1`), so #72's bounded-unit-Jacobian `|det dE| ∈ [a,b]` near
`0` holds by continuity from `=1` at `0`. **GENERAL-L structural argument + a 40-config adversarial sweep —
NOT an L=3 spot-check** (the #70 lesson: validate across the regime, with a structural reason, not instances).

## The setup (g125 block-normal)
At the deepest point, every layer is block-normal: `C_s = [[I_r + X_s, Y_s],[Z_s, T_s]]` (the output of
`deepestPoint_exists`/`block_elimination`, in Lean). `E` reads off the `(0,0),(0,1),(1,0)` blocks of
`P − D`, `P = ∏C_s`, `D = blockdiag[I_r, 0]` (the regular residual; the `(1,1)` block is the homogeneous
core). `nReg = r(H_0 + H_L − r)`, `H_s = r + M_s`.

## (i) `dE(0) = id` — the STRUCTURAL argument (general L, the #70-trap-proof reason)
`dP` at the deepest is `Σ_s (∏_{a<s} C_a^0) δC_s (∏_{b>s} C_b^0)`, where `C^0 = blockdiag[I_r, 0]` (the
deepest layer value) and `δC_s` the perturbation. The prefix/suffix products of `blockdiag[I_r,0]` are
**idempotent**: `blockdiag[I_r,0]^k = blockdiag[I_r,0]` for all `k` (the `(0,0)`-block-unit sub-fact, ∀L —
see (ii)). So the sandwich `blockdiag[I_r,0] · δC_s · blockdiag[I_r,0]` keeps ONLY the `(0,0)` corner of
`δC_s` for an INTERIOR `s`, and the endpoint blocks survive only at the chain ends:
- the `(0,1)` block survives ONLY when the suffix is empty (`s = L`, last layer) → picks `Y_L`;
- the `(1,0)` block survives ONLY when the prefix is empty (`s = 1`, first layer) → picks `Z_1`;
- the `(0,0)` block survives for ALL `s` → picks `Σ_s X_s`.

Hence `dE = (E_00, E_01, E_10) = (Σ_s X_s, Y_L, Z_1)` (= g125's `d(P−B) = [[Σ_s X_s, Y_L],[Z_1, 0]]`).
Choosing the PIVOT coords `(X_first for E_00, Y_last for E_01, Z_first for E_10)`, each generator has its
private pivot with coefficient EXACTLY `I_r` (the surviving `blockdiag[I_r,0]` sandwich is `I_r` on the
`(0,0)` corner). ⟹ **`dE(0)` on the pivot coords = the IDENTITY, `det = 1`, for ALL L** — no depth / width /
rank dependence. The idempotency of `blockdiag[I_r,0]` is the structural reason; it ties to a57's
determinantal-tangent (first + last factors generate the tangent: `Y_L` from the last, `Z_1` from the first,
`Σ X_s` the diagonal).

## (ii) the `(0,0)`-block-unit sub-fact ∀L (the load-bearing partial-product fact)
For any partial product `(C_a···C_b)`, the `(0,0)` block at the deepest is `I_r` (a UNIT, det 1): at the
deepest each `C_s = blockdiag[I_r, 0]`, and `blockdiag[I_r,0] · blockdiag[I_r,0] = blockdiag[I_r,0]`
(idempotent), so `(C_a···C_b)_00 = I_r·I_r···I_r = I_r` for any depth `b−a`. By continuity, `(C_a···C_b)_00`
is a UNIT on a neighbourhood of the deepest, ∀L. **This is the structural fact that makes the g125 triangular
solve's unit-denominators (`S_11`, `R_11`) units at every depth.**

## (iii) Validation — exact + adversarial sweep (the #70-trap-proof set)
- **Structural cases (exact, `dE(0)` pivot-Jacobian = `id`, det 1):** `r=1` M=(1,1,1)/(2,0,2)/(1,1,1,1)/
  (3,2,1) [non-monotone widths]; `r=2` M=(1,1,1)/(1,0,1,2)/(2,1,3); `r=3` M=(1,2,1,2,1) [depth-5]. All
  `dE(0) = id`, `det = 1` (`g211`).
- **Adversarial sweep (`g212`):** 40 randomized configs — asymmetric widths, `r ∈ {1,2,3}`, depth `∈ {1..5}`,
  including degenerate `M_s = 0` interiors. **dE(0) = id in ALL 40; ZERO fails.** No config with `dE(0) ≠ id`
  / non-invertible found. The regimes #70's 6 configs missed (r≥2, asymmetric/non-monotone) are covered.
- **Jacobian rank = nReg** (the generator count matches, `g210`): `#E_gens = nReg` and `rank dE = nReg` on all.

## What cobuild-sub34 builds (the Lean handoff for #82)
`HasFDerivAt E (id) 0` (or `dE(0)` an invertible CLE with `|det| = 1`) ⟹ `|det dE| ∈ [a,b]` near `0` (#72's
local bounded-unit-Jacobian, by continuity from `=1`). The Lean ingredients: the block-product derivative at
the deepest (the `Σ_s X_s, Y_L, Z_1` structure, via the idempotent `blockdiag[I_r,0]` prefix/suffix) + the
`(0,0)`-block-unit ∀L (idempotency + continuity). The pivot coords give `dE(0) = id` directly; the off-pivot
gauge coords are the regAbsorb straightening's domain (the IFT `Ψ` straightens `E` to its linear part, with
`dE(0) = id` the invertibility hypothesis the IFT needs). NO general constant-rank theorem — the identity
corner + idempotency supply the explicit unit-Jacobian (lighter, as g125 established).

## Most likely thing to break this
The idempotency `blockdiag[I_r,0]^k = blockdiag[I_r,0]` is exact (a projection), so the structural argument
has no hidden regime dependence — UNLESS the deepest layer value were NOT `blockdiag[I_r,0]` (e.g. a
non-block-normal deepest). But `block_elimination` / `deepestPoint_exists` PUTS the deepest in block-normal
form (identity corner) by construction — that is the hypothesis. So the load-bearing Lean fact is: the
deepest IS block-normal (given), and then `dE(0) = id` is the idempotent-sandwich computation. If a consumer
applied this at a NON-block-normal point it would fail — but the deepest is always block-normal (the frame
from #77 `deepestPoint_frame_exists`).

## Decorrelation
pp-hall exact algebra: `g210` (`#E_gens = nReg`, `rank dE = nReg` general L), `g211` (`dE(0) = id` exact on
the pivot coords across r=1/2/3 + asymmetric + depth-5), `g212` (the 40-config adversarial sweep, zero fails,
+ the idempotent-sandwich structural argument). Codex is DOWN env-wide (the AISI-wrapper git-ssh hang) — per
the dispatch + the #70 discipline, the exact-algebra + structural argument carries it (the idempotency is a
clean projection fact, regime-independent), NOT a numeric spot-check; a decorrelated subagent pass is the
substitute channel if wanted. Builds on g125 (the triangular-block-solve / `d(P−B) = [[Σ X_s, Y_L],[Z_1,0]]`),
a57 (the determinantal-tangent: first+last factors generate the tangent), #72 (the local bounded-unit-Jacobian
peel), #77 (`deepestPoint_frame_exists`, the block-normal frame). The #70 regime-lesson applied: structural
reason + regime-spanning sweep, not instances.

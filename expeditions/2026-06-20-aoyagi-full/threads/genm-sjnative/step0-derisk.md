# STEP-0 VERIFY-FIRST GATE — (3,3,3,4) t=(1,0,0) native R-BLOWUP sequential pullback

**Thread:** `genm-sjnative` (formaliser, R1-UPPER native decorated route → `sjJointResolution`).
**Base:** `expedition/aoyagi-full` @ `6592dad2`. **No Lean build in STEP 0** — sympy/scipy exact algebra
(`step0_*.py`, this dir) + a decorrelated `local-codex-consult` (xhigh, `codex/step0-{prompt,answer}.md`).

## VERDICT — GATE PASS

**The shared-support closes across ALL Case-1 equal-run partitions of `(3,3,3,4)`. The residual risk
(a Case-1/equal-run chart where the det-1 unit block-elimination mixes generators of DIFFERENT
accumulated `b_i`-support so the ledger is not closed — i.e. a forced simultaneous principalisation) does
NOT fire.** Proceed to the multi-tide build.

The decorrelated Codex red-team (below) materially sharpened the verdict: it flagged that a *naive*
constant-support argument is not faithful to Aoyagi's Case-1 step (which uses a monomial-coefficient
clear), and the resolution — the banked `corankStep`'s clear-first ordering reproduces Aoyagi's step
EXACTLY — is what makes the closure both true and Lean-faithful. Confidence GATE PASS ≈ 0.85.

## The object

`M = (3,3,3,4)`, `minAdm = 7`, threshold `½·minAdm = 7/2`. Equal-width run at nodes 0,1,2 (width 3);
node 3 width 4. Front layer `A₀` (3×3) resolved at its pivot; deeper `Z = A₁·A₂` (a GENUINE 3×4 product
— the corank-2 deeper-product case the probe `chart-lemma-probe.md` flagged but never ran end-to-end at
opaque width). Three binding admissible profiles (`Mval == minAdm`), each a way rank drops across the
width-3 run:

| branch `T` | layer charges | Case classification (corank vs running-min carrier dim) |
|---|---|---|
| `(1,0,0)` | `[4,3,0]=7` | L1 Case-1 (partial 2<3) · L2 Case-2 · L3 Case-2 |
| `(2,0,0)` | `[1,6,0]=7` | L1 Case-1 (partial 1<3) · L2 Case-2 |
| `(2,1,0)` | `[1,2,4]=7` | L1 Case-1 (partial 1<3) · L2 Case-1 (partial 1<2) · L3 Case-2 |

`(3,3,3,4)` is a genuine Case-1 witness — every binding branch has a partial drop at L1, and `(2,1,0)`
has TWO nested Case-1 steps (the richest witness for the residual risk).

## Evidence (all at the ACTUAL (3,3,3,4) widths)

**(B) Unit transforms det = 1, Z-independent, at each boundary** (`step0_pullback.py`, `step0_nested.py`).
- Rank-1 pivot (corank-2 block): `A₀ = L·diag(1,Δ₀)·R`, `det L = det R = 1`, `L,R` functions of `A₀`'s
  own entries `(a,b)` only → Z-independent. The corank-2→corank-1 reduction `L₂·Δ₀'·R₂ = diag(d₁₁, δ')`,
  `det L₂ = det R₂ = 1`, functions of `Δ₀'` only.
- Rank-2 pivot (corank-1 block, branch (2,1,0) L1): `A₀ = Lrow·diag(P,Δ₀)·Rcol`, `det = 1`, functions of
  `A₀`'s own entries only. **`det Q(0)·det P(0) = 1` (unit) at each boundary.**

**(D) Relative invariant / passive prefactor** (`step0_pullback.py`).
After the L1 corank peel of `(1,0,0)`: `rows(2,3) of A₀·Z − b·(pivot row)` factor EXACTLY as
`u₁·(residual)`, and the residual is `u₁`-FREE and `b`-FREE. So `u₁` is a passive overall prefactor on
the deeper term; `φ*(u₁²·G) = u₁²·φ*(G)` — the deeper resolution is independent (sequential, not
simultaneous). This is the banked `corankStep_prefactor` (`pref·frobSq((u•Δ)·Q) = (pref·u²)·residual`,
residual u-free and pref-free) at the actual widths.

**(C) Shared-support closure** (`step0_closure.py`, `step0_nested.py`, `step0_codex_probe.py`).
- **Block-split isolation:** the loss splits additively `‖pivot‖² + ‖corank‖²` (banked `loss_blockSplit`
  = the additive Schur split of `corankStep`). The pivot (u-free at the layer level) and the corank
  block are in separate summands; the recursion continues on the corank block, which is CONSTANT-support.
- **Within-block row-mix is faithful:** at a constant-support block, `g₁' = λg₀ + g₁ = u·(residual)` —
  the shared divisor factors cleanly out (banked `gen_rowMix_const`). The adversarial cross-support mix
  (`λ·pivot + u·row`, not divisible by `u`) is prevented by the block-split (pivot split off first).
- **Generator-support model, all 3 branches (incl. nested (2,1,0)):** every active block is
  constant-support; terminal supports are NESTED (`{} ⊂ {u₁} ⊂ {u₁,u₂}`) — no incompatible-support mix.
- **Toric shared-vs-fresh (exact LP):** the nested shared ledger gives the SMALLER (correct) RLCT at
  every depth (1-block ½ vs 1; 2-block ½ vs 1; 3-block ½ vs 3/2). A naive fresh-per-block ledger
  UNDERCOUNTS — the shared ledger is NECESSARY (reproduces DATA-1, extends to the (3,3,3,4)-shaped nest).

**(A) Charge accounting** (`step0_spine.py`, `step0_closure.py`). All 3 binding branches sum layer
charges to `7 = minAdm`; min over branches `= 7`; threshold `= 7/2`. The value is reached by the banked
exponent-shift accounting (`minAdmRec_eq_minAdm`, `sjSubordination`), not a hand-built toric.

## The decorrelated Codex red-team — the load-bearing refinement

Codex (xhigh, leaning withheld) returned **"GATE FAIL as stated", confidence PASS 0.35**, with a precise
objection: my constant-support block-split argument is NOT literally Aoyagi's Case-1 recursion. Aoyagi's
Case-1(2) row-clear DOES mix rows of different support, closing not by constant support but by the
`diag(b)` divisibility chain — the coefficient `b_i/b_{pivot}` is a regular monomial that RAISES the pivot
term to the target support. Codex's instance: `b_{J+1}=u·b`, `b_{J+2}=u·b·v`, clear
`g'_{J+2} = g_{J+2} − v·d''·g_{J+1}`. Its own point (4): the fail is wrong "if your gate includes a
generator-level row-mix lemma allowing monomial support quotients `b_i/b_pivot`; then the native ledger
can close."

**Resolution (`step0_codex_probe.py`, exact) — the objection is answered, the closure holds:**
- **(R1)** Codex's instance CLOSES: `g'_{J+2} = (u·b·v)·(res₂ − d''·res₁)`, support `{u,b,v}` (the
  target) PRESERVED. Closure holds because the supports are NESTED (`u·b ∣ u·b·v`), so the quotient
  `b_{J+2}/b_{J+1}=v` is a regular monomial.
- **(R2, decisive)** Aoyagi's "attach divisor → monomial-coefficient clear" and the banked `corankStep`'s
  "scalar Schur-clear → attach radial" orderings give the **EXACT SAME result**
  (`−b·u·v·(d''·res₁ − res₂)`, verified). The radial is factored FIRST (`frobSq_smul_mul`); the Schur
  elimination coefficients are `A⁻¹B` (regular pivot-block scalars) on the u-FREE residual; the next
  divisor enters at the NEXT step. So `gen_rowMix_const` (scalar coeff, constant support) is FAITHFUL —
  it reproduces Aoyagi's monomial-coefficient step, the monomial-coefficient mix being AVOIDED by the
  clear-first ordering, not needed.
- **(R3)** In `corankStep` the clear pivot and the rows it clears are ALL in the current active block
  (same accumulated prefix); a deeper divisor is attached to the corank residual only at the next step,
  AFTER this clear. The clear-first ordering is enforced by the recursion structure, not assumed —
  verified on the nested `(2,1,0)` trace.
- **(R4)** Two divisors never coexist within one clear: each `corankStep` introduces one radial and
  immediately Schur-splits (pivot Morse + corank recurses fresh). No single-step cross-divisor clear.

**Net:** Codex confirmed the closure holds (its own instance preserves support); its objection was to the
FAITHFULNESS of the constant-support argument, resolved by R2 (clear-first ordering ≡ Aoyagi's step). The
math does not wall; no simultaneous principalisation.

## The precise build obligation Codex surfaced (carry into the build)

The recursion must attach each step's radial only AFTER that step's SCALAR Schur elimination (the
"clear-first ordering"), so `gen_rowMix_const` applies at each step at constant support. This IS the
banked `corankStep`'s design (radial factored first via `frobSq_smul_mul`, then the scalar
`frobSq_schur_block_split`). The recursion assembly must PRESERVE this ordering across the nested Case-1
steps — this is the "relative chart lemma at opaque widths" the cert already named as the single hardest
bounded brick, now with the ordering requirement made explicit. It is NOT a monomial-coefficient row-mix
lemma (that is the equivalent-but-harder Aoyagi-order route, avoided).

## Banked substrate STEP 0 grounds the build on (verified faithful to the pointwise algebra)

`corankStep` / `corankStep_prefactor` / `corankStep_sequential` (`RouteMSJCorankStep`) — the relative
corank-step invariant at general widths, = STEP-0's (B)+(D). `SJLinGenState` / `radialStep` /
`loss_radialStep` / `rowMix` / `gen_rowMix_const` / `loss_blockSplit` (`RouteMSJLinGen`) — the
generator carrier, = STEP-0's (C). `SJSupport` / `sharedDivisorExp` / `sjLoss_factor` /
`sjLoss_terminal_lintegral_lt_top` (`RouteMSJLedger`) — the terminal endpoint. `matBox_corank_*_absZ_*`
(`RouteMSJCorankPure`) — the two block-Morse peel regimes. `minAdmRec_eq_minAdm` / `redChain` /
`Mval_decompose` (`RouteMLayerSplit`) — the charge/value spine.

## Files

`step0_spine.py` (charges/branches/equal-runs), `step0_pullback.py` (unit transforms + prefactor
independence), `step0_closure.py` (Case classification, block-split, row-mix, toric, charges),
`step0_nested.py` (rank-2 pivot + generator-support model all branches),
`step0_codex_probe.py` (the Codex-objection resolution R1–R4). Codex artefact:
`codex/step0-{prompt,answer}.md`.

# Shell-j ∧ IsUnit-P soundness — VERDICT: **CONFIRMED** (buildable). The route needs `c' < ½·minAdm M`, which the object clears for every `1≤j<r`.

**Seat:** pen-and-paper (OBSTRUCTION, decorrelated), aoyagi-full, `genm-shelljhunt`. **Date:** 2026-07-14.
**NO Lean, NO git, NO build.** Exact algebra (codim stratification + exact-ℚ smooth-point Jacobian, sympy)
+ decorrelated `local-codex-consult` (xhigh, gpt-5.6-sol, run with NO repo access — clean decorrelation;
my conclusion WITHHELD): `codex/shellj-{prompt,answer}.md`. Scripts: `shellj_codim.py`, `shellj_sweep.py`,
`circularity_check.py`. Object read from `genm-sj5-wallfin` (`RouteMSJHeadSplitFin.lean` `Hfull_eq_Hblock`,
`frobSqBlockFull_lt_top`), the driver `RouteMSJDeeperFlagCore.lean` (`deeperFlag_shell_le`), and
`RouteMSJDecorated.lean` / `RouteMSJShellCharge.lean` (`carrierThreshold`, `flagCharge_ge`).

---

## ★ VERDICT — **CONFIRMED.** No shell-j ∧ IsUnit-P divergence at any `c'` the route uses.

The object `I_j(c') = ∫_{W∈shell-j} ∫_{B∈box, IsUnit P} ‖B·hsQ‖_F^{−2c'}` (L=0: `W=hsQ=(z₀;A_cor)`,
`B` the `M₀×M₁` front block) is **finite for all `c' < carrierThreshold M = ½·minAdm M`**, for EVERY
`1 ≤ j < r`. That is the whole-chain carrier the mountain actually runs at (Lean
`carrierThreshold M := minAdm M / 2`, `RouteMSJDecorated.lean:64`), and it is the range the shell-cover
assembly (`∫_box ≤ Σ_j ∫_{S_j}`) invokes each shell piece at. So the re-scoped head-split (a)/hstrict
route is **buildable — not a terminal wall.**

The proof is one line: `shell-j ∧ IsUnit-P` is a **subset** of the full off-shell box (same nonneg
integrand), whose RLCT is `½·minAdm M` (thresholdhunt, re-confirmed here by exact-ℚ Jacobian). A domain
restriction can only RAISE the RLCT, so `RLCT(I_j) ≥ ½·minAdm M`. Route needs `c' < ½·minAdm M`. Done.

**Decorrelated Codex CONCURS on every load-bearing point** (independent derivation): the exact `λ_j`,
`IsUnit-P` value-vacuity, the `(6,6,6)@j=2` numbers, and the Q4 adjudication — *"Divergence at some
`c' < ½·minAdm(M)`: NO … If the surrounding proof invokes the domination only under `c' < T1`, there is
no RLCT wall in its used range."*

---

## 1. The target threshold — `½·minAdm M`, NOT the recon's `(minAdm(redChain u M)+ab)/2`

This is the crux, and it flips the recon's framing. There are **two different thresholds**, both named
"carrierThreshold" in different documents:

| name | value | what it is |
|---|---|---|
| **T1** = Lean `carrierThreshold M` | `½·minAdm M` | the **whole-chain carrier**; the `c'` the mountain runs at |
| **T2** = recon/couplingfin "carrierThreshold(M)" | `(minAdm(redChain u M)+ab)/2` = `(u·M₂+ab)/2` (L=0) | the per-cut **comparator** finiteness range |

- Lean: `carrierThreshold M := (minAdm M : ℝ)/2` (`RouteMSJDecorated.lean:64`).
- `flagShift_lt_carrierThreshold` (`RouteMSJShellCharge.lean`): for `c' < carrierThreshold M`, the shifted
  comparator exponent `c'−½·peelCharge` sits below `carrierThreshold(redChain u M) = ½·minAdm(redChain u M)`.
  So the mountain's `c'`-ceiling is **T1**; the comparator staying finite (needs `c' < T2`) is automatic
  because `flagCharge_ge` gives `minAdm M ≤ ab + minAdm(redChain u M)`, i.e. **`T1 ≤ T2`**.
- `peelCharge M u := (M₀−u)(M₁−u) = ab` (`RouteMSJDecoratedCharge.lean:45`).

So the shell-j LHS must be finite only for `c' < T1`. The recon (§3) and couplingfin stated the target as
T2 — the higher, per-cut comparator range. The team-lead brief's parenthetical "`= minAdm(M)/2`" (i.e. T1)
was the correct one.

## 2. The exact shell-j RLCT (subset-cap of the strata)

`{B·W=0}` stratifies by `s = rank B`; `codim Z_s = (M₀−s)(M₁−s) + s·M₂` (exact-ℚ Jacobian rank verified
for all `s`, chains `(3,3,3),(4,4,4),(6,6,6)` — `shellj_codim.py`: every stratum matches the formula).
`minAdm M = min_s codim Z_s` at the argmin `t★`.

**shell-j caps the reachable strata.** On `{B·W=0}`, `rank W ≤ M₁ − s`; on shell-j, `rank W ≥ min(M₁,M₂)−j`
(exactly `j` singular values `< ε`, so `min(M₁,M₂)−j` stay `≥ ε > 0` in the whole closure). Reachable ranks:
`s ≤ R_j := min(M₀, M₁ − min(M₁,M₂) + j)`. Hence (Codex-confirmed, independent):

    RLCT(I_j) = λ_j = ½ · min_{0 ≤ s ≤ R_j} [ (M₀−s)(M₁−s) + s·M₂ ]  ≥  ½·minAdm M.

The last `≥` is immediate: a min over a **subset** of strata is `≥` the global min. So `λ_j ≥ T1` **always**
(sweep `shellj_sweep.py` / `circularity_check.py`: `λ_j ≥ T1` holds with non-negative slack in every case).

**`IsUnit P` is value-vacuous.** `{IsUnit(toBlocks₁₁ B)} = {det(B[1:u,1:u]) ≠ 0}` is co-null in `B`
(complement is `{det=0}`, an algebraic hypersurface). `∫_{det P≠0} f = ∫_{box} f` as extended nonneg
integrals (they differ by a null set — even when both are `+∞`). So it cannot turn `⊤` into `<⊤`; it is
load-bearing for the peel change-of-variables (`Hfull_eq_Hblock`: peeled `= ∫ frobSq(B·hsQ)` over
`{IsUnit}`), **not** for finiteness. "shell-j ∧ IsUnit-P finite" ⟺ "shell-j finite". (Codex: identical
conclusion, incl. the closure remark — rank-`B<u` strata remain in `closure{det P≠0}`.)

## 3. The witness table — CONFIRMED against T1, but the recon's T2 target degrades for `j > r/2`

`t★ = argmin`, `r = min(M₀−t★, M₁−t★)`, cut `u = t★+j`. `λ_j` exact; both thresholds shown.

| M | j | u | a,b | `λ_j = RLCT(I_j)` | **T1 = ½·minAdm M (route need)** | T2 = (uM₂+ab)/2 | `λ_j ≥ T1`? | `λ_j ≥ T2`? |
|---|---|---|---|---|---|---|---|---|
| (3,3,3) | 1 | 2 | 1,1 | 7/2 | 7/2 | 7/2 | ✓ (=) | ✓ (=) |
| (4,4,4) | 1 | 3 | 1,1 | 13/2 | 6 | 13/2 | ✓ | ✓ (=) |
| (6,6,6) | 1 | 4 | 2,2 | 31/2 | 27/2 | 14 | ✓ (+2) | ✓ |
| **(6,6,6)** | **2** | **5** | **1,1** | **14** | **27/2** | **31/2** | **✓ (+½)** | **✗ (−3/2)** |
| (8,8,8) | 1 | 5 | 3,3 | 57/2 | 24 | 49/2 | ✓ | ✓ |
| (8,8,8) | 2 | 6 | 2,2 | 26 | 24 | 26 | ✓ | ✓ (=) |
| **(8,8,8)** | **3** | **7** | **1,1** | **49/2** | **24** | **57/2** | **✓ (+½)** | **✗ (−4)** |
| (5,5,5) | 2 | 4 | 1,1 | 19/2 | 19/2 | 21/2 | ✓ (=) | ✗ (−1) |

**`λ_j ≥ T1` is a theorem (all `j`)** — the `>=need?` column never fails (sweep). **`λ_j < T2` exactly when
`j > r/2`** (square case: `λ_j − T2 = −½·t★·(2j−r)`). The `(6,6,6)@u=5,j=2` and `(8,8,8)@u=7,j=3` rows are
the exact configurations where the object diverges **below T2** — the "candidate wall" the recon feared.
It is REAL against T2, and MOOT for the route because the route never runs `c'` there (`T1 ≤ T2`).

## 4. The domination `deeperFlag_shell_le`, and a latent STATEMENT bug the build must fix

`deeperFlag_shell_le` (`RouteMSJDeeperFlagCore.lean:741`) claims
`shellSpineIntegrand …(c') ≤ C · comparator.integral(c' − ab/2)`, `C < ⊤`, with `comparator.integral(e) < ⊤`
iff `e < ½·minAdm(redChain u M)` (iff `c' < T2`).

- For a fixed `c'`: LHS `= I_j(c')` finite iff `c' < λ_j`; comparator finite iff `c' < T2`. The domination
  is FALSE precisely on `[λ_j, T2)` (LHS `= ⊤`, RHS finite) — nonempty iff `j > r/2`.
  Concretely `(6,6,6)@j=2: [14, 31/2)`; `(8,8,8)@j=3: [49/2, 57/2)` (Codex-confirmed).
- The stated theorem carries **only a lower `c'` bound** `hc' : (M₀−u)(M₁−u)/2 < c'` — **no upper bound.**
  So AS STATED it is **false for `j > r/2` at `c' ∈ [λ_j, T2)`**.
- **Fix (actionable, not a wall):** add the hypothesis `c' < carrierThreshold M` (`= ½·minAdm M = T1`). The
  consumer (`RouteMSJShellCover` → mountain) supplies exactly this. On `c' < T1 (≤ λ_j)` the LHS is finite,
  the comparator is finite (`T1 ≤ T2`), so a finite `C` exists and the domination holds. (Codex, verbatim:
  *"If the surrounding proof invokes the domination only under `c' < T1`, there is no RLCT wall in its used
  range. If it asserts the domination throughout `c' < T2`, that stronger assertion is false."*)

Note (Codex, and a build caveat): `C = I_j/comparator` finite "does not validate any separately prescribed
or uniform constant" — a UNIFORM-in-`c'` (endpoint) constant is a separate matter, as `c' → T1` the constant
may blow up (couplingfin's per-exponent caveat). The mountain only needs per-exponent `C(c') < ⊤` strictly
below `T1`, which holds.

## 5. Build implications (for the strong-minor-chart tide, Risk B)

- Target `c' < T1 = ½·minAdm M` ONLY. **Do NOT** re-prove up to T2 — that is the exact over-claim that made
  `frobSqBlockFull_lt_top` false (thresholdhunt). The strong-minor build must carry `c' < carrierThreshold M`.
- The object has genuine slack for `j ≤ r/2` (e.g. `(6,6,6)@j=1`: `λ=31/2` vs need `27/2`) and is marginal
  (`λ_j = T1`, per-exponent-strict) where the shell reaches the argmin stratum. Both are fine.
- Alternative to the strong-minor mechanism: the finiteness is `I_j ≤ I_full` (subset), so any route that
  banks the full-chain `RLCT = ½·minAdm M` gives it directly. The strong/weak split is needed for the
  reduced-comparator **form** (the L≥1 recursion), not for finiteness. The coupling worry (strong↔weak
  through `B`) is a build-difficulty question, not a soundness one — the statement is true regardless.

## Close

- **Firmest result.** `I_j` (shell-j ∧ IsUnit-P) is finite for all `c' < carrierThreshold M = ½·minAdm M`,
  every `1 ≤ j < r`. Exact: `RLCT(I_j) = ½·min_{s≤R_j} codim Z_s ≥ ½·minAdm M`, and `= ½·minAdm M` is the
  route's ceiling. Triple-confirmed: exact-ℚ Jacobian codim; the subset-monotonicity one-liner; decorrelated
  Codex (independent, no repo access). **CONFIRMED — buildable.**
- **Most likely to break it.** (i) If a re-scoped statement mistakenly targets `c' < T2` (the recon's stated
  threshold) rather than `c' < T1`, it is FALSE for `j > r/2` — the concrete `(6,6,6)@u=5,j=2` /
  `(8,8,8)@u=7,j=3` divergences. Guard: the build MUST carry `c' < carrierThreshold M`. (ii) L≥1 scope: the
  witnesses are L=0 (where thresholdhunt's `½·minAdm M` full-box RLCT is exact); for L≥1 the subset argument
  rests on the full-chain `RLCT = ½·minAdm M` (the paper's codimension result), so the L≥1 shell pieces are
  sound on the same ground once that is banked — worth a confirming pass but not an open wall.
- **Next.** For the strong-minor-chart tide: (a) state Brick D / `deeperFlag_shell_le` with the upper bound
  `c' < carrierThreshold M` threaded from the shell cover; (b) prove `I_j` finite up to T1 only (slack for
  `j ≤ r/2`, marginal-strict otherwise); (c) do NOT reach for T2.

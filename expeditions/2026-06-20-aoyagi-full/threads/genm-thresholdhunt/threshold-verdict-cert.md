# Off-shell full-block threshold — VERDICT: **DEGRADES.** `frobSqBlockFull_lt_top` is FALSE as stated.

**Seat:** pen-and-paper (OBSTRUCTION/witness, decorrelated), aoyagi-full, `genm-thresholdhunt`.
**Date:** 2026-07-14. **NO Lean, NO git, NO build.** Exact algebra (minAdm recursion, codim stratification,
an exact-rational smooth-point Jacobian over ℚ), + decorrelated `local-codex-consult` (xhigh, my conclusion
WITHHELD): `codex/threshold-{prompt,answer}.md`. Object read off `origin/genm-sj5-wallfin @0c392c3b`
(`RouteMSJHeadSplitFin.lean`, `RouteMSJHeadSplitDom.lean`).

---

## ★ VERDICT — **DEGRADES.** The off-shell full-block RLCT is `minAdm(M₀,M₁,M₂)/2`, NOT `(minAdm(redChain u M)+ab)/2`.

The wall `frobSqBlockFull_lt_top` claims `∫_z ∫_{A_cor∈matBox} ∫_{B∈genBox} frobSq(B·hsQ)^{−c'} < ⊤`
for `2c' < minAdm(redChain u M) + ab` (`a=M₀−u, b=M₁−u`), given the deep floor `hfloor` (FULL matBox,
off-shell). **This is FALSE for min(a,b)≥2 at any non-argmin cut.** The true convergence threshold is
`λ_full = minAdm(M₀,M₁,M₂)/2` (Codex-confirmed, independent method), which is STRICTLY BELOW the wall's
claimed `(minAdm(redChain u M)+ab)/2` whenever `u` is not a minimizing cut of `minAdm(M₀,M₁,M₂)`.

**Certified witness (min(a,b)≥2):** `M=(6,6,6)`, `u=4` (`a=b=2`). All wall hypotheses satisfiable; the LHS
diverges for `c'∈[13.5, 14.0)` while the wall claims finite up to `14.0`.

---

## 1. The object reduces to a matrix-product RLCT (L=0, intended wiring)

`hsQ = fromRows(Q_p, Q_b)`, with **`Q_p = prod(redChain u M) z`** (the genuine reduced-chain product —
does NOT use the abstract `Zf`) and `Q_b = A_cor·Zf z`. For L=0 (3-width `M=(M₀,M₁,M₂)`), the intended
`Zf = deeperFlagZdeep = I_{M₂}` (empty deep product), so

    hsQ = (z₀ ; A_cor) =: W   (M₁×M₂),   B·hsQ = B·W.

`z₀` (=`Q_p`, `u×M₂`), `A_cor` (`b×M₂`), `B` (`M₀×M₁`) all range over FULL entrywise boxes
(`paramsBoxM`/`matBox`/`genBox` are `[−1,1]` per entry). So `W=(z₀;A_cor)` fills the full `M₁×M₂` box and

    LHS  =  ∫_{W∈box, B∈box} ‖B·W‖_F^{−2c'}   — a pure two-matrix-product RLCT, chain (M₀,M₁,M₂).

**Key structural fact — the LHS is `u`-INDEPENDENT.** `u` only relabels the row-split of `W` into
pivot/corank; it does not change the integration region or the integrand. So `pivotDomLHS_full M u c' (I)`
has the SAME value for every `u`, namely the threshold `minAdm(M₀,M₁,M₂)/2`. The wall's *claimed* threshold
`(minAdm(redChain u M)+ab)/2 = (u·M₂ + ab)/2` (L=0 leaf) is `u`-DEPENDENT — so it cannot equal the true
`u`-independent value at more than one family of `u`. [Codex, decorrelated: "Because `W=[z0;Acor]` fills all
`n` rows, `u` does not affect the true threshold." — verbatim independent agreement.]

## 2. The exact threshold `λ_full = minAdm(M₀,M₁,M₂)/2`

`codim{BW=0}` (B `M₀×M₁`, W `M₁×M₂`), stratifying by `r=rank B`:
`codim Z_r = (M₀−r)(M₁−r) + r·M₂`, so `codim{BW=0} = min_{r} [(M₀−r)(M₁−r)+r·M₂] = minAdm(M₀,M₁,M₂)`
(this IS the minAdm recursion for the 3-chain — `minAdm(t,M₂)=t·M₂` leaf). By the universal Watanabe bound
`rlct ≤ codim/2`, the integral DIVERGES for `c' ≥ minAdm(M₀,M₁,M₂)/2`.

**Exact divergence certificate (elementary, no cited black box).** At the top stratum, `{BW=0}` is SMOOTH of
codimension `C=minAdm(M₀,M₁,M₂)`: an explicit rational point `B₀` (rank = argmin cut), `W₀` (columns in
`ker B₀`) has differential `dΦ(δB,δW)=δB·W₀+B₀·δW` of rank exactly `C` (verified over ℚ, sympy). Hence in a
local chart `‖BW‖² ≍ Σ_{i=1}^{C} y_i²`, and `∫_{|y|<δ} ‖y‖^{−2c'} dy = vol(S^{C−1})∫₀^δ ρ^{C−1−2c'}dρ = ∞`
for `2c' ≥ C`. Verified `C = minAdm`: (3,3,3)→7, (4,4,4)→12, (6,6,6)→27 (Jac-rank matches exactly).

**Codex decorrelated derivation (different method).** Gaussian localization
`J(t)=∫ e^{−‖B‖²−‖W‖²−t‖BW‖²}` → integrate `W` → `∫ e^{−‖B‖²}det(I+tBᵀB)^{−p/2}` → Wishart ordered-eigenvalue
blow-up gives, for `k` singular values of size `t^{−1}` (`r=q−k`), the candidate exponent `2λ_k=(M₀−r)(M₁−r)+rM₂`.
No stratum undershoots `C/2`; a smooth point of a maximal component realizes it. `⟹ λ_full = ½·min_r[(M₀−r)(M₁−r)+rM₂]`.

## 3. The witness table (all wall hypotheses satisfiable, cut reachable in the route)

The wall is invoked via `headSplit_domination_impl` at `u = t+j` for every valid `(t,j)`
(`1≤t≤min(M₀,M₁)`, `0≤j<min(M₀−t,M₁−t)`, `m=min(M₁,M_last)−j`, `a+b≤m≤M₂`). So non-argmin cuts ARE reached.

| M | u | a,b | reach `(t,j,m)` | hpiv | wall = (ab+minAdm(red))/2 | **λ_full = minAdm(M₀,M₁,M₂)/2** | argmin cut | verdict |
|---|---|---|---|---|---|---|---|---|
| (3,3,3) | 2 | 1,1 | (2,0,3) | 6≤6 ✓ | 3.5 | 3.5 | t*∈{1,2}∋2 | **SOUND (tight)** |
| (4,4,4) | 3 | 1,1 | (3,0,4) | 12≤12 ✓ | 6.5 | 6.0 | t*=2 ∌3 | **UNSOUND** (diverges c'=6.25) |
| (6,6,6) | 4 | 2,2 | (2,2,4) | 24≤24 ✓ | **14.0** | **13.5** | t*=3 ∌4 | **UNSOUND** (diverges c'=13.75) |

Codex concurs on all three: A EQUAL/sound-sharp; B ABOVE (c=6.25<6.5 diverges); C ABOVE (c=13.75<14 diverges).

**Headline min(a,b)≥2 witness `(6,6,6)@u=4`, full hypothesis check for `frobSqBlockFull_lt_top`:**
`hu`(1≤4)✓ `hnd`(6≥1)✓ `hpiv`(minAdm(4,6)=24 ≤ 4·min(6,6)=24)✓ `hcvg`(a+b=4≤m=4)✓ `hmM`(m=4≤M₂=6)✓
`hε'`(1>0)✓ `Zf=I₆`, `U_sf`=first 4 cols of I₆: `hUs`✓ `hrank`(rank I₆=6≥4)✓ `hfloor`(I₆−U_sfU_sfᵀ = proj onto
complementary 2-dim, PSD)✓ `hcrit`(2·13.75=27.5 < 24+4=28)✓. LHS = ∫‖BW‖^{−27.5}, `{BW=0}` smooth codim 27
⟹ DIVERGES. Wall claims `<⊤`. **Contradiction ⟹ the theorem is unprovable.**

## 4. Mechanism — the deep floor does NOT control the front-factor rank drop (couplingfin vindicated)

The divergence lives at the **off-shell, low-rank-`W`** locus. For `{BW=0}` with `B` rank `r`, `W` must have
`col(W)⊆ker B` (dim `M₁−r`), i.e. **`W=hsQ` is rank-deficient** there. The wall goes OFF-shell deliberately
and relies on `hfloor` (a Loewner bound on the DEEP factor `Zf`) instead of the shell. But `hsQ = W·Zf`, and
its rank drop comes from the **front factor `W=(pivot z₀ ; corank A_cor)`**, which `hfloor` (constraining
`Zf` only) leaves completely free. So the floor cannot exclude the divergence.

The **shell** `σ_min(hsQ)≥ε` WOULD exclude it: on-shell `‖B·hsQ‖² ≥ ε²‖B‖_F²`, so the only singularity is
`B=0` and `∫_B‖B‖^{−2c'}` over `B∈ℝ^{M₀M₁}` converges up to `c' < M₀M₁/2` (= 18 for (6,6,6)) — safely above
the wall. **The shell is load-bearing for the FULL block, not just the pivot** — the exact sharpening
`genm-couplingfin` reported ("off-shell degrades; the shell is load-bearing"), now shown to break the
FULL-block object at min(a,b)≥2 non-argmin cuts and quantified exactly.

## 5. Sharp characterization (refutation dialectic) + the fix

**Wall (off-shell full box) is SOUND ⟺ `u` is an argmin cut of `minAdm(M₀,M₁,M₂)`** (L=0; general L: of
`minAdm(M)`). The dividing line is the CUT vs the argmin — **not** `min(a,b)`. The brief's "a=b=1 is the
theorem" holds only because the confirmed anchor `(3,3,3)@u=2` happens to sit at an argmin cut; the wall is
ALSO false at a=b=1 non-argmin cuts, e.g. `(4,4,4)@u=3`.

**The brief's proposed test case `(4,4,4)@u=1` is VACUOUS:** `a=b=3 ⟹ a+b=6`, but `hcvg`+`hmM` need
`6≤m≤M₂=4` — no valid `m`. `hfloor`/`hUs`/`hrank` (an orthonormal `m≥6`-frame inside a `4×4` `Zf`) cannot be
satisfied. It does not exercise the wall. (Use `(6,6,6)@u=4` for a genuine min(a,b)≥2 test.)

**The correct threshold** for the off-shell full box (L=0) is `minAdm(M₀,M₁,M₂)/2` — the min over ALL
sub-cuts, `u`-independent — not `(minAdm(redChain u M)+ab)/2`.

**Fix directions (either restores soundness):**
- (i) **Restore the shell** `σ_min(hsQ)≥ε` (couplingfin's load-bearing restriction). The deep floor `hfloor`
  is NOT a substitute — it controls `Zf`, not the front factor `W`. This is the design's real gap.
- (ii) If off-shell is required: tighten `hcrit` to `2c' < minAdm(M)` [full chain], equivalently restrict the
  wall to the argmin cut. Then the claim matches the true `u`-independent threshold and is provable.
- The likely-intended object (`pivotDomLHS_full` via `Hfull`, `IsUnit(toBlocks₁₁)`-restricted) may reach the
  higher threshold by excluding the low-rank-`B` stratum — but the UNSOUND step is the enlargement in
  `pivotDomLHS_full_lt_top` (`lintegral_mono_set`, dropping `IsUnit`): the docstring's "the enlargement is a
  ≤, and by Claim F the enlarged integral is still finite" is the false step. Whether `IsUnit`-restricted-but-
  off-shell reaches 14 needs its own adjudication (couplingfin's off-shell pivot degradation suggests caution).

## Close

- **Firmest result.** `frobSqBlockFull_lt_top` is FALSE as stated. Off-shell full-block RLCT
  `= minAdm(M₀,M₁,M₂)/2` (triple-confirmed: codim stratification; exact-ℚ smooth-point Jacobian; decorrelated
  Codex Wishart blow-up). Witness `(6,6,6)@u=4`: diverges on `[13.5, 14.0)`; all wall hyps satisfiable; cut
  reachable. The wall's `(minAdm(redChain u M)+ab)/2` overcharges by committing to cut `u` instead of the
  free integral's cheaper argmin cut.
- **Most likely to break the finding.** That the route's DRIVER only ever instantiates the wall at an argmin
  cut (then the over-general statement is false but the used instances are true — fix = restrict `u`). Needs a
  driver trace. Either way the theorem AS STATED is unprovable.
- **Next.** (a) Trace which cuts `u=t+j` the flagpeel driver actually needs (argmin-only vs all). (b) Adjudicate
  whether `IsUnit`-restricted off-shell reaches the wall threshold, or whether the shell must be restored.

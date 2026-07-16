# q2gate — does the coupled ∀-M capstone INHERIT the Q2 obstruction?

**Seat:** pen-and-paper, OBSTRUCTION direction (aoyagi-full, `genm-q2gate`). **Date:** 2026-07-16.
**NO Lean edits, NO build.** Exact-ℕ (`minAdm` recursion, certified equal to Lean's `minAdmRec`) +
structural RLCT reasoning; Monte-Carlo **only** to discriminate density shape (nothing load-bearing rests
on a float). Decorrelated `local-codex-consult` (gpt-5.x xhigh, my conclusion WITHHELD):
`codex/crux-{prompt,answer}.md`, `codex/crux-run.log`. Decorrelated from couplerad/corankrec/satred.

The single truth-value: does `routeMBoxThresholdFinite_coupled` (RouteMSJArity4Assembly.lean:324),
via the plain-`SJStepHyp` wrapper `routeMBoxThresholdFinite_of_step` fed by `sjStepHyp_of_coupled`,
invoke the **plain unweighted arity-IH** `∀ M', RouteMBoxThresholdFinite M'` on a **Q2-hard** reduced
chain (reduced integrand carrying the unabsorbed truncated-Gram / `H⁻⁴` weight at the zero-slack binding
cut)?

---

## ★ VERDICT (SHARP after the u≥3 scan) — Q2-INHERITING for the full ∀-M mint (decorated canonical); Q2-CLEAN only for `u = min(M₀,M₁) ≤ 2`.

The truth-value splits **exactly by the saturated-shell waist rank `u = min(M₀,M₁)`**:

- **`u ≤ 2`: Q2-CLEAN.** The saturated-shell plain-IH invocation reaches the full threshold
  `½·minAdm(M)` via a **dyadic-shell (σ_max) homogeneity + Hölder** argument (decorrelated Codex,
  independent of satred) using ONLY the plain unweighted arity-IH + a standalone waist-density atom —
  NOT a weighted/decorated IH. The obstruction I first set out to prove (the pointwise-fold undershoot,
  real for `A>2Δ`) is DEFEATED here. Cleanest witness **(2,2,2,2)** (nondeg cut `t=1`, `a=b=0`): the
  2×2-product density is **logarithmic** along the generic `{det=0}` hypersurface (power `r⁻¹` confined
  to the origin, absorbed by the shell volume `r⁴` → `r^{minAdm−2c'}`, tight to `c'<3/2`). Numerically
  confirmed (Tests 1&3) + structural (`RMBTF(M)|_{P inv}`, Aoyagi RLCT `3/2`).

- **`u ≥ 3`, SQUARE waist (`M₀=M₁≥3`, `a=b=0`): Q2-INHERITING (proven).** Here the front is `X=P`
  (square `u×u`, NON-injective product `z̃₀=P·z₀`), the worst density. The plain-IH shell/Hölder/pointwise
  routes ALL **undershoot**; the escape requires a **weighted/coupled IH** (= the decorated FaithfulSJAt
  mechanism) or `σ_min(P) ≥ δ` pinned charts (unavailable at the full-`{IsUnit P}` waist) — both strictly
  stronger than the plain unweighted IH. **Confirmed by THREE decorrelated lines:** (i) a second
  decorrelated Codex (u≥3 consult, `codex/u3-answer.md`): "the shell route using only the unweighted `B_n`
  reaches sharply only for `n≤2`"; for `n≥3` pure Hölder reaches `(3/8)·minAdm(n,n,n)` vs the needed
  `½·minAdm(n,n,n,n)` — `n=3`: `21/8 = 2.625 < 3`, gap `3/8`; `n=4`: `9/2 < 11/2`, gap `1`. (ii) satred's
  density atom: the wide-square density has a genuine power `γ = ⌊k²/4⌋` on the corank-`k` stratum, so
  `ρ_ang ∈ L^p` iff `p < 4` (binding: corank-2 stratum, codim 4, `γ=1`), NOT all `p`. (iii) My
  3×3-product Monte-Carlo (`u3_strata.py`): rank-2 stratum (codim 1) LOG (`γ=0`); rank-1 stratum (codim 4)
  measure `~ε³` (not `ε⁴`) ⟹ density power `γ=1` — exactly the `p<4` obstruction. The square `u≥3` waists
  are in-scope with nondeg cuts (**(3,3,3,3)** t=2, **(4,4,4,4)** t∈{2,3}, **(3,3,3,3,3)** t=2), so the
  coupled route as wired (plain `SJStepHyp` → `routeMBoxThresholdFinite_of_step`) **cannot** discharge
  `hcoupled` for them.

- **`u ≥ 3`, NON-square waist: not fully adjudicated, but the closability arithmetic points the SAME way
  (likely also inheriting).** The shell brick closes a cell for-sure iff `min_k codim_k/γ_k ≥ R/(R−1)`
  where `R = minAdm(redChain u M)/minAdm(M)` (`γ_k` = the TRUE per-corank density order; `codim_k` the
  stratum codim). This is the exact criterion; satred owns the true `γ_k`. **(a=0, b>0 wide-non-square)**
  e.g. `(3,4,4,4)`: `R=10/9`, so the **target `R/(R−1)=10`** (even HIGHER than the square's `7`, because a
  larger `minAdm` gives less relative headroom); the strata have small codim (corank-1 codim 2, corank-2
  codim 6), so closing needs nearly ALL strata LOG (`γ_k≈0`) — implausible for a genuine rank-drop (the
  deepest stratum carries `γ≥1`). The `B₁₂`-columns *do* soften `γ` (satred: true order milder,
  monotone-decreasing in `b`, so the square is the worst *density*), but they do not lower the *target*.
  So wide-non-square `u≥3` **very likely also inherits** — pending satred's true `γ_k` for the definitive
  call (targets: `(3,4,4,4)→10`, `(3,5,5,5)→13`, `(4,5,5,5)→16`, `(3,4,5,5)→13/2`). **(b=0, a>0 tall)**
  e.g. `(5,3,3,3)`: injective `[P;C]` ⟹ no pushforward-density power ⟹ satred's **qbox**
  `det(PᵀP+CᵀC)^{−M₂/2}` (conv ⟺ `M₂≤a`, recurses if `M₂>a`); the recursion INHERITS its reduced chain's
  status (satred exact-ℕ: 2850 clean / 276 decorated / 654 open; decorated ones reduce to a square, e.g.
  `(5,3,3,3)→(3,3,3)`). satred owns the qbox leaf.

**Net for the controller (endgame call).** The `∀-M` mint contains the **square** chains `(n,n,…,n)`,
`n≥3` — in-scope, nondeg cut, and PROVEN Q2-inheriting — so **the coupled route CANNOT close the full
mint via the plain `SJStepHyp`; the DECORATED route (weighted FaithfulSJAt IH) is canonical for the full
`∀-M` closure.** This call rests on the square witnesses alone and does not need the non-square `u≥3`
sub-cases resolved. The coupled route is a genuine *partial* result: the **interior** cells are fully
native (`RectSchurCore`, no reduced-chain descent) and always close; the `u ≤ 2` sub-family closes via
the shell+Hölder saturated brick (a=0) / qbox leaf (b=0), and the edge pivot-core descent is `u≤2`-clean.
Three sites route through `RMBTF(redChain u M)` via the `X·Y` descent — the saturated shell `hbdryShell`,
the EDGE pivot-core (edgefub's factor 2; Q2-clean only in *statement form*, §1), and `hdegen` — so all
three inherit the square-`u≥3` wall through `redChain` (satred's b=0 exact-ℕ scan: 2850 clean / 276
decorated-inheritor / 654 open; the decorated inheritors reduce to a square, e.g. `(5,3,3,3) → (3,3,3)`).
This is the same wall as the bare `sjJointResolution` L≥3 sorry — the coupled *split* pushes it from the
general cut down to the square `u≥3` waist/reduced-chain, but does not remove it. The saturated brick must
NEVER be a pointwise-fold brick (provably undershoots on `A>2Δ` at every `u`); at `u≤2` it is the
shell+Hölder form (a=0) / qbox leaf (b=0) of §8.

---

## 1. Where the plain arity-IH is actually invoked (Lean trace)

`routeMBoxThresholdFinite_coupled hcoupled hdegen M`
`= routeMBoxThresholdFinite_of_step (sjStepHyp_of_coupled hcoupled hdegen) sjBase1_freeMatrix M`.
The wrapper (`routeMBoxThresholdFinite_of_step`, RouteMSJResolution) does **strong induction on chain
arity**; at arity `≥ 3` it hands the step the IH `hIH : ∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M'`
(box-finiteness for **all** chains one arity shorter). `sjStepHyp_of_coupled`:

- **arity 3 (`L=0`):** IH IGNORED; bottoms at the banked, proven arity-3 `(□)`
  `routeMBoxThresholdFinite_mnp`. (Coupled route is arity ≥ 4 by construction.)
- **arity ≥ 4 (`L=succ`):** `by_cases (∀i,1≤Mi) ∧ ∃t, NondegBindingCut M t`; if yes →
  `hcoupled M t hnd hcut hIH`, else → `hdegen M h hIH`. So `hIH` (the plain IH) flows into `hcoupled`
  and `hdegen` only.

Inside `hcoupled` (discharged by `routeMBoxThresholdFinite_of_coupled` + the bricks, which itself does
NOT take `hIH`), the IH is consumed exactly at **`hbdryShell`** — the **saturated shell `j = r`**
(`u = t+r = min(M₀,M₁)`, so `a = M₀−u = 0` OR `b = M₁−u = 0`). satred's brick signature bakes this in:
`hbdryShell(j=r) : (hIH : RMBTF (redChain (min M₀ M₁) M)) → (density facts) → shellSpineIntegrand … < ⊤`.

The `hcell` cells (`j < r`, `a,b ≥ 1`) are `GenericCellFinite` (RouteMSJHcellNull:101) — a **direct**
`∫ coupledBoxIntegrand < ⊤` statement, NOT phrased through `RMBTF(shorter)`, so none of them
**syntactically** consumes the wrapper's `hIH`. But "not through the wrapper IH" is **statement form**,
not native buildability — split the arms (edgefub correction, satred item 1):
- **INTERIOR (in-regime `a+b ≤ ρ`):** genuinely native — couplerad reduces it to `RectSchurCore (u+a) u
  d c' T`, proven `∀T>0` by `rectCore_schurGen_lt_top` (WellFounded on `min(m,n)`, a **proven arity-3
  base**). Q2-clean in full (native, no reduced-chain descent).
- **EDGE (`a+b = deepTailMin+1`):** Q2-clean only in **statement form**. edgefub (with
  `coupledInner_slice_le`) shows the edge cell FACTORS: factor 1 `|v'|^{−a}` (`a<u` sphere) is native,
  but **factor 2 = the pivot-core `∫_pb frobSq(P·Q̃ₚ)^{−(c'−a/2)}`, finite ⟺ `c'−a/2 < ½·minAdm(redChain
  u M)`** — the reduced-chain RLCT, reached via the SAME `X·Y` front-product descent as the saturated
  shell. So the edge's CONTENT is a reduced-chain descent; it is NOT the wrapper `hIH` (so no Q2
  *pathology through the recursion wrapper*), but it **inherits the square-`u≥3` wall through
  `redChain u M`** exactly when that reduced chain is square-`≥3` (§5). The `a/2` corank charge gives an
  exponent-shift headroom the saturated waist lacks (`c'−a/2` vs `c'`), so an edge cell can be milder
  than its bare-waist analogue — but it is not unconditionally native.

So the plain-IH / reduced-chain-descent question lands on **(i) `hbdryShell`** (saturated shell), **(ii)
the EDGE pivot-core** (factor 2, via `redChain`), and **(iii) `hdegen`** — the interior is fully native.
All three route through the same `X·Y` front-product descent to `RMBTF(redChain u M)`, so they share the
square-`u≥3` wall.

## 2. The pointwise-fold obstruction is REAL (satred's `A > 2Δ`) — exact-ℕ

At the saturated shell `u = min(M₀,M₁)`, the reduction target is `RMBTF(redChain u M)` = the plain IH,
which is valid for `c'' < ½·minAdm(redChain u M) = ½·minAdm(M) + Δ`, `2Δ := minAdm(redChain u M) −
minAdm(M) ≥ 0` (banked `minAdm_le_peelCharge_add_redChain`, since `peelCharge M u = ab = 0`). The
pushforward density of the front product carries a rank-drop weight of pointwise order
`A = max_{1≤j≤min(u,M₂)} j·(M₂ − b − j)`. The **naive pointwise fold**
`ρ ≤ const·frobSq^{−A/2}` reaches only `c' < ½·minAdm(M) − (A/2 − Δ)`, i.e. it **undershoots iff
`A > 2Δ`**. Exact scan (`q2_arith.py`, `minAdm` recursion = Lean's `minAdmRec`, cross-checked vs
`aoyagiLambda` #evals): among chains **with a nondeg binding cut** (so routed through `hcoupled`):

| chain | nondeg cut | saturated `u,a,b` | `A` | `2Δ` | `½minAdm` | pointwise-fold reaches | pointwise-fold |
|---|---|---|---|---|---|---|---|
| (2,2,2,2) | t=1 | 2,0,0 | 1 | 0 | 3/2 | 1 | **undershoots** |
| (3,3,3,3) | t=2 | 3,0,0 | 2 | 1 | 3 | 5/2 | **undershoots** |
| (2,2,3,3) | t=1 | 2,0,0 | 2 | 1 | 2 | 3/2 | **undershoots** |
| (2,3,4,4) | t=1 | 2,0,1 | 2 | 1 | 3 | 5/2 | **undershoots** |
| (4,4,4,4) | t∈{2,3} | 4,0,0 | 4 | 1 | 11/2 | 4 | **undershoots** |
| (3,3,4,4) | t∈{1,2} | 3,0,0 | 4 | 2 | 4 | 3 | **undershoots** |
| (2,3,3,3) | t=1 | 2,0,1 | 1 | 0 | 5/2 | 2 | **undershoots** |
| (2,2,2,2,2)| t=1 | 2,0,0 | 1 | 0 | 3/2 | 1 | **undershoots** |

So a **pointwise-fold saturated brick would inherit Q2** on all of these — satred's satred-cert §4 and
the §3bis-P2 "extract-weight-then-unweighted-IH is UNSOUND" (Codex countercheck `∫ e^{−N(1+c²)z²} ~
N^{−1/2}`, no log, though the extracted `|z|^{−1}` is non-integrable) are both correct **about the
pointwise route**. This is the genuine obstruction the coupled route must not walk into.

## 3. The obstruction is DEFEATED by shell-homogeneity + Hölder (decorrelated Codex) — the escape

The pointwise fold is not the only way to spend the plain IH. Codex (independent, my conclusion
withheld; `codex/crux-answer.md`) supplies a **dyadic-shell** argument on the cleanest witness
`(2,2,2,2)`, where the saturated integrand is exactly

    I(c') = ∫_{P∈box, det P≠0} ∫_{Z∈box} ∫_{W∈box} ‖P·Z·W‖_F^{−2c'}  =  RMBTF((2,2,2,2))|_{P inv}
    (b=0 ⟹ no B₁₂ block; z̃₀ = P·Z; reduced chain (2,2,2) = redChain 2 M; plain IH = RMBTF((2,2,2))).

- **Density (Codex Q1, numerically confirmed).** The pushforward density of `Y = P·Z` (2×2 boxes),
  `ρ(Y) = ∫_{P: P⁻¹Y∈box} |det P|^{−2} dP ≍ (1 + log(σ_max/σ_min))/σ_max`. So the singularity is
  **LOGARITHMIC along the generic `{det Y=0}` hypersurface** (order `α=0`), and the power `r⁻¹` is
  **confined to the origin** (homogeneity). *Monte-Carlo discriminator (`density_shape.py`, guiding
  only):* the conditional density of `σ_min` as `σ_min→0` at `σ_max≍1` increases by a **constant
  additive** amount per halving (9.39→8.24→7.16→6.06→…, Δ≈1.1) — the log signature; a genuine
  `σ_min^{−α}`, `α>0` would show a constant *ratio*. And `r·ρ(rX)` is roughly flat as `r→0` (origin order
  ≈ 1).
- **The argument.** Dyadic shells `E_r = {r/2 < σ_max(Y) ≤ r}`, rescale `Y=rX` (`σ_max(X)∈(½,1]⊆box`,
  `dY=r⁴dX`). Then `ρ(rX) ≲ r⁻¹·L(X)`, `L=1+|log σ_min(X)| ∈ ⋂_p L^p`, and the shell contributes
  `r⁴·r⁻¹·r^{−2c'}·K = r^{3−2c'}·K`, `K = ∫_{X-shell,W} L(X)‖X·W‖^{−2c'}`. By Hölder,
  `K ≤ ‖L‖_{L^p}·(∫‖X·W‖^{−2c'q})^{1/q}` with `q>1`, `c'q < 3/2`; the second factor is the **plain IH
  `RMBTF((2,2,2))` at bumped exponent `c'q`** (`X`-shell ⊆ box). `‖L‖_{L^p} < ∞` for every finite `p`
  (log along a codim-1 locus). So `K < ∞`, and `I(c') ≲ Σ_r r^{3−2c'}·K < ∞` iff `c' < 3/2` — the
  **exact** threshold.

The two features that make this WORK where the pointwise fold fails: (a) the `r⁻¹` origin power is pure
**homogeneity**, absorbed for free by the shell volume `r⁴` (leaving `r^{minAdm−2c'}`, tight); (b) the
Hölder bump is **multiplicative `q→1⁺`** (arbitrarily small threshold cost), not the additive `A/2` of
the pointwise fold. Crucially the escape uses the plain IH on the **full `{IsUnit P}` chart** (no
`σ_min(P)≥δ` pin needed) — the near-singular `P` is swallowed by the density `ρ`, whose origin
homogeneity the shells handle. This is a THIRD route beyond satred's §3bis P2 dichotomy
"(i) uniform chart | (ii) weighted IH": **(iii) homogeneity-shell**, which satred did not consider.

**Tightness (`β = minAdm`).** `I = RMBTF(M)|_{P inv}` has RLCT `½·minAdm(M) = 3/2` (Aoyagi; the exact
`aoyagiLambda(![2,2,2,2]) 0 = 3/2`); the shell decomposition is a faithful reorganization and the origin
is the binding stratum, so the shell exponent `β = minAdm = 3` is forced tight. (A sublevel-slope MC,
`waist_rlct.py`/`calib_rlct.py`, reads `≈1.26` at finite ε — **below** 1.5 — but this is the
**log-multiplicity** artifact: the calibrator `(2,2,2)` reads `≈1.56 ≈ 1.5`, and the deeper `(2,2,2,2)`
has a larger `θ` (log factor) depressing the finite-ε slope; the exact RLCT is 3/2. These
"harmless-multiplicity logs" are exactly satred's `one_add_log_inv_le_rpow` δ-slack — absorbed by the
`q→1⁺` bump, no threshold shift.)

## 4. Reconciling with the documented Q2 / the `sjJointResolution` wall

`sjJointResolution` (RouteMSJResolution:803, bare sorry, "the L≥3 wall") peels at a **general** cut `t`,
emitting the pivot-Gram weight `det(Q_bQ_bᵀ)^{−(M₀−t)/2}` with the **full positive corank charge**
`a = M₀−t ≥ 1`, and recurses through all charts (incl. rank-deficient `Q_b`) — a strictly harder object
than the saturated waist (`a=0`). The coupled route's genuine architectural advance is the **split**:
positive-charge interior cells → native `RectSchurCore` (couplerad; no plain IH); the plain IH is
**isolated to the saturated waist `a=0`**, the ZERO-slack cut where the charge is `0` and (for `u≤2`) the
density is log-clean. So the coupled decomposition **escapes** the `sjJointResolution` wall for `u≤2`;
the wall re-emerges only in the `u≥3` waist strata (§5). This is why the documented Q2 ("plain
undecorated `DecoratedPeelStep` is UNPROVABLE") is true for the **un-split** peel yet does not
automatically kill the **split** coupled route.

## 5. The `u≥3` residual — RESOLVED = Q2-INHERITING (three decorrelated lines)

The interim residual (does the shell escape extend to `u ≥ 3`?) is now **settled: it does not.** The
`u×M₂` front-product density has multiple rank-drop strata, and the corank-`k` stratum carries a genuine
power `γ = ⌊k²/4⌋` (up to log), codimension `k²`. So `ρ_ang ∈ L^p ⟺ p·γ < k²` at every stratum; the
**binding** stratum is corank-2 (`k=2`, codim 4, `γ=1`), giving `ρ_ang ∈ L^p ⟺ p < 4` for **every**
`u ≥ 3` (independent of `u`). The Hölder bump then has `q > 4/3` (not `q→1⁺`), so the plain-IH shell
route reaches only

    c' < (3/4)·½·minAdm(u,u,u) = (3/8)·minAdm(u,u,u)   <   c* = ½·minAdm(u,u,u,u)   (the needed threshold)

`u=3`: reaches `21/8 = 2.625 < 3` (gap `3/8`). `u=4`: reaches `9/2 < 11/2` (gap `1`). The joint
rank-stratified argument that *does* reach `c*` "is itself a weighted/coupled estimate — NOT implied by
the scalar unweighted `B_n`" (Codex U4), i.e. it needs the **weighted/decorated IH** or a `σ_min(P)≥δ`
pin (unavailable at the full-`{IsUnit P}` waist). **Three decorrelated confirmations:**

1. **Second decorrelated Codex** (`codex/u3-{prompt,answer}.md`, my conclusion withheld): origin order
   `A_scale = ⌊n²/4⌋` (so `β = minAdm(n,n,n)`, NOT `minAdm(n,n,n,n)` — angular degeneration lowers
   `7→6`, `12→11`); per-stratum `γ_{r'} = ⌊k²/4⌋`; `ρ_ang ∈ L^p ⟺ p<4`; "the shell route using only the
   unweighted `B_n` reaches sharply only for `n ≤ 2`"; `n≥3` needs a strictly-stronger weighted/coupled
   black box or pinned charts.
2. **satred's waist-density atom** (independent): `b ≥ M₂` bounded; `b = M₂−1` log (all `p`);
   `b ≤ M₂−2` power `ρ ≍ dist^{−A}`, `A = max_j j(M₂−b−j)`, `ρ ∈ L^p ⟺ p < codim/A`. For the `u≥3`
   square waist the corank-2 stratum bites (`p<4`), matching Codex.
3. **My 3×3-product Monte-Carlo** (`u3_strata.py`): rank-2 stratum (codim 1) LOG (`γ=0`, constant
   additive `−1.85`/halving); rank-1 stratum (codim 4) measure `∝ ε³` not `ε⁴` ⟹ density power `γ=1`
   (blows up `∝ dist⁻¹`) ⟹ `ρ_ang ∉ L⁴`. Exactly the `p<4` obstruction.

**Kill-condition status: TRIGGERED at `u≥3`.** The obstruction I set out to prove is REALISED there: the
plain-IH shell bracket `K(c')` diverges before `c*`, and no plain-`SJStepHyp` route reaches `c*` (a
negative, but tightly corroborated by three decorrelated lines + the identical `sjJointResolution` L≥3
wall). The saturated brick's kill-conditions therefore split by `u`:

- **`u ≤ 2` (Q2-clean, native):** **(KC1)** the waist density is log-along-hypersurface (only the codim-1
  corank-1 stratum, `γ=0`) — CONFIRMED; **(KC2)** tight shell exponent `β = minAdm(M)` (`= minAdm(redChain u M)`
  at `u≤2`, so the angular degeneration is trivial); **(KC3)** multiplicative Hölder bump `q→1⁺` only
  (NOT the additive `A/2` pointwise bump); **(KC4)** full-`{IsUnit P}` chart is fine (no `σ_min≥δ` pin).
- **`u ≥ 3` (Q2-inheriting):** the coupled route's `hbdryShell` at a `u≥3` waist is NOT dischargeable by
  the plain arity-IH — it requires the weighted/decorated IH. Route these chains through the **decorated**
  capstone (`routeMBoxThresholdFinite_of_decoratedDescent`), NOT the coupled plain `SJStepHyp`.

## 6. `hdegen` (the other plain-IH consumer) — flagged, not fully audited

`hdegen` handles `¬((∀i,1≤Mi) ∧ ∃t NondegBindingCut)` — degenerate width (`M₀=1`/`M₁=1`, no interior
cut), boundary-argmin, zero width. Zero-width is proven vacuous (`routeMBoxThresholdFinite_of_zero_width`).
The width-1 reductions consume `hIH`; a width-1 leading layer is a free row/column direction (no
square-product density singularity), so these are *likely* Q2-mild — but this is **not** audited here and
should be checked with the same log-vs-power density lens if a width-1 chain routes a nontrivial reduction.

## 7. Levels kept apart

- **Quiver/orbit** — untouched; consumed via `minAdm`/`redChain`.
- **Codim `(C,θ)`** — `A`, `2Δ`, `minAdm` are exact ℕ facts of the `minAdm` recursion; `θ` appears only as
  the log-multiplicity that slows the sublevel MC (harmless, δ-slack).
- **RLCT cap** — this works at the per-shell **finiteness** (`RouteMBoxThresholdFinite`) level, needing
  only the box integral + the plain IH; it does NOT invoke the cited `rlct = ½·codim` equality. `½minAdm`
  here is the box integral's finiteness threshold (Aoyagi-consistent), not a re-derivation of the equality.

## 8. Saturated-brick design (the `u ≤ 2` shell+Hölder form — for the formaliser)

This is the `u≤2` saturated-brick the coupled route can ship (the square `u≥3` waists go to decorated,
§5). **The saturated shell has TWO structurally different forms — dispatch on `sign(M₀−M₁)`:**

- **`M₀ ≤ M₁` (a=0, wide `X=[P|B₁₂]`, NON-injective product):** the **shell+Hölder** brick below (this
  cert owns the assembly; satred supplies the (a)+(b) density atom).
- **`M₀ > M₁` (b=0, tall `[P;C]`, INJECTIVE front):** a **separate qbox leaf** — satred's banked
  `qbox_lintegral_lt_top` on `det(PᵀP+CᵀC)^{−M₂/2}` (`b=M₁,q=M₀,α=M₂`, conv ⟺ `M₂≤a`, recurses if
  `M₂>a`). Injective front ⟹ no pushforward-density power ⟹ NOT the shell assembly. satred owns this leaf
  end-to-end (incl. its Q2-status under the `M₂>a` recursion).

The shell+Hölder brick (a=0 case). Coordinate with satred: satred supplies the **density atom**; this
cert owns the **shell+Hölder assembly**. Target: `hbdryShell` at `j=r`, `u = min(M₀,M₁) ≤ 2`, `M₀≤M₁`,
from the plain arity-IH `RMBTF(redChain u M)`.

- **Object.** `I = shellSpineIntegrand M u κ ε r ⟨r⟩ c'`; at `a=0` (resp. `b=0`) it is
  `∫ frobSq(z̃₀·Zdeep)^{−c'}` over `z̃₀ = X·Y` (`X=[P|B₁₂]` full-row-rank `u×M₁`, `Y=[z₀;A_cor]`
  `M₁×M₂`), `= RMBTF(M)|_{P inv}` (the `{IsUnit P}` chart; `Cresid(0)=1`, second `frobSq` vanishes —
  satred-cert §1).
- **Atom (satred, `u≤2` regime).** The pushforward density `ρ(z̃₀)` of `X·Y`: at `u≤2` it is
  **log-along-hypersurface** — `ρ ≲ σ_max(z̃₀)^{−A_scale}·(1+|log(σ_max/σ_min)|)`, `A_scale = ⌊u·M₂ −
  minAdm(redChain u M)⌋` (`=1` for `(2,2,2,2)`); the angular part `L(X)=(1+|log σ_min(X)|) ∈ ⋂_p L^p`.
  State the atom as: (a) the pushforward bound `ρ ≲ σ_max^{−A_scale}·L`; (b) `L ∈ L^p(σ_max≍1 shell)`
  for every finite `p` (log on the codim-1 corank-1 locus). satred pins the exact `(b,M₂)`-dependent
  constant; at `u≤2` there is one nontrivial stratum, so `L^p`-all-`p` holds.
- **Assembly (this cert).** (1) Dyadic-shell partition of the `z̃₀`-domain by `σ_max`: `E_r = {r/2 <
  σ_max(z̃₀) ≤ r}`, `r` dyadic in `(0, σ_max^{bound}]`. (2) Rescale `z̃₀ = r·X` on `E_r`
  (`σ_max(X)∈(½,1]⊆box`, Jacobian `r^{u·M₂}`; raw-`Pi` matrix CoV per the `Matrix.module` diamond).
  (3) Pull the loss homogeneity: `frobSq(z̃₀·Zdeep)^{−c'} = r^{−2c'}frobSq(X·Zdeep)^{−c'}`; the density
  `ρ(rX) ≲ r^{−A_scale}L(X)`. (4) Shell bound: `∫_{E_r} ≤ r^{u·M₂ − A_scale − 2c'}·K`, `K = ∫_{X-shell,
  deep} L(X)·frobSq(X·Zdeep)^{−c'}`. (5) Hölder on `K`: `K ≤ ‖L‖_{L^p(shell)}·(∫ frobSq(X·Zdeep)^{−c'q})^{1/q}`,
  `1/p+1/q=1`, `q>1` chosen with `c'q < ½minAdm(redChain u M) = ½minAdm(M)+Δ` — the second factor is the
  **plain IH `RMBTF(redChain u M)`** at the bumped exponent `c'q` (restricted to the `X`-shell ⊆ box, so
  `≤` the full box integral). `‖L‖_{L^p} < ∞` (atom (b)). (6) Sum: `I ≲ (Σ_r r^{minAdm(M)−2c'})·K < ∞`
  iff `c' < ½minAdm(M)` (shell exponent `u·M₂ − A_scale = minAdm(M)` at `u≤2`, tight).
- **Kill-conditions to bake into the brick signature** (from §5): **NEVER** a pointwise fold
  (`ρ ≤ const·frobSq^{−A/2}`, additive `A/2` bump — undershoots on `A>2Δ` at every `u`); the Hölder
  bump MUST be multiplicative (`q→1⁺`); the chart is the full `{IsUnit P}` (no `σ_min(P)≥δ` pin — the
  near-singular `P` is absorbed by `ρ`); the shell exponent MUST be `minAdm(M)` (verify `u·M₂ − A_scale =
  minAdm(M)`; this is the `u≤2` fact, and it FAILS at `u≥3` where `A_scale = ⌊u²/4⌋` makes the shell
  exponent `minAdm(redChain u M) > minAdm(M)` and the angular strata bind — the `u≥3` exclusion).
- **Guard (`u≥3`):** the brick MUST assert `u = min(M₀,M₁) ≤ 2` (or, equivalently, single-nontrivial-stratum
  / `b ≥ M₂−1` so `ρ ∈ ⋂_p L^p`); a `u≥3` waist violates the `L^p`-all-`p` premise and is out of scope
  (→ decorated).

## Close

- **Firmest result.** The truth-value splits by `u = min(M₀,M₁)`: **Q2-CLEAN at `u ≤ 2`** (the
  shell-homogeneity + Hölder saturated brick reaches `½minAdm(M)` via the plain unweighted IH + a
  log-shaped density atom — a THIRD route past satred's §3bis "(i) uniform chart | (ii) weighted IH"
  dichotomy; structural + numerical, `(2,2,2,2)`); **Q2-INHERITING at `u ≥ 3`** (the plain-IH
  shell/Hölder/pointwise routes all undershoot — corank-2 stratum power `γ=1`, `ρ_ang∈L^p ⟺ p<4`,
  reaching only `(3/8)minAdm(u,u,u) < ½minAdm(u,u,u,u)`; the sharp escape needs the weighted/decorated
  IH). Interior/edge cells are native `RectSchurCore` bricks (no plain IH). **Since the mint is `∀-M` and
  `u≥3` chains are in-scope, the DECORATED route is canonical for the full closure; the coupled route
  natively closes only `u≤2`.**
- **Most likely to break it (both directions).** (i) If someone builds a `u≥3` saturated brick on the
  plain IH via any of the three plain-IH routes, it WILL undershoot — do not ship it. (ii) The one
  inference (not a hard proof) is "no plain-`SJStepHyp` route reaches `c*` for `u≥3`" — a negative;
  corroborated by two independent Codex consults + satred's atom + the 3×3 numerics + the identical
  `sjJointResolution` L≥3 wall, but a genuinely-new plain-IH manipulation would refute it (unlikely, but
  the honest residual). (iii) `hdegen` (width-1) is not fully audited (§6).
- **Next.** (a) Route `u≥3` chains to the decorated capstone (the endgame call). (b) satred + this cert
  co-produce the `u≤2` shell+Hölder saturated brick per §8 (the one new atom = the `u≤2` log-density
  bound). (c) Optionally harden the `u≥3` negative into "no unweighted-IH argument reaches `c*`" via the
  determinantal-stratum RLCT lower bound (the `sjJointResolution` L≥3 content) — but the operational call
  (decorated canonical) does not wait on it.

Files (absolute):
- `…/threads/genm-q2gate/q2gate-cert.md` (this cert)
- `…/threads/genm-q2gate/codex/crux-{prompt,answer}.md`, `crux-run.log` (decorrelated consult, `u≤2`)
- `…/threads/genm-q2gate/codex/u3-{prompt,answer}.md`, `u3-run.log` (decorrelated consult, `u≥3` strata)
- `…/threads/genm-q2gate/{q2_arith,density_shape,waist_rlct,calib_rlct,u3_strata}.py` — guiding scripts
  (exact-ℕ `q2_arith`; the rest float, not load-bearing).

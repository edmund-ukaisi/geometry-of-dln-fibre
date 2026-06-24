# D1≥ two-point core-domination — VALUE-FREENESS CERTIFICATE (pp-hall, 2026-06-21)

**Task #112.** Is the two-point domination `core(deepest) ≤_local core(v)` (Aoyagi 2013 Thm 2, the
fibre-monotonicity giving D1≥) VALUE-FREE — provable from normal-form *existence* + a germ-domination
argument (S1 `|G|≤|F|` + L1 + deepest), WITHOUT R1's resolution *value* `⨅ monomialThreshold =
lambdaCore`? If value-free, D1≥ closes parallel-now; if it needs the value, D1≥ is R1-gated.

**Verdict: VALUE-FREE.** D1≥ is independent of R1's resolution value. It closes parallel-now (parallel
to #111/#113), from the green primitives + two named *existence* obligations (neither is the value).
Two decorrelated legs converged: (1) pp-hall exact source + symbolic; (2) Codex (xhigh) independent.

## What the live `sorry` must prove (Skeleton.lean `deepest_point_reduction`, line 981)
`refine le_iInf₂ (fun v _ => ?_)` then for every `v ∈ optimalSet H B`:
`rlctAt H (dlnLoss H B) (deepestPoint …) ≤ rlctAt H (dlnLoss H B) v`.
(The `≤` half of the antisymmetry — `iInf₂_le` — is already PROVEN; this is the residual `≥`.)

## The source (Aoyagi 2013, Entropy 15:3714) — exact, primary
- **Theorem 2** ("method for finding a deepest singular point"), p.3720–21 (`entropy-15-03714.pdf`):
  for `f₁…f_m` homogeneous of degree `nᵢ` in `w₁…w_j` (spectators `w_{j+1}…w_d`) and a `C^∞` bump `ψ`
  with `ψ(0,…,0,w*_{j+1},…) ≥ ψ(w*)`:
  `λ_{(0,…,0,w*_{j+1},…)}(Σfᵢ²,ψ) ≤ λ_{w*}(Σfᵢ²,ψ)`.
- **The proof** (verbatim mechanism): blow up `wᵢ = v·wᵢ'` along `{v=0, wᵢ=0}`; homogeneity gives
  `fᵢ(w) = v^{nᵢ}fᵢ(w')`, so `Σ v^{2nᵢ}fᵢ'² ≤ Σ fᵢ'²` for `|v|<1`, then **Lemma 1 (Appendix C)**.
- **Lemma 1(1)** (Appendix C): `g²≤f² ⟹ λ_{w*}(g²) ≤ λ_{w*}(f²)` at the SAME point — this is EXACTLY
  our green `rlctAt_mono` (task #51).
- **Example 3** (immediately after the Q.E.D.): D1≥ is FALSE for a general critical point `w₀` lacking
  the homogeneity (`f₁=x(x−1)², …`, `λ_{(1,0,0)}=3/4 > λ_{(0,1,1)}=2/3`). Homogeneity is ESSENTIAL —
  this is the scope boundary, and it is why D1 must be applied to the HOMOGENEOUS core, not the raw loss.

## The step-by-step (every step labelled; NO step USES-VALUE)
| step | content | label |
|---|---|---|
| 1 | radial/blow-up chart `w = t·(a+u)` toward the comparison direction `a` | PURE-ALGEBRA + CHANGE-OF-VARIABLES |
| 2 | homogeneity: `fᵢ(t(a+u)) = t^{nᵢ}fᵢ(a+u)`, `K(t(a+u)) = Σ t^{2nᵢ}fᵢ(a+u)²` | PURE-ALGEBRA |
| 3 | `|t|<1`: `Σ t^{2nᵢ}fᵢ'² ≤ Σ fᵢ'² = K(a+u)` | PURE-ALGEBRA |
| 4 | same-point monotonicity in the common chart (`rlctAt_mono` = Lemma 1(1)) | SAME-POINT-MONOTONICITY |
| 5 | transport the scaled pullback back: contribution at deepest `0` vs germ at `a` | CHANGE-OF-VARIABLES (S1) |
| — | admissible-tree min / monomialThreshold / closed-form RLCT | **USES-VALUE: NONE** |

Exact symbolic confirmation: on (2,1,2) r=0 the scaling is `Σ t^{2nᵢ}fᵢ² = t⁴·F ≤ F` for `|t|<1`
(`d1_twopoint.py`, `Fs − F = (a0²+a1²)(b0²+b1²)(t−1)(t+1)(t²+1)`). Pure homogeneity; no value.

## The two GENUINE prerequisites (existence, NOT value) — where the load actually is
D1≥ consumes, beyond the green primitives, two *existence* obligations. **Neither is R1's value.**

**(a) Homogeneous-residual-form existence at an ARBITRARY fibre point `v`.** At a non-deepest `v` the
core generators are NOT homogeneous in the local coords — they carry a nonzero LINEAR leading part, so
`v` is a smooth point in those directions (`d1_homog_check.py`: at `v=(A¹=0, A²≠0)` the generators are
`c_j·wᵢ + wᵢ·eⱼ`, leading-linear). Concretely on (2,2,2) r=0, a rank-(1,1) fibre point `v` has
generator-Jacobian rank 3 (`d1_222_strata.py`): the germ splits as `Q(x) + K_res(y)` = [nondegenerate
quadratic block, dim 3, each `+½`] ⊕ [homogeneous residual core], giving `λ_v = 3/2 + λ(residual) >
3/2 = λ_deepest` — the deepest is STRICTLY minimal (`d1_222_resid.py`). The split is a local
constant-rank / implicit-function / Morse-with-parameters reduction (S1-type analytic c-o-v) — its
EXISTENCE; the residual core's homogeneity is pure algebra. **This is L1 / G3.2's chart EXISTENCE
(#111), NOT its value.** Aoyagi's `ψ`-monotonicity hypothesis is satisfied because the regular block is
a positive UNIT bump (`ψ(0)=1 > 0`, cosmetic; `d1_mechanism_exact.py`).

**(b) Strata-coverage + deepest-in-closure.** The SAME deepest point must dominate EVERY `v`. This is a
fibre-stratification statement (rank patterns), **value-free**: the fibre core variety `{prod=0}` is a
CONE — `prod(t·A) = t^L·prod(A)` (`d1_closure.py`, exact: `prod(t·A) − t²·prod(A) = 0` on (2,2,2)) — so
the scaling ray `t→0` keeps `v` in the fibre and limits to the all-zero deepest core. Hence the deepest
is in every stratum's closure. Pure algebraic geometry of the fibre; no RLCT value.

**Scope flag (the honest gap, per Example 3):** D1≥ is value-free *given* (a)+(b). If (a)/(b) are not
established, D1≥ has a STRUCTURAL gap — but the missing ingredient is the normal-form/coverage
EXISTENCE, **not R1's value**. So D1≥ is NOT R1-gated; it is (a)/(b)-gated, and (a) is the same chart
#111 already builds.

## The clean decomposition into green primitives (the formaliser's target)
For each `v ∈ optimalSet H B`:
1. local analytic c-o-v at `v` → germ = regular block `Q(x)` ⊕ homogeneous residual core `K_res(y)`
   (= L1/G3.2 chart existence #111 + S1 c-o-v invariance) — **no value**
2. regular directions contribute `q/2 ≥ 0` (S1 smooth-block, green) — **no value**
3. Aoyagi homogeneous scaling `Σ t^{2nᵢ}fᵢ'² ≤ Σ fᵢ'²` (`|t|<1`) on `K_res` — **pure algebra**
4. `rlctAt_mono` (= Lemma 1(1), green #51) turns the scaling into the RLCT inequality — **green**
5. S1 transports back; `prod` cone ⟹ deepest in closure (`d1_closure.py`) — **pure algebra + S1**
⟹ `λ_deepest(F) ≤ λ_v(F)`. NONE of 1–5 is `⨅ monomialThreshold = lambdaCore` (R1's value).

## Net for the parallelism gate
**D1≥ is VALUE-FREE ⟹ it closes PARALLEL-NOW** (does not wait for R1 #111/#113's value). Its engine is
`rlctAt_mono` (#51, green) + S1 (green) + homogeneity (pure algebra) + the G3.2 chart EXISTENCE (#111,
shared) + the fibre-cone closure (pure algebra). a114e07e can build D1≥ from L1 + deepest + S1-germ +
`rlctAt_mono` + the chart-existence, with no dependence on the resolution value. The one thing not to
gloss (Example 3): apply to the HOMOGENEOUS core, with the (a)/(b) existence obligations stated, never
to the raw `B≠0` loss.

## The sketch in a114e07e's exact green-tool names (the build wiring)
The line-981 obligation `rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v` (for each
`v ∈ optimalSet H B`) maps onto the green primitives as follows (all verified present, signatures read):

| step | tool (exact name, verified) | role at the D1≥ site |
|---|---|---|
| germ-locality | `rlct_germ_local_aux` (`Foundations/S1Local.lean:97`) — `F=G` on a nbhd ⟹ equal RLCT | makes the comparison LOCAL at `v` / at deepest; lets the L2/G3.2 normal form replace the raw germ |
| gauge / normal-form c-o-v | `rlctAtOn_comp_homeomorph` (`Foundations/S1Fubini.lean:54`) | transports `rlctAt` along the GL-gauge / block-normal-form homeomorphism at `v` (the L1 `block_elimination` chart, EXISTENCE) |
| ψ-bump cancel | `rlct_unit_invariant_aux` (`Foundations/S1Local.lean:38`) — `0<a≤|u|≤b` on a nbhd ⟹ `rlctAt (u·F)=rlctAt F` | discharges Aoyagi's `ψ`-hypothesis: the regular block is a POSITIVE unit `u` (`u(0)=1`), factors out RLCT-free |
| regular block value | `smoothBlockND_rlct` (`Foundations/S1SmoothBlock.lean:164`) — `rlctAtOn(Σxᵢ²) 0 = (m+1)/2` | the `q` nondegenerate quadratic directions at `v` add `q/2` (additive via S1.5 Fubini); `≥ 0` |
| the two-point inequality | `rlctAt_mono` (`Foundations/Rlct.lean:93`, #51) — `\|G\|≤\|F\|` + `(G=0→F=0)` on a nbhd ⟹ `rlctAt G ≤ rlctAt F` | = Aoyagi Lemma 1(1); consumes the homogeneous scaling `Σ t^{2nᵢ}fᵢ'² ≤ Σ fᵢ'²` (`\|t\|<1`) on the residual core |
| deepest-in-closure | (pure algebra — `prod (t•A) = t^L · prod A`, the fibre core is a cone) | the all-zero deepest core is the `t→0` limit of every `v`; no tool, no value |

The `rlctAt_mono` hypothesis is met cleanly: with `G = Σ t^{2nᵢ}fᵢ'²` and `F = Σ fᵢ'²` (the residual
core in blown-up coords), `|G|≤|F|` for `|t|<1` is the scaling inequality and `G=0→F=0` is trivial
(same zero-set, `t≠0`). NONE of these tools is R1's value (`⨅ monomialThreshold = lambdaCore`) — that
value lives only in `resolution_charts` / `product_reduction`, downstream and separate. So a114e07e
builds D1≥ from `block_elimination` (L1) + `deepestPoint_isDeep` (deepest) + the four S1-germ tools
above + `rlctAt_mono`, with the two existence prerequisites (a)/(b) as stated obligations — **off the
R1 critical path.**

Decorrelation: pp-hall (Aoyagi 2013 source Thm 2 + Lemma 1 + Example 3 verbatim; 7 exact-symbolic
scripts in `d1-scripts/`) + Codex xhigh (independent: VALUE-FREE, same step-labels, same regular-split
for (B), same fibre-stratification for (C), "USES-VALUE: none"). Converged. Consult banked at
`codex/d1-valuefree-{prompt,answer}.md`.

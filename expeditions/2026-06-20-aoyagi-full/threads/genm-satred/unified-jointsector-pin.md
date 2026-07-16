# unified-jointsector-pin — the ONE joint-rank-sector descent for all HARD cells

**Seat:** pen-and-paper (design, decorrelated), `genm-satred`, capstone. **Date:** 2026-07-16. **NO Lean.**
The unified mechanism the controller adopted (the leaf-1 confound revealed the unification). Subsumes
`hFrontReduce` (edgefub's front reduce), the edge two-chain descent (`hBackbone-edge-pin`), the two waist
bricks (`waist-pin` a=0/b=0), and the interior-HARD shells (`leaf1-soundness`). Consolidates
`backbone-cert` (decorated joint descent) + `D-cert` (joint rank-sector) + `satred-cert` (X·Y). Verified:
exact-ℕ (`scripts/{kill_check,waist_reach,edge_twochain,leaf1_threshold2,draft_route_sound}.py`, all 0-fail
on the min-recursion) + decorrelated Codex (`codex/{backbone,brickD,edgereach,leaf1}-answer.md`).

---

## ★ THE MECHANISM (one seam, four instances)

A **HARD cell** (a corner/shell where the bare-constant front bound undershoots — `minAdm(M) > ab +
u·(conditioned frame dim)`, the A>2Δ regime) is reduced to `½minAdm(M)` by the **joint-rank-sector
descent**: reorganize the front into a coupled linear factor, stratify a rank, reduce each stratum to a
DIFFERENT shorter chain `redChain u'_r M` carrying the reduced-Gram `det(GGᵀ)^{−·}` to the arity-IH via
`qbox`, and `min_r [charge_r + minAdm(redChain u'_r M)] = minAdm(M)` (the `minAdm` recursion, geometrically).
**No `(□)` wall** (every hard cell `⊆ RMBTF(M)`, reaches `½minAdm(M)`). The four instances differ ONLY in
which factor is stratified + the `qbox` dims + the chains.

## 0bis. SUPERSESSION (q2gate Q2, LATE-84) — the SATURATED instances use Hölder, not the pointwise fold

The waist-a0/b0 saturated instances' POINTWISE density fold undershoots on A>2Δ (q2gate verified). The
working saturated route is **q2gate's dyadic-shell (σ_max) + Hölder** with the plain unweighted IH + the
STANDALONE waist-density atom (my characterization). So in the table below, waist-a0/b0's "carry" is NOT the
pointwise fold — it is the density atom fed into q2gate's Hölder assembly. The interior-hard/edge instances
(P2 pivot-Gram carry) are unaffected by this note; they remain the uniform-chart / full-coupling content.

## 1. The easy/hard GUARD (arch1build's dispatch)

Per shell/corner at cut `u=t+j` (`a=M₀−u`, `b=M₁−u`, `M₁−j = b+t` = the shell's conditioned SV count):
- **EASY** (`minAdm M ≤ ab + u·(M₁−j)`): the bare-constant front bound (threshold `u(M₁−j)/2`, shell-
  conditioned domain) reaches → `deeperFlagCore + L1` (route α, brickf's easy leaf). Built machinery.
- **HARD** (`minAdm M > ab + u·(M₁−j)`, the A>2Δ regime — 6090/76832 interior shells + all edge-tie + all
  waist a=0/b=0): the bare constant caps below `½minAdm M` → **the unified joint-rank-sector descent**.

## 2. The THREE shared primitives (the seam)

**(P1) Coupled reorganization (the X·Y / [P|B₁₂] / [P;C] seam) — EXACT, banked block identity.** The front
energy is LINEAR in the joint front factor `F`: `frobSq(F · G)`, `G` = the reduced-chain leading-Gram data
(a function of the reduced params `z` and the corank `A_cor`). No affine drop (verified |lhs−rhs|~1e-14).
- wide `F=[P|B₁₂]` (u×M₁), `G=[z₀;A_cor]·Z_deep` (interior/edge/waist-a0);
- tall `F=[P;C]` (M₀×M₁), `G=Q_p=z₀·Z_deep` (waist-b0).

**(P2) Rank-sector blow-up + the Gram carry — THREE distinct Gram integrals (precision, review-corrected).**
Stratify the critical rank `r`; on stratum `r`, the rank-drop peels to a deeper effective cut `u'_r` (reduce
to `redChain u'_r M`). The Gram-carry object depends on WHICH VARIABLE it is integrated over — a distinction
that is load-bearing (verified exact-ℕ + decorrelated Codex; the controller flagged it "most likely to break"):
- **PIVOT Gram** `det(Q̃ₚ Q̃ₚᵀ)^{−a/2}`, `Q̃ₚ` the u×n pivot block — integrated over the REDUCED-CHAIN
  params `z` (NOT over `A_cor`). It IS the reduced chain's own leading-layer Gram singularity, so it is
  **ABSORBED by `redChain u'_r M`'s recursion (the arity-IH)** — not a separate integral. (interior-hard, edge.)
- **WAIST-b0 Gram** `det(PᵀP + CᵀC)^{−M₂/2}` — a LITERAL `qbox` over the FRONT `(P,C)` box
  (`RouteMSJQBoxCore.qbox_lintegral_lt_top`, `(qbox-b,qbox-q,α)=(M₁,M₀,M₂)`, converges ⟺ `M₂ ≤ a`; `M₂>a`
  recurses one level — D-cert §3bis).
- **CORANK Gram** `∫_{A_cor box} det((A_cor·Z_deep)(·)ᵀ)^{−a/2}` — a strong-block over `A_cor`, converges
  iff `a < ρ−b+1` (ρ=rank Z_deep). **This is the TRAP: it FAILS at the edge `a+b=ρ+1` (a=ρ−b+1 exactly;
  21898/26460 interior shells are in its failure region).** It is the EASY route's (L1's) corank weight; the
  HARD route must NOT fall back to it — the coupled rank-sector (pivot Gram → IH) replaces it precisely
  because the corank strong-block fails on the hard shells. **NEVER cite the corank strong-block for a hard
  cell; carry the PIVOT Gram to the IH (or the literal front-box `qbox` for waist-b0).**

**(P3) Min-over-strata = the recursion.** `min_r [charge_r + minAdm(redChain u'_r M)] = minAdm(M)` — this
IS the `minAdm` recursion realized geometrically (`minAdm_le_peelCharge_add_redChain`). Reaches `½minAdm(M)`
for `c'<½minAdm(M)`; coincident-charge strata give harmless-multiplicity logs (δ-slack, no threshold shift,
`one_add_log_inv_le_rpow`). Verified across instances: interior-hard 0/4039 (`kill_check`), edge 0/1076
(`edge_twochain`), waist-a0 0/10976, waist-b0 0/10976 (`waist_reach`).

## 3. The FOUR instances (specializations)

| instance | front `F` | stratify | chains `redChain u'_r M` | Gram carry | notes |
|---|---|---|---|---|---|
| **interior-HARD** | `[P|B₁₂]` wide | `rank(G=[Q_p;Q_b])` | per stratum `r`, `u'_r` = cut+drop | `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` via qbox | A>2Δ, `minAdm M>ab+u(M₁−j)`; corank `Γ·Q_b` term present |
| **edge-tie (b=1)** | `[P|B₁₂]` | `rank(A_cor·Z_deep)∈{0,1}` | `redChain u M` (r=1) + `redChain (u+1) M` (r=0) | — (leaf: `\|v'_{j₀}\|^{−a}`, a<u sphere) | 2 chains, both @ `c'−a/2`; tie-log δ-fold |
| **waist a=0** | `[P|B₁₂]` wide (`X·Y`) | `rank(z̃₀=X·Y)`, `s∈0..M₀` | `redChain s M` | wide-product density `ρ(z̃₀)` (order `A=max_j j(M₂−b−j)`) | `u=M₀≤M₁`; genuinely-new density (the ONE non-qbox instance) |
| **waist b=0** | `[P;C]` TALL | `rank([P;C])` | `redChain M₁ M` (drops M₀) | `det(PᵀP+CᵀC)^{−M₂/2}` via qbox (b=M₁,q=M₀,α=M₂), conv ⟺ M₂≤a | `u=M₁≤M₀`; CLEANER (injective CoV, banked) |

All four: (P1) coupled reorganization → (P2) rank-sector + Gram carry → (P3) min = `minAdm(M)`. The edge is
the corank-rank instance (2 strata); the waists are the front-rank instances (wide/tall dual); interior-hard
is the corank-rank instance with the full A>2Δ strata. `hFrontReduce` (edgefub's front→RMBTF) = the (P1)+(P2)
core specialized to the edge. **Only waist-a0's `hdens` (the wide density `ρ`) is genuinely-new; the other
three carry `det(GGᵀ)` via banked `qbox`/`gammaAtom`.**

## 3bis. Decorrelated premise review (Finding 7) — P1 sound; P2/P3 are INFERENCES with named gaps

A decorrelated Codex xhigh (`codex/premise-{prompt,answer}.md`, conclusion withheld) red-teamed the P1/P2/P3
geometric premise. Verdict: the STRUCTURE is right, but **P2/P3 are inferences, not proven** — the tide must
build genuine analytic content, and the naive "extract bare determinant + invoke IH" is UNSOUND.

- **P1 — SOUND (Jacobian = 1), with a coordinate caveat.** The reorganization `[P|B₁₂][Q_p;Q_b] = P(Q_p +
  P⁻¹B₁₂Q_b)` (and the tall stacking) is measure-preserving IN THE ORIGINAL `(P,B₁₂)` variables (Jac 1).
  **Do NOT substitute `D=P⁻¹B₁₂`** — that introduces `dP dB₁₂ = |det P|^b dP dD`, harmless only on a
  `σ_min(P) ≥ δ` chart (the det-P hazard resurfaces). Also: the WIDE product is NOT rank-preserving
  pointwise (`P=B₁₂=1, Q_p=1, Q_b=−1 ⟹ FG=0` while `rank G=1`); the front-map `F↦FG` has rank `ur` for
  `rank G=r`. The TALL `[P;C]` is injective ⟹ rank-preserving.
- **P2 — the corank/pivot distinction is REAL, but pivot-Gram IH-absorption is an INFERENCE.** Codex
  COUNTERCHECK: `∫_{[−1,1]²} e^{−N(1+c²)z²} dz dc ~ N^{−1/2}` (NO log) though the extracted pivot weight
  `|z|^{−1}` is NON-integrable. **So "carry the pivot Gram to the IH" must mean carrying the FULL finite-N
  coupling — NOT extracting `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` pointwise and invoking an unweighted IH (UNSOUND).** Valid
  only when (i) the IH explicitly handles the coupled/weighted reduced chain, OR (ii) `P` is uniformly
  invertible on the chart (`σ_min(P)≥δ`), so `‖PQ̃ₚ‖²` is uniformly comparable to `‖Q̃ₚ‖²`. This is exactly
  the backbone-cert's "refined joint descent" (relatively-compact GL charts + boundary resolution, OR the
  coupled full-coupling IH) — the pivot-Gram carry IS the genuine analytic core (= Bricks F/D), NOT a
  one-line extraction.
- **P3 — the min-over-strata is an INFERENCE.** The `min_r[charge_r + minAdm(redChain u'_r M)] = minAdm(M)`
  ARITHMETIC is verified (0-fail); but its PROOF as a domination needs the rank-stratum normal
  Jacobians/codimensions + the log multiplicities (the actual determinantal blow-up geometry), not only the
  minimum exponent.
- **Cheapest de-risk (Codex Q3, for the tide):** on every pivot-IH chart, prove the UNIFORM sandwich
  `m²‖Q‖²_F ≤ ‖PQ‖²_F + ‖CQ‖²_F ≤ (M²+K²)‖Q‖²_F` (`m>0`, constants uniform on the chart) — this immediately
  gives RLCT + log-multiplicity equality with the reduced chain. **If the uniform constants fail, the IH
  absorption is NOT justified** (the boundary logs are created/erased by a non-uniform Gaussian/Fubini step —
  the single biggest soundness risk). So the tide's FIRST obligation is the uniform-chart sandwich, per
  instance.

**Net:** P1 clears (keep original vars, no D-substitution). P2/P3 do NOT clear as one-liners — the pivot-Gram
carry needs the uniform-`P` chart (or full-coupling IH), and the min-recursion needs the stratum-Jacobian
domination. These are the backbone's Bricks F/D, now confirmed as the unified descent's genuine analytic
core. The exponent arithmetic (P3-min) is a DONE certificate; the analytic domination is the build.

## 4. Banked vs new

**BANKED (consume):** the coupled block identity / `prod_headSplit` / `hsQ` (P1); `gammaAtom_aniso_shifted_eq`
+ `qbox_lintegral_lt_top` (P2 Gram carry); `minAdm_le_peelCharge_add_redChain` (P3 recursion); the arity-IH
`sjStepHyp_of_coupled` (`∀ shorter chain, RMBTF`); `one_add_log_inv_le_rpow` (δ-fold); `scaledRadialEuclid`
+ `corner_block_lintegral_lt_top` (edge leaf); `edge_generic_cells_of_box` + `exists_measurable_nonzero_index`
(edgefub, edge cells + j₀ selector). **NEW (build, ONE formaliser):** (i) the per-stratum rank-sector blow-up
(the determinantal stratification + the per-stratum charge → `redChain u'_r M`); (ii) the `qbox`-recursion
threading (the per-level pivot-Gram folds into `redChain`'s recursion); (iii) waist-a0's wide-product density
domination (the genuinely-new `ρ(z̃₀)` order bound — the ONE hard analytic atom); (iv) the min-over-strata
assembly (= the recursion, arithmetic). **Diamond guard:** raw-`Pi` for all matrix CoV/products.

## 5. The open piece (per-instance `qbox` dim-matching → reduced-chain IH)

For each instance, the `qbox` `(b,q,α)` must be read from the ACTUAL front/Gram dims (interior: `Q̃ₚ`
row/col; waist-b0: `[P;C]ᵀ` = `M₁×M₀`, `(b,q,α)=(M₁,M₀,M₂)`; edge: no qbox, the `a<u` sphere). The single-
level `qbox` is strict in a range; the marginal cells recurse ONE level into `redChain u'_r M` (the arity
recursion — D-cert §3bis, verified single-level strict for 209/283 a≥u edge cells, the rest recurse). This
dim-matching FOLDS into the coherent-unit merge (it has the exact dims + the recursion); no further pen-and-
paper design. Finiteness is guaranteed (`⊆ RMBTF(M)`).

## Close

- **Firmest.** The unified joint-rank-sector descent is the ONE mechanism for all hard cells (interior-A>2Δ,
  edge-tie, waist a=0/b=0), reaching `½minAdm(M)` via `min_r[charge_r + minAdm(redChain u'_r M)] = minAdm(M)`
  (verified 0-fail across all four instances). Three shared primitives (coupled reorganization; rank-sector
  + `det(GGᵀ)`→qbox→IH; min-recursion); four specializations differing only in the stratified factor + qbox
  dims. Subsumes hFrontReduce + the edge/waist descents + the two waist bricks. Easy/hard guard =
  `minAdm M ≤ ab + u(M₁−j)`. No `(□)` wall.
- **Most likely to break the BUILD.** (i) qbox on the corank Gram (the `a=q−b+1` trap) — always the PIVOT
  Gram. (ii) Treating waist-a0 by qbox (it's the genuinely-new wide density `ρ`, NOT qbox). (iii) A one-shot
  qbox where the marginal cells must recurse (the per-level arity recursion). (iv) The edge/interior corank-
  rank tie-logs must δ-fold (harmless, but present). (v) Forcing the bare constant on a hard cell (unsound).
- **Next.** ONE formaliser builds the unified descent (the 3 primitives + the 4 instance specializations);
  brickf builds the easy leaf; the wrappers (edgefub, waist) consume it as instances; arch1build guards the
  easy/hard split (`minAdm M ≤ ab+u(M₁−j)`). The one genuinely-new atom is waist-a0's density; everything
  else is banked qbox/gammaAtom + the rank-sector chart-maps + the recursion. I pin any per-instance detail
  (the exact qbox dims, the waist-a0 density order) on request.

Files (absolute): `…/threads/genm-satred/unified-jointsector-pin.md` (this); `backbone-cert.md`, `D-cert.md`,
`hBackbone-edge-pin.md`, `waist-pin.md`, `leaf1-soundness.md`, `brickD-{pin,sublemmas}.md`, `satred-cert.md`;
`codex/{backbone,brickD,edgereach,leaf1}-answer.md`; `scripts/{kill_check,waist_reach,edge_twochain,leaf1_threshold2}.py`.

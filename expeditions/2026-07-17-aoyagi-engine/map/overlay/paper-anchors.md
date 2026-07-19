# Overlay — paper anchors (cartographer-6, 2026-07-19, operator fidelity-steer pass)

*Every landmark + banked family carries a PAPER ANCHOR: the `worked.tex` §/line (and preprint page) it
realizes. Every DEVIATION from the paper is marked as a DOCUMENTED typo-fix (the registry below) or
FLAGGED unanchored. Provenance: operator steer 2026-07-19 (compass standing counsel `:513-532` — "THE
PAPER IS THE ACTIVE FIDELITY TOUCHSTONE" + "MATHEMATICAL NECESSITY IS THE BAR, NOT LEAN-BUILD PROGRESS").
Paper = `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` (+ preprint images
`aoyagi-2023-neural-networks-preprint.pdf`). Anchors verified against `worked.tex` at HEAD `6ba880ec6`.*

## CARTOGRAPHER STANDING POSTURE (this office's working note)

**When judging map placement / naming / promotion, the PAPER's structure outranks the module DAG's
convenience.** A family named or placed for Lean-import tidiness, if it cuts across the paper's
mathematical joints, is mis-mapped — re-anchor to the paper's object. An overlay card that cannot be
anchored to `worked.tex` (or a documented typo-fix) is exactly the "silent Lean-convenience" the steer
hunts: flag it, do not launder it as banked. A green build never anchors a card; the paper does.

## Documented-deviation registry (the "known four" + instance-#9)

*A deviation from the paper's printed form is legitimate ONLY as one of these. Anything else on a card is
a stray to flag.*

| # | deviation | paper site | fix / status | consuming cards |
|---|---|---|---|---|
| **T-D / F-1** | Def 3 condition (iii) sign prints `≤`, empty on the majority (105/216 at L=2) + contradicts Thm 1 | `worked.tex:834-865` (ledger); Def 3 `:245-274` | GENUINE paper typo (`≤`→`≥`); replaced by the geometric primitive `rlct_core = ½·Mval_min` over the admissible lattice with `t_L=0` (`:848-857`). Witness `g-def3-broken`. | exponent-ledger-bridge, R1 (minAdm), resolution-tree |
| **T-C** | Case-2 exponent prints raw `(M(S)−J)(M^{(S+1)}−J)` | `worked.tex:522-525, 881-885`; preprint p.20 | image-pinned; non-binding (`2·rlct ≤ M^{(i)}M^{(j)}`, never attains min). Lean FIX-A caps the head-reset at the RUNNING-MIN width (`EngineDefs.stepUpdate` case2, `:167-177`). | resolution-tree (stepUpdate case2) |
| **p.15 chain** | total-comparability of the divisor chain (p.15) is FALSE at interior bottlenecks (`∃ 3≤S≤L, r_S<r_2`) | preprint p.15; `worked.tex:499-510` (Case 1) | reshaped to `SameLevelChainInv` + `LiveHeadDom` (the live-restricted bound). [[dead-routes]] full-chain kill. | resolution-tree, carrier (EngineConstruction), o5 |
| **realization gap** | the implicit "t̃=0 profile-set = ALL of Adm" is FALSE — stranded profiles at interior-bottleneck widths | `worked.tex:527-538` (t̃=0 read-off); defect `verify-realization-gap-defect.md` | `realizedProfiles = {a∈Adm : Clearable a}` (ClearableReify); the minimizer fact `minAdm∈terminalExponents` stays safe. | ClearableReify, o5-realization |
| **instance-#9 (three-ledger split)** | the stranded-divisor DICHOTOMY is FALSE — reachable terminals carry t̃>0 divisors with divExp>1 that the FOLD blows up | `worked.tex:492-494` ("∏_{s,k} u^{M−1} over ALL exceptional divisors"); compass `:533-545`; `cert-stranded-dichotomy` | the JACOBIAN (LeafJacobian β-det) reads the FULL ledger (`fullDivCoord`/`fullDivExp`); LOSS / (C) / RLCT-pole read the ANALYTIC (t̃=0) ledger. region_glue survives via `|det|_full ≤ |det|_analytic·K_R` thin wrapper. **This is a fidelity CORRECTION toward the paper** (the t̃=0 Jacobian filter was OURS, `:519-520` — the stray the steer's own example names). | fold-Jacobian spine, LeafPullback, region_glue |

## Landmark anchors (8)

| landmark | paper anchor (`worked.tex`) | deviation |
|---|---|---|
| mint-repoint | §clean `:707-726` (the closed form = formalisation target) + Thm 2 `:275`; `aoyagiLambda` = `:858-860` | — (the honest headline) |
| hbox-root | the resolution route to RLCT `:171-199` (Hironaka + monomial S2 rule) + the boxed `rlct_core = ½·min{M_{s,k}: t̃=0}` `:537` — hbox = the FINITENESS half | — |
| engine-route | §blowup `:468-526` (the recursive `(S,J)` blow-up IS reduce→tree→coverage→thresholds) | — |
| resolution-tree | the inductive invariant `:475-490` (`diag(b)`, `b_i=∏_{t̃=i−1}u_{s,k}·b_{i−1}`) + Cases 1&2 `:499-520` | T-C (case-2), p.15-chain, + coupled-`diag(b)` support-field NECESSITY `:631-649` (design-necessity, not a typo) |
| coverage-theorem | the structural cover lower bound `:564-567` (α-divisor `≥½Mval(0)`, ρ-divisor `=½Mval(branch)`, recursive `≥½min` by induction) | — |
| exponent-ledger-bridge | terminal exponent `M_{s,k}` `:531-533` + boxed `:537` + `M_{s,k}=Mval=codim` `:540` + Lemma 3 `:668-694` (`N-1`, NOT a typo) | T-D/F-1 (Def-3) |
| theorem4-localization | Thm 4 `:437-467` (reduction to the deepest singular point, method of Aoyagi 2013) | — |
| rr4-precedent | the `(3,3,4)` coupled-binding RRR core `:623-630` (Aoyagi–Watanabe 2005 RRR anchor); Thm 1 RRR `:224-242` | — (OUTER-plumbing only; inner SchurCore non-generalising) |

## Endgame + R1–R6 banked-family anchors

| family | paper anchor | deviation / note |
|---|---|---|
| LEDGER carrier (ConState/RootLedger/stepUpdate, EngineConstruction) | the `(S,J)` inductive invariant + `diag(b)` `:475-490`; the three step-cases `:499-520` | T-C (case-2 running-min), p.15-chain (SameLevelChainInv) |
| CHART-EMISSION carrier (QNodeCarrier: `dCenterOfNode`/`qNodeOf`) | the blow-up center = residual-block codim `(M(S)−J)(M^{(S+1)}−J)` `:516`; the regular `Q,P` gauge `:509,:518` (α ≈ the incidence gauge realizing `Q,P`) | — |
| DivBirth reachability (DivBirthReach) | exceptional coords `u_{s,k}` are DISTINCT per divisor `:483-484,:492` → divCoord/resCoord injective + disjoint | — |
| GEO-ATLAS (GeoChart/`geoAtlas`) | "the full chart-by-chart matrix transforms" `:470-473`; chart splits `:504` | the ledger/atlas SPLIT is a formalisation refinement of the paper's single-tree presentation — FAITHFUL (the ledger tree is the symmetric quotient of the geometric fan-out; the atlas is the full fan-out). Anchored-with-note, not a stray. |
| FOLD-JACOBIAN spine (GeoJacobianSpec/Fold, GeoLeafJacobian) | **`worked.tex:492-497` EXACTLY** — `∏_{s,k}u_{s,k}^{M_{s,k}−1}`, Jacobian power `M−1` per exceptional divisor | instance-#9 (full-ledger reading — a CORRECTION toward the paper) |
| region_glue / per-leaf read (RegionGlueAssembly/PerLeaf) | the boxed S2 monomial rule `:495-497` (`k_j≡1`, `h_j=M−1`, ratio `M/2`); normal-crossing `∑b_i²` `:489-490` | the Mathlib AREA FORMULA is the Lean realization of the S2 rule (fork-8); measure-theory clauses = scaffold (below) |
| R1 minAdm / Def-3 (Foundations.Lambda, RouteMLayerSplit) | Def 3 `:245-274` + F-1 fix `:848-857` (`Mval_min`, `t_L=0`) | T-D/F-1 |
| R4 genDivExp propagation | Case-1(1) exponent-merge `M'=M+J_1(M^{(S+1)}−J)` `:505-507`; support field `:645` | — |
| R6 regular-peel (Thm 3 / Lemma 2) | Thm 3 `:363-426` (peel the regular part) + Lemma 2 `:340-360` (block elimination) | — |
| CoRank2Spike (superseded) | the `(3,3,4)` coupled-binding witness `:623-630` | superseded-to-cordon ([[wiring-endgame]] §1a-bis); paper-anchored regardless |

## Measure-theory SCAFFOLD (anchored-as-scaffold, NOT math strays)

*These carry NO direct paper object — the paper uses the boxed S2 monomial-ratio rule (`:495-497`)
directly, never Lebesgue/area-formula bookkeeping. They are the Lean/Mathlib scaffolding that REALIZES
the paper's monomial integral, and are named as such (not passed off as Aoyagi objects):*
- `srcBox = paramsEquivFlat ⁻¹' cubeBox` + `MeasurableSet`/bounded (PivotLeafClauses) — the integration
  domain; anchors to the LOCAL integral near the deepest singular point (Thm 4 `:437-467`).
- the a.e.-`InjOn` null-set clause (PivotInjOn) — faithful to the blow-up (a blow-up chart IS
  non-injective on the exceptional fibre `:504,:512`); the null set = the exceptional fibre.
- the full-pivot-family / `corner_chart_not_cover` (hbij) — the paper's blow-up covers via ALL charts of
  the split `:504`; fewer than the full family leaves a corner gap.
- Haar on `Params M` / the scaling bridge (RegionGlue*) — Mathlib measure transport; no paper object.

## Anchor-pass finding — UNANCHORED FLAGS

**NONE genuine.** Every banked family + landmark anchors to a `worked.tex` site (table above); every
deviation is a documented typo-fix or the instance-#9 correction (registry). The steer's own worked
example — the analytic-only (t̃=0) Jacobian, "instance #9" — is ALREADY corrected in the tree (the
three-ledger split reads the FULL ledger, `:492-494`), so it is no longer a live stray. The
measure-theory clauses are honest scaffold (marked), not silent Lean-convenience math. The one item to
WATCH (not a flag, a note): the ledger/atlas SPLIT (GeoChart) is a formalisation structuring absent from
the paper's single-tree presentation — it is faithful (fan-out quotient) but is the kind of structure the
steer says to re-derive from the math if a ruling ever leads with "zero ripple / unblocks the build"
rather than the fan-out-quotient ground.

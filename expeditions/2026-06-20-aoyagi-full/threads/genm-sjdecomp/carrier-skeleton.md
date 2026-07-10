# Carrier skeleton — Aoyagi §5 `(S,J)` determinantal-locus resolution, decomposed into bankable bricks

> **⚠ LIVE-TREE CORRECTIONS (vsrecon 2026-07-10, verified vs `expedition/aoyagi-full` LIVE — supersede any conflicting "banked" ref below).** For the authoritative banked-vs-fresh map read `../genm-vsrecon/recon-map.md`. Three refs used as "banked" below are stale/absent: (1) `normalSlice_transfer` is NOT on canonical (on `genm-threadedshear` w/ 3 sorries) — the "#109 math-complete" is the CERT, not Lean; (2) `remaining_lt_of_support_ssubset` (the §5.2/5.3 "banked kernel") does NOT exist in Lean (design-note only) — the real termination carrier is `routeMBoxThresholdFinite_of_step` (RouteMSJResolution:863, arity induction); (3) `gammaPeelFromRedChain` is a conceptual name, no Lean def. Also §8-i's dyadic-shell framing is DROPPED (pivchg — see the §8-i annotation). The corner brick + both leaves + the descent ℕ-arithmetic ARE banked/landed on canonical (see recon-map (a)).

**Seat:** scout (design pass, `genm-sjdecomp`). **Charge:** produce the statements-first brick DAG
for the COMMITTED build of Aoyagi §5's `(S,J)` resolution — the atom that discharges `(□)` and mints
the unconditional `aoyagi_learning_coefficient`. **NO Lean written; design + recon + one decorrelated
Codex.** Verified against the LIVE tree (branch `genm-inj-injon`), not the log. All `file:line`
citations checked. This supersedes nothing banked; it is the commissioning map for task #111's
`DeeperStrataResolution` heart.

---

## 0. What is already banked and OFF this build (do not re-commission)

Aoyagi §5 has four steps (ledger UPDATE-605/606). **Steps 1–2 are banked and wired into
`aoyagi_learning_coefficient_gen`; only Steps 3–4 (the recursive blow-up + read-off) are the atom.**

| Aoyagi step | statement | Lean | status |
|---|---|---|---|
| (1) Lemma 2 — block elimination `Q₁AQ₂ = diag(A₁,C₄)` | Gaussian/Schur normal form | `block_elimination` `Skeleton.lean:242` | **BANKED** (explicit normal form, non-vacuous) |
| (1) Thm 3 — regular+core peel `P₁(∏A)P₂ = diag(C₁,∏C)` | product simultaneously block-diagonalised | `rlct_additive_smooth_block` `Skeleton.lean:198` (the `Σxᵢ²` regular block, RLCT `n/2`) | **BANKED**; delivers the `[−r²+r(H⁰+Hᴸ⁺¹)]/2` shift |
| (2) Thm 4 — deepest-point comparison `rlct₀ ≤ rlct_v` | homogeneity ray-domination | `deepest_le_of_homogeneous_core` `DeepestMinRlct.lean:157` | **BANKED** (= `rlctAtOn_lsc_at_origin`) |
| (3) recursive monomial blow-up | `(S,J)` double induction | `SJDecoration`/`SJLinGenState` carrier + `DecoratedPeelStep` | **THE ATOM** ↓ |
| (4) read RLCT off exponents | `monomial_rlct` + Lemma 3 arith | `monomialIntegrand_integrable_of_lt` `Case222Cover:59`, `Mval`/`minAdm`/`Adm` `Lambda.lean:41` | **BANKED endpoint + value formula** |

Steps 1–2 reduce the full DLN loss to the **core-at-origin problem**: compute
`rlctAtOn (‖∏_{s=1}^L C^{(s)}‖²) 0`, where `C^{(s)}` is a **free** `M^{(s)}×M^{(s+1)}` matrix,
`M^{(s)} = H^{(s)} − r`. The RLCT-UPPER direction of that (finiteness = `rlct ≥ ½·minAdm`) IS `(□) =
RouteMBoxThresholdFinite M` (`RouteMBoxReduction.lean:165`). **The atom = Steps 3–4 on the core.**

The reader-facing level discipline (precision.md): the build delivers **box-finiteness / codim =
`minAdm`** (the `rlct ≥ ½·minAdm` leg). The matching `rlct ≤ ½·codim` is the separately-**cited**
Watanabe/Aoyagi interface (`RlctInterface.cited_aoyagi_dln`). The caveat stays beside the claim.

---

## 1. The exact atom contract — what discharges `(□)`

**Live gap tree (task #111, verified against tree):**

```
(□)  = RouteMBoxThresholdFinite M          [∀ nondegenerate M ; RouteMBoxReduction:165]
  ⇐ DecoratedPeelStep                       [T0 driver, BANKED: routeMBoxThresholdFinite_of_decoratedPeel, RouteMSJDecoratedRec:99]
      ⇐ (one decorated peel at binding cut u★, descend to redChain u★ M, one-shorter IH)
          ⇐ gammaPeelFromRedChain           [per-(t,ρ,κ)-chart finiteness = sjJointResolution:803]
               = pivot-Schur split (charge tq)          [BANKED frobSq_schur_block_split, RouteMSJChartAlgebra:107]
               + good stratum {rank Q_b = b}            [Cat I, task #113, Regime-A]
               + top stratum {rank Q_b = b−1} leaf      [3-width base, CERTIFIED — crnrt Q1 exact + MC]
               + DeeperStrataResolution {rank Q_b ≤ b−2} [★ THE HEART — Aoyagi §5 product-rank-flag]
```

**Two equivalent driver Props, both BANKED sorry-free above their single leaf.** Commission against
whichever the controller fixes; do not build both leaves.

- **`DecoratedPeelStep`** (`RouteMSJDecoratedRec.lean:78`) — `∀ M (≥3 wide), (∀ one-shorter M',
  RouteMBoxThresholdFinite M') → DecoratedBoxThresholdFinite (SJDecoration.trivial M)`. Driver
  `routeMBoxThresholdFinite_of_decoratedPeel` closes `(□)` sorry-free modulo it (arity strong induction
  `routeMBoxThresholdFinite_of_step` + `L=1` Morse base `sjBase1_freeMatrix`, both banked).
- **`sjJointResolution`** (`RouteMSJResolution.lean:803`, the sole open sorry of the `RouteMSJ*` family)
  — same content phrased per-chart; `sjResolutionStep_proof` composes it with the **closed**
  `sjBoundaryPeel:688`. `gammaPeelIntegral_lt_top_of_decoratedPeel` (`RouteMSJDecoratedRec:111`) shows
  `803` is retro-fillable from `DecoratedPeelStep` via `sjJointResolution_of_boxThresholdFinite`.

**The atom's precise scope — a Level-A (integrability) obligation, NOT the Level-B value (see §1.5):**
on the deeper strata `{rank Q_b ≤ b−2}` where `Q_b = Y·A_{≥2}` is a **product**-determinantal variety,
the per-chart integral `∫ frobSq(Γ·Q_b)^{−c'} < ⊤` for all `c' < ½·minAdm(M)` (genuine finiteness =
`rlct ≥ ½·minAdm`). This is `(□)`. The stronger reading "RLCT equals `½·codim`, not below" is Level B
(§1.5) and rides on the cited Watanabe/Aoyagi upper bound — the build does NOT need it for the payoff.

**The descent that discharges this is PROVEN (subred `verdict.md`, task-#111 interface (ii); exact
witnesses `(1,1,2)`/`(2,2,3)` + a Gaussian/Bartlett proof, decorrelated Codex).** The Γ-integral after
the Schur split produces the corank-Gram weight `∫ det(Q_bQ_bᵀ)^{−a/2} d(Y,A_{≥2})`, and this **IS the
corank-Gram integral of the SHORTER chain `(b, M₂,…,M_last)`** — a chain-length `L → L−1` descent:
- reduces via the Jacobian `J(A_{≥2}) = det⁺(Gram A_{≥2})^{−b/2}` (SVD-exact; **a genuine det-inverse**,
  unbounded on `{rank A_{≥2} < min(M₂,q)}` — NOT a unit);
- net **integrability threshold `a < min(M₂,…,M_last) − b + 1`** — the MIN TAIL WIDTH, **strictly below**
  the free-`Q` value `q−b+1` when the tail contracts (`M₂<M_last`). This IS the twist / product-lowering,
  one chain-length up from crnrt's `min(a,m,D)`.
- **the clean `[free-Q core]∘[loss IH]` factorization is INVALID** (the free-core's `Q`-domain shrinks
  with `A_{≥2}` and cancels `J`'s blow-up; wrong already at `a=0`). Do NOT wire it that way.
- **Lean wiring (subred prescribes):** a **dominant-minor COVER of `A_{≥2}`** — on-chart `J` is a unit
  and the free-core sits over the rank-`min(M₂,q)` image (threshold `min(M₂,q)−b+1`) — plus the deeper
  corank-Gram recursion off-chart. **Termination = chain-length strictly decreasing**, which matches the
  banked `(S,J)` kernel's support-strict-subset (`remaining_lt_of_support_ssubset`).

subred also **sharpens/corrects `wtint`** (and hence brick B3): the good-stratum codim is
`min(M₂,…,M_last)−b+1`, NOT `q−b+1`; the Cat-I boundary is `a+b ≤ min(tail)`, NOT `a+b ≤ M_last`. A
formaliser routing interface (ii) through the free-`Q` core at `a<q−b+1` **over-estimates the budget on
every contracting-tail chart** — and permutation-invariance means the widths can be in any order, so
contracting tails DO occur at binding cuts: **the twist is load-bearing, not a rare edge.**

This supersedes the earlier "elementary twist + arity-IH fails" framing: the twist is not a wall, it is
the *correct lowered per-chart threshold*, and subred supplies the proven descent that carries it.
`normalSlice_transfer` (task #109) is the complementary RANK-identity + additive-charge view
(`{rank P ≤ q} ≅ Σ⁰(M₁−q,…)`), unit-Jacobian at the RANK layer but carrying the same pivot-charge
det-inverse at the loss layer (§8-i); the two certs agree on the descent — subred pins the integrability
threshold, normalSlice pins the charge bookkeeping.

## 1.5 TWO LEVELS — keep them as separate brick classes (controller discipline)

The build has two strictly-separated statement levels; **name every brick for exactly the level it
proves, and never let a Level-A brick masquerade as Level-B** (the `x⁴+y⁶` trap: codim 2 but RLCT
`5/12` — a finiteness threshold is NOT the RLCT value).

- **Level A — INTEGRABILITY (`∫ < ⊤`).** The corank-Gram weight is finite for `a < min(tail)−b+1`, via
  the dominant-minor cover + `J = det⁺(Gram)^{−b/2}` + chain-length descent (subred, PROVEN). Composed
  across the recursion + the terminal, this is `RouteMBoxThresholdFinite` = `(□)` = `rlct ≥ ½·minAdm`.
  **This is the entire committed build.** Genuine finiteness (Gaussian/Bartlett exact), not a codim
  proxy. These bricks feed `(□)`.
- **Level B — RLCT VALUE (`= ½·codim`, "lands AT, not below").** The exact-value reading: the resolution
  is normal-crossing and the exponent read-off gives *exactly* `½·minAdm` (Aoyagi Step 3/4, `Mval` +
  Lemma 3 = `monomial_rlct`). STRICTLY STRONGER than Level A. **Not needed for the payoff** — the
  matching `rlct ≤ ½·codim` is the CITED Watanabe/Aoyagi interface (`RlctInterface.cited_aoyagi_dln`),
  so `rlct = ½·minAdm` follows from Level A (finiteness) + the cited upper bound + `codim = minAdm`
  (banked). Level B is a separate, optional resolution layer.

Consequence for the DAG: the descent/finiteness bricks (subred, corank atoms, corner blow-up, terminal
endpoint) are **Level A** and each proves an honest `< ⊤`. The `Mval`/`minAdm`/`monomialThreshold`
read-off is where a **Level-B** value claim would live — commission it separately and only if the
operator wants the RLCT half axiom-free (dropping the cited upper bound).

---

## 2. The `SJLinGenState` carrier IS Aoyagi's `⟨diag(b)·[E_J|D_J]·∏C⟩` invariant, in Lean

The build's core data structure is banked and faithful. Aoyagi's inductive invariant (p.15)

```
⟨∏_{s=1}^L C^{(s)}⟩ = ⟨ diag(b₁,…,b_{M(S)}) · [E_J O ; O D_J] · ∏_{s=S+1}^L C^{(s)} ⟩
```

maps term-for-term onto `SJLinGenState ζ ν ι d` (`RouteMSJLinGen.lean:100`) + `SJDecoration`
(`RouteMSJDecorated.lean:89`):

| Aoyagi object | Lean field / op | file:line |
|---|---|---|
| the monomials `bᵢ = ∏_{t̃=i−1} u_{s,k} · b_{i−1}` | `supp : SJSupport ι d` (per-generator exceptional-divisor support) | `RouteMSJLinGen:102` |
| the free residual entries `d_{ij}` | `coeff : ζ → ι → ν → ℝ` (linear residual `residual`) | `:104`, `:112` |
| the still-free tail `∏_{s>S} C^{(s)}` | `Z`, `ctx : Z → ζ × (ν→ℝ)`, `dom` | `RouteMSJDecorated:107–113` |
| accumulated Jacobian `∏ u^{M_{s,k}−1}` | `jac : Fin d → ℕ` | `:105` |
| the loss `‖…‖² = ∑ bᵢ²` | `loss = ∑ᵢ genᵢ²`, `gen = genMonomial·residual` | `RouteMSJLinGen:120`, `:116` |
| **base state** (S=0, J=0, π=∅) | `SJDecoration.trivial` = `ofMatrix` at product entries | `RouteMSJDecorated:157`, `RouteMSJLinGen:138` |
| **Case-2 blow-up** (whole-block radial `u₀` shared by all) | `radialAttach`/`radialStep` (`loss ↦ u₀²·loss`) | `RouteMSJDecorated:242`, `RouteMSJLinGen:176`,`:192` |
| **Case-1 block elimination** (Lemma 2 unit row-mix) | `rowMix` (`loss_rowMix`, faithful at fresh block `gen_rowMix_const`) | `RouteMSJLinGen:204`,`:251` |
| **Case-1 `[E_J | D_J]` block structure** (pivot ⊕ corank) | `loss_blockSplit` (`∑pivot² + ∑corank²`) | `RouteMSJLinGen:290` |
| the value `M_{s,k}` (p.22) | `Mval M T` = `∑ⱼ (t^{j−1}−t^{j})(M^{j+1}−t^{j})` | `Lambda.lean:41` |
| the admissible cone / `minAdm` | `Adm`, `minAdm`, `minAdmRec` (layer-peel descent) | `Lambda:62`, `RouteMLayerSplit:51`,`:58` |
| **terminal** (S=L+1, pure monomial) read-off | `monomialIntegrand_integrable_of_lt`, `terminal_monomial_mul_unit_lintegral_lt_top` | `Case222Cover:59`, `RouteMSJTerminal:160` |

**Consequence for commissioning:** the atom is NOT a from-scratch structure build. The carrier,
the base state, the two blow-up ops (radial / row-mix), the block-split shape, the value formula, and
the monomial endpoint are all banked. **The missing content is (i) the recursion that composes these
into the invariant across `(S,J)`, and (ii) the per-chart analytic finiteness on the deeper strata.**
The `SJState`/`sjRunMin` (`RouteMSJResolution:752`,`761`) are explicitly stubs for the full carrier;
`sjRunMin_antitone` is the only dimensional fact proved on them.

---

## 3. The `L=2` base case — the COMPLETED from-scratch template (`Case222*`)

The operator's feasibility proof: **`Case222Resolution.lean` resolves `f = ‖A₀A₁A₂‖²` for
`(2,2,2)` end-to-end via exactly this construction**, and `Case222Rlct.lean:30` reads off
`rlctAtOn (dlnLoss H222 0) deepest222 = 3/2 = ½·minAdm(2,2,2)`. The pipeline (the LIFT bricks
generalize each node):

```
myF222  →[step1A = pivotBlowupOn {0,1,2,3} 0, |det|=x₀³]  step1Residual
        →[= resolvedForm]                                 (Schur residual, unit-cleared)
        →[step2E = pivotBlowupOn {1,2,3} 1, |det|=z₁²]     resolvedForm
        →[step2D]                                          blockForm
        →[phiUnit]                                         myF222_phiUnit_monomial = u₀²·z₁²·(unit)
        → monomial endpoint (unitK8=(1,0,1,…), unitH8=(3,0,2,…)); threshold ≤ 3/2 = binding axis (k,h)=(1,2)
```

Concrete facts that anchor the general shape: `pivotBlowupOn_hasFDerivWithinAt`,
`pivotBlowupOn_injOn`, `pivotBlowupOnDeriv_det = pivot^{card−1}` (`Case222Resolution:257`,`259`,`275`);
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` is the CoV engine. **Every BASE brick below is
"generalize a `Case222*` node to opaque widths".**

---

## 4. THE BRICK DAG

Notation: **[B]** = BASE (generalize the `Case222`/vslice `L=2`/`(3,3,3,4)` instance to opaque
widths); **[L]** = the `(S,J)` LIFT (the recursion / general-arity glue). Sizes are order-of-magnitude
(S=small ≤½ day, M=medium 1–2 days, L=large / genuine module). Each brick lists its `consumes`.

### Tier 0 — DRIVER (BANKED — commission nothing; listed for the DAG root)

- **D0. `routeMBoxThresholdFinite_of_decoratedPeel`** — `DecoratedPeelStep → (□)`. **BANKED**
  (`RouteMSJDecoratedRec:99`). Root. Consumes `routeMBoxThresholdFinite_of_step`, `sjBase1_freeMatrix`.

### Tier 1 — the pivot-Schur chart reduction (mostly banked; ONE opaque-width lift)

- **B1. front-split + pivot-chart cover.** `∫ frobSq(A₀·Q)^{−c'} = ∑_{t,ρ,κ} gammaPeelIntegral`.
  **BANKED** (`routeMLayerBoxIntegral_front_split:461`, `sjBoundaryPeel:688`, `pivotLocus_eq_iUnion`).
  *(The `sjBoundaryPeel` block-reindex plumbing is closed.)*
- **B2. Schur block split on a `t`-pivot chart** — `frobSq(A₀Q) = ‖a·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²`,
  `Γ = D − Ca⁻¹B` the Schur complement, `a⁻¹` living ONLY in `det-1` shears (COMPASS). **BANKED EXACT**
  at the `L=2` single-matrix level (`frobSq_schur_block_split` `RouteMSJChartAlgebra:107`;
  `measurePreserving_shearSub` `RouteMSJPivotChart:337`). Size **M [L]**: the opaque-width block algebra
  `M_i X_i M_{i+1}⁻¹ = [[α_i,B_i],[0,Y_i]]` (the threaded normal form, §2 of `normalslice-cert`).
  Consumes B1.
  - ⚠ **pivot-charge — CORRECTED by pivchg (2026-07-10, task #115): the dyadic-shell / Anderson framing
    below is WRONG — DROP it.** The `|det α|^{−m₀}` det-inverse is real, but spending it via disjoint dyadic
    `|det α|`-shells DIVERGES as a BOUND (`term_k≍2^{k(m₀−1)}`; `∫|det α|^{−s}<∞ ⟺ s<1`, and charge×rest
    does NOT factorize). The finiteness is instead delivered by the **banked FRONT-FIRST box-bound**
    (covdesign §CONCESSION): the box keeps the collapsing direction O(1), so the effective charge is
    **`α=max{0,2c'−m₀(q−1)}`, NOT m₀**, landing EXACTLY at ½·minAdm (linchpin `minAdm ≤ D+m₀(q−1)`, tight
    0/120). **B5a/B2 owe NO shell/Anderson lemma — the charge dissolves into the banked box-bound.** The one
    remaining open is the PRODUCT-tail rank codim D (`codim{rank(A₁···A_{L−1})≤q−1}`, non-Lebesgue measure
    on P) — pivchg computing it. See `genm-pivchg/verdict.md` + synthesis UPDATE-857.
    ~~(superseded) …spend it via disjoint dyadic `|det α|`-shells (or Anderson)…~~ Size **M [B]**. Consumes B2.

### Tier 2 — the three rank(Q_b) strata (the per-chart resolution). All **Level A** (`< ⊤`).

- **B3. good stratum `{rank Q_b = b}` (Regime-A wiring).** Cat I, **task #113 IN PROGRESS**
  (`genm-r1rankcharge`/Gram-Schur radial). ⚠ **threshold CORRECTED by subred:** the good-stratum codim
  is `min(M₂,…,M_last)−b+1`, NOT `q−b+1`; the Cat-I boundary is `a+b ≤ min(tail)`, NOT `a+b ≤ M_last`.
  Routing through the free-`Q` core at `a<q−b+1` OVER-ESTIMATES on contracting-tail charts. Consumes B2,
  `matBox_corank_residual_le` (`RouteMSJCorankResidual:114`), `det(MMᵀ)≥minor²` (task #112 CLOSED). Size
  **M [B]** (in flight). **Level A.**
- **B4. top stratum `{rank Q_b = b−1}` free-bilinear leaf.** `(a,1,D)` leaf, threshold `½·min(a,D)` by
  factoring `∫‖γ‖^{−2s}∫‖z‖^{−2s}`, coupling `C'B₀` removed by comparability, direct-sum with redChain.
  **CERTIFIED** (crnrt Q4 exact + MC; cornrev Q1). Size **S [B]**. Consumes B2, `sumSqND_box_lt_top`
  (`S1RadialMorse:67`), `radial_morse_dominates_lt_top:127`. **`b=1` charts fall ENTIRELY here** (single
  stratum) — first buildable milestone. **Level A.**
- **★ B5. `DeeperStrataResolution {rank Q_b ≤ b−2}` — THE HEART.** For `b≥2`, the corank-Gram integral
  over the deeper stratum is finite up to `½·minAdm(M)`, via subred's PROVEN chain-length descent.
  Decomposes into B5-desc … B5d below. Size **L**. **Level A.**

### Tier 3 — decomposition of B5 (the deeper-strata resolution). All **Level A** unless flagged.

- **★ B5-desc. subred's descent primitive (the PROVEN load-bearing step).** The corank-Gram integral
  `∫ det(Q_bQ_bᵀ)^{−a/2} d(Y,A_{≥2})` (`Q_b = Y·A_{≥2}`) reduces to the corank-Gram integral of the
  **SHORTER chain `(b, M₂,…,M_last)`** via `J(A_{≥2}) = det⁺(Gram A_{≥2})^{−b/2}`, on a **dominant-minor
  cover of `A_{≥2}`** (on-chart `J` = unit, free-core over the rank-`min(M₂,q)` image; deeper recursion
  off-chart). **Integrability threshold `a < min(M₂,…,M_last) − b + 1`** (PROVEN — Gaussian/Bartlett +
  exact `(1,1,2)`/`(2,2,3)`, subred). Descent = chain-length `L→L−1`; termination via the banked kernel
  `remaining_lt_of_support_ssubset` (support strict subset). **Do NOT wire as `[free-Q core]∘[loss IH]`
  (invalid factorization).** Size **L [L]**. Consumes B2, the dominant-minor cover machinery
  (`pivotLocus_eq_iUnion`, `isUnit_submatrix_le_rank`), the corank atoms
  (`matBox_corank_residual_le`), the `(S,J)` termination kernel. **Level A.** ← the recursion's
  spine; commission with a **contracting-tail chart** (`M₂<M_last`, e.g. tail `(1,2)` ⟹ `(b,1,2)`) so
  the twist is exercised, not a balanced case that hides it.
  - **B5-desc-ℕ. the min-tail-width threshold ℕ-lemma.** `min(M₂,…,M_last)−b+1` composed across the
    descent equals the layer-peel `minAdm` recursion (`minAdmRec`). New ℕ-lemma; the analogue of
    `minAdm_eq_frontPeel`/`minAdmRec_eq_minAdm` at the corank-Gram level. Size **S [B]**. **Level A.**
- **B5a. `normalSlice_transfer` — the complementary RANK-identity + additive-charge view.** `{rank P ≤
  q} ≅ Σ⁰(M₁−q,…,M_L−q)` via a threaded shear (`M_i X_i M_{i+1}⁻¹` block-upper-tri, `rank P = q +
  rank(reduced product)`) — **unit-Jacobian at the RANK layer** (`rank_eq_q_add_of_normalForm`, the
  landed `blockShear_step`). **Math COMPLETE, task #109** (`normalslice-cert.md`, exact `L≤4`). Used for
  the CHARGE bookkeeping (which widths reduce, additive composition), NOT the loss finiteness (that is
  B5-desc). Size **M [L]**. Consumes B2, `pivotLocus_eq_iUnion`, `measurePreserving_shearSub`,
  `mul_three_reassoc`. **Level A (rank identity).**
  - **B5a′.** The opaque-width block-shear identity `M_i X_i M_{i+1}⁻¹ = [[α_i,B_i],[0,Y_i]]`, threading
    `α_i = A_i + B_i K_{i+1}`. Size **M [L]** (`L=2` = B2's banked `frobSq_schur_block_split`; lift by
    prefix-length induction reusing `prodAux_succ`). Consumes B2. **← SECOND BUILDABLE NOW.**
- **B5b. additive charge composition ("sum-not-min").** On the normal slice the loss is `‖R‖² + ‖Z‖²`
  (disjoint blocks: `R` dim `M₀q` from `A₀`, `Z` = reduced product), RLCTs ADD:
  `½·M₀q + ½·minAdm(reduced) = ½·frontCharge(q)`, `min_q = ½·minAdm(M)`. **ℕ accounting BANKED**
  (`minAdm_eq_frontPeel` `RouteMFrontPeelCharge:158`; `Mval_decompose`/`sjChargeUpdate_accum:353`;
  `minAdmRec_eq_minAdm`); the **analytic disjoint-sum RLCT-add** is `radial_morse_dominates_lt_top`
  applied to disjoint variable blocks. Size **S [B]**. Consumes B5a.
- **B5c. the CORNER blow-up (toric CoV `u₁ = u₀τ`).** The binding zero is at the CORNER `u₀=u₁=0` (NOT
  a boundary); blow it up, accumulating Jacobian powers ADDITIVELY (`3+2+1=6` for `(3,3,3,4)`) onto one
  terminal divisor while the loss stays order 2 → threshold `(Σqⱼ+1)/2 = ½·Σqⱼ`. **Finiteness leg
  BANKED** (`radial_morse_residual_power_le` `RadialResidualPower:157`, `lintegral_eq_polar`
  `RouteMSJSphereBlowup:82`); the toric-corner CoV composition is **NEW**. Size **M [B]** (target
  exact: `vslice_corner.py`, `∫ u₀^{Mval−1−2c'}du₀ < ⊤ ⇔ c' < ½·Mval`). Consumes B5b + the banked
  radial/sum machinery. **Avoid** `fibre_lintegral_mul_le` + `product_min_rlct` here (they give the
  boundary-wise MIN = the undershoot).
- **B5d. bounded-below unit supply.** The resolved cores `U₀,U₁,U″ = frobSq(row·A₂)` are simultaneously
  `≥ a > 0` a.e. on the generic-downstream chart, uniformly on the compact box. **This is the shape the
  endpoint `terminal_monomial_mul_unit_lintegral_lt_top` consumes as `hunit`.** Supply technique BANKED
  ("nonzero-poly ⟹ >0 a.e.": `Uval4422_ae_pos` `RouteM4422:240`, `achieverUfun_ae_pos`
  `RouteMAchieverVvalPoly:385`, `cleanUfun_ae_pos` `RouteMBoundaryCleanU:328`); residual = the a.e.→
  uniform bridge (continuity+compactness) OR routing the `A₂`-rank-drop locus as a higher-`Mval`
  branch. Size **M [B]**. Consumes B5c. **This is the vslice §8 named gap — bounded chart algebra on a
  proven template, not a wall.**

### Tier 4 — the recursion glue + terminal (the `(S,J)` LIFT)

- **B6. `DecoratedPeelStep` assembly** — compose B2–B5 into ONE decorated peel at the binding cut `u★`,
  landing on `redChain u★ M` at threshold `carrierThreshold M − ½·peelCharge` (banked
  `carrierThreshold_shift` `RouteMSJDecorated:71`), closed by the one-shorter IH. Size **M [L]**.
  Consumes B2,B3,B4,B5, `decoratedBoxThresholdFinite_trivial_iff:217`.
- **B7. terminal monomial read-off (Step 4 / Lemma 3).** At the fully-resolved leaf the loss is
  `(unit)·∏bᵢ²` with Jacobian `∏u^{h}`. **Level A** (feeds `(□)`): finite ⟺ `c' < min_axis (h+1)/2 =
  ½·minAdm`. **BANKED** (`monomialIntegrand_integrable_of_lt` `Case222Cover:59`,
  `terminal_monomial_mul_unit_lintegral_lt_top` `RouteMSJTerminal:160`, base `sjBase1_freeMatrix`).
  Consumes B5d, B6. **Commission nothing for Level A** — verify the Lemma-3 arithmetic (§6) matches.
  **Level B** (separate, optional): the read-off equals `½·minAdm` *exactly* (`monomialThreshold` +
  `Mval` + `minAdmRec_eq_minAdm`) → `rlct = ½·codim`. Build only if the operator drops the cited upper
  bound (§1.5).

### Dependency order (topological) — Level A (integrability, feeds `(□)`)

```
D0 [banked]
 └ B1 [banked] ─ B2 [M,lift] ─┬─ B4 [S,base]  (b=1 charts + top stratum)   ← FIRST BUILDABLE
                              ├─ B3 [M,#113 in flight]  (good stratum; threshold min(tail)−b+1)
                              └─ B5 = B5a′[M] ─ B5-desc[L, PROVEN math] ─ B5b[S] ─ B5c[M] ─ B5d[M]
                                     (B5a normalSlice = charge-accounting side, parallel to B5-desc)
 B6 [M,lift] consumes B2..B5 ;  B7 [banked] verifies read-off
   B5-desc-ℕ [S]  (min-tail-width threshold → minAdm)   feeds B5b/B7
```

**First 1–2 buildable-now bricks:** **B4** (the `b=1` free-bilinear leaf + top stratum — self-contained,
banked corank/Morse inputs, no recursion) and **B5a′** (the opaque-width block-shear identity — pure
linear algebra, `L=2` banked, lift by induction). Both stand on banked pieces; neither waits on B5's
recursion. B3 is in flight (task #113 — flag it the min-tail-width threshold correction). The proven
spine B5-desc (subred) is the third to commission, on a contracting-tail chart.

---

## 5. The `(S,J)` induction measure — explicit + RED-TEAMED

**There are TWO nested recursions; keep them distinct — conflating them is where a hidden gap lives.**

### 5.1 OUTER recursion — arity (Aoyagi's `S` loop), BANKED well-founded

`routeMBoxThresholdFinite_of_step` (`:863`) is **strong induction on chain arity `L`** (# matrices).
Measure = `L : ℕ`, well-ordered. Each `DecoratedPeelStep` peels the leading layer-PAIR to pivot rank
`t` and descends to `redChain t M = (t, M₂,…,M_L)` — **one fewer layer** (`RouteMLayerSplit:40`),
strictly smaller arity. Base `L=1` (`sjBase1_freeMatrix`, Morse) + `L=0` vacuous. **This is banked and
sound** — the descent is manifest (`L → L−1`), `t≥1` not needed for termination (arity drops
regardless). This is Aoyagi's "increase `S`" as an ℕ that is bounded by `L+1`, recast as a strictly
decreasing arity.

### 5.2 INNER recursion — the `(S,J)` block resolution WITHIN one peel (Aoyagi Case 1/Case 2)

This resolves one layer's `M(S)×M^{(S+1)}` block into diagonal monomials. Aoyagi's three branches move
DIFFERENT coordinates, so the measure is **NOT** `(S,J)` (both S and J *increase*). The claimed
descent (`reference-notes-sj-kernel.md`, banked kernel `remaining_lt_of_support_ssubset`):

- **measure = `remaining := #(source labels) − #(introduced labels)`** = `(actualWidthLabelFinset).card
  − support.card`, a strictly-decreasing ℕ as the introduced-support Finset strictly GROWS
  (`Finset.card_lt_card`). Bounded below by 0. This is the honest well-foundedness carrier.

**RED-TEAM (my pass, then Codex xhigh decorrelated — `codex/wellfounded-answer.md`, both-withheld).**
Codex CORROBORATED the Case-1(1) danger and SHARPENED it, and found four more under-specified steps.

**The correct inner measure is a lexicographic TRIPLE (ordinal), NOT `remaining` alone.** Write
`μ_S = min_{r≤S} m_r`, `K_S = min(μ_S, m_{S+1}) = μ_{S+1}`, `N(S,J) = #{u live : t̃(u) > J}` (ALL live
labels above `J`, not just at one slot). Then

```
Φ(S,J,U) = ( L+1−S ,  K_S−J ,  N(S,J) ) ∈ ℕ³      ( = ω²(L+1−S) + ω(K_S−J) + N(S,J) )
```

strictly decreases on every branch:

| branch | component that drops |
|---|---|
| Case 1(1) | `N ↦ N−1` (selected label relabelled `t̃ = J+J₁ ↦ J`, no new `u`) |
| Case 1(2), same `S` | `K_S − J ↦ K_S − J − 1` |
| Case 1(2), layer done / Case 2 macro | `L+1−S` drops |

- **Case 1(1) — the danger, now pinned.** It keeps `(S,J)` fixed and introduces no new `u`, so
  `remaining` (#source − #introduced) does NOT drop. Termination needs (i) an EXPLICIT transition rule
  *"the selected coordinate's label moves DOWN to `J`"* (relabel `t̃: J+J₁ ↦ J`), and (ii) the measure
  must count **all** labels above `J` (`N(S,J)`), NOT the count at the single slot `J+J₁` — because once
  that slot empties, the first nonempty slot moves (Codex Q1/Q2). **My first-pass `slotCount` was
  insufficient; Codex's `N(S,J)` is the fix.** Bounded: `#U ≤ ∑_s K_s ≤ ∑_s m_{s+1}`.
- **The banked kernel `remaining_lt_of_support_ssubset` covers ONLY the support-GROWTH steps** (Case
  1(2)/Case 2, the `L+1−S` / `K_S−J` components). It does **NOT** supply the Case-1(1) `N` component nor
  the "label moves to `J`" rule. → **Measure-level obligation to state at commission.**
- **Empty-residual boundary `J = K_S` — a genuine gap (Codex Q3).** At `J=K_S` the residual block has
  zero rows (`K_S=μ_S`) or zero columns (`K_S=m_{S+1}<μ_S`); NO nontrivial blow-up should occur. Aoyagi's
  prose has no explicit transition here — treating it as Case 2 would blow up an empty ideal. Needs an
  explicit `(S,K_S) → (S+1,0)` step. `J=μ_S` is NOT an ordinary Case-2 state.
- **Base-state indexing defect (Codex Q3).** `μ_0` is undefined, and `D_0 = ∏C^{(s)}` while retaining the
  displayed tail product DUPLICATES the product. Clean start: `S=1, J=0, D_0 = C^{(1)}`, tail
  `C^{(2)}···C^{(L)}` — or declare `S=0` a separate base convention.
- **Case 2 "advances S" is too aggressive (Codex Q5b).** One radial blow-up of the residual produces one
  unit pivot and advances `J` by ONE (`D_J' ~ diag(1, D_{J+1})`); it does NOT resolve the whole block in
  one op. "Case 2 advances `S`" must mean the finite ITERATION of this pivot step until `J=K_S`.
- **Comparability (Codex Q4).** NOT needed for termination — but the Case-1 step must choose the
  coordinate whose label `T` is LEAST among those at the same slot (a finite total order has one; a
  partial order may have several incomparable minima). So comparability is load-bearing for the
  *invariant closedness* + the RLCT read-off, and a lemma "Case-1(1)/(2) updates preserve total
  comparability" is needed. "Choose any `u`" is insufficient.

**Verdict:** the OUTER arity recursion is banked-sound. The INNER native `(S,J)` recursion, taken
literally from Aoyagi's prose, is **repairable but not yet a fully-specified proof** — it needs SIX
additions: the triple measure, the Case-1(1) label-move rule, the `J=K_S` boundary transition, the
`S=1` base convention, the Case-2-iterates clause, and the comparability-preservation lemma.

### 5.3 subred's chain-length descent gives a CLEAN measure — the recommended one

**subred (`verdict.md`) resolves the measure question for the recommended route.** Its descent
(B5-desc) is `chain-length L → L−1` — the corank-Gram integral of `(b, q)` reduces to that of
`(b, M₂,…,M_last)`, one layer shorter. The measure is then just **chain-length `L : ℕ`**, well-ordered,
strictly decreasing per step, and subred verified this **matches the banked `(S,J)` kernel's
support-strict-subset** (`remaining_lt_of_support_ssubset`: introducing the layer's exceptional
coordinates strictly grows the support, `Finset.card_lt_card`). So the recommended route's termination
is banked-supported with NO Case-1(1) complication: **the whole `ω²/ω`-triple concern of §5.2 arises
ONLY if one builds Aoyagi's literal inner Case-1/Case-2 loop; subred's descent (and `normalSlice_transfer`)
descend by chain-length instead, and the six repairs all evaporate** (the measure collapses to arity/
chain-length `L`, banked). This is the decisive argument against the literal native-inner-loop route and
for the subred/normalSlice descent — see §8–9.

---

## 6. Chart census — the centers the blow-up produces

Aoyagi's centers are the named submanifolds `{d_ij=0, u_{s,k}=0}` (Case 1) and `{d_ij=0}` (Case 2).
Per one layer-peel, on the rank-`t` pivot chart, the corank block `Q_b` (`(M₁−t)×(deeper)`) stratifies:

| stratum | condition | count (per crnrt census, `L=3..5`) | binding? | brick |
|---|---|---|---|---|
| good | `rank Q_b = b` (`b=M₁−t`) | full-rank slice | Regime-A, non-binding above `½·minAdm(tail)` | B3 (#113) |
| top | `rank Q_b = b−1` | drop-by-one | closes elementarily (charge `a(b−1)+D`) | B4 |
| deeper | `rank Q_b ≤ b−2` (`b≥2`) | **252/294 (86%)** of corner charts | **BINDING** — the atom | B5 |
| Cat III | `b>q` (all-degenerate) | **0 nontrivial** (`a=0` at every binding cut) | trivial peel, no corner | — |

Within B5, the deeper stratum recurses (via B5a) to the reduced chain `(M₁−q,…,M_L−q)` — the same
census applies one arity down. **Binding centers:** the corner `u₀=u₁=0` (B5c), where per-boundary
charges ADD. **Non-binding (checked):** the pivot/α-divisor (threshold `≥ ½·Mval(0,…) ≥ ½·minAdm`),
Cat III (empty Γ), the good stratum (codim `≥ minAdm(tail)`). Case-2 branches are non-binding for the
equal-prefix-width slices (`2λ ≤ M^{(i)}M^{(j)}`, coarse bound suffices, vslice §10) but the
**prefix-min form must be built for width-general chains** where `M(S) < M^{(s)}` (§7).

---

## 7. Exponent bookkeeping → RLCT read-off + the Case-2 typo absorption

**Step 4 = the terminal monomial read-off.** After full resolution the loss on each chart is
`(unit) · ∏_ℓ |u_ℓ|^{2k_ℓ}` with Jacobian `∏_ℓ |u_ℓ|^{h_ℓ}` (`h_ℓ = M_{s,k}−1`), so
`∫ ∏|u_ℓ|^{h_ℓ − 2c'k_ℓ} · unit^{−c'} < ⊤ ⟺ c' < min_ℓ (h_ℓ+1)/(2k_ℓ) = ½·min_ℓ M_{s,k}`
(coordinatewise, `Case222Cover`/`monomialIntegrand_integrable_of_lt`). The min over charts/branches is
`½·minAdm` — Aoyagi's Lemma 3 arithmetic min `min{A(b) : b} = a·ℓ·(ℓ−a)` gives the closed value; in Lean
this is `minAdm = ((Adm M).inf' Mval).toNat` with `minAdmRec_eq_minAdm` the layer-peel recursion, and
`Mval` (`Lambda:41`) = Aoyagi's `M_{s,k}`. **Verify (B7): the per-axis `(h+1)/2k` read-off = `½·Mval`
on the introduced labels** — the one place the exponent bookkeeping must be checked against Lemma 3, not
assumed.

**The Case-2 typo (documented, `brief.md:119`, `lessons.md:9`).** Aoyagi's Case-2 divisor exponent
prints `M'_{S,J+1} = (M(S)−J)(M^{(S+1)}−J)` in **actual** widths, but the faithful form is the
**prefix-min** `(μ_S − J)(M^{(S+1)}−J)` with `μ_S = min{M^{(s)}:s≤S}` a running minimum. **Absorption
(three-fold, all confirmed):**
1. **Value unaffected:** the discrepancy `(M(S)−μ_S)(M^{(S+1)}−J)` is a non-negative slack; the Case-2
   branch **never attains the min** (trusted-spine slack `2λ ≤ M^{(i)}M^{(j)}`, vslice §10), so a
   **coarse bound suffices** and the typo does not change `minAdm`.
2. **Equal-prefix slices** (`(3,3,3,4)`: `M(1)=M(2)=M(3)=3`): prefix-min = actual-width, the forms
   **coincide** — the typo does not bite where the base modules live.
3. **Width-general grind:** the forms diverge exactly when `m_S > μ_S` (`q_actual − q_prefix =
   (m_S−μ_S)(m_{S+1}−J)`). **Codex Q6 SHARPENED this: it includes MONOTONE-INCREASING chains, not just
   globally non-monotone ones** — any chain where an earlier layer was a strict bottleneck and the width
   has since risen. Example `(2,4,4)`, `S=2, J=0`: `16` (actual) vs `8` (prefix). **build the prefix-min
   form regardless** and land the named-deviation fidelity card there (task #107 CLOSED — "Case 2:
   prefix-min form + printed-paper fidelity card"). Do NOT silently use actual widths.

Codex Q6 scope (decorrelated, confirms + sharpens): (i) termination **unaffected** (the exponent is not
in the measure); (ii) normal-crossing monomialization **unaffected** — *provided the coordinate map
really blows up the effective `μ_S`-row block*; (iii) the RLCT is **affected** — actual-width
**overcounts**, and "harmlessness for the final RLCT requires a separate proof that these Case-2 divisors
never minimize" (= the vslice §10 trusted-spine slack; carry it, don't assume it). ⚠ **A stronger
warning:** if the actual-width expression is meant LITERALLY as the blow-up center's dimension (not just
a bookkeeping formula), it references rows ABSENT after the bottleneck, so *the coordinate construction
itself is undefined* — the prefix-min `(μ_S−J)` form is the only well-defined center. This is precisely
why B5a/`normalSlice_transfer` (which reduces to the `μ`-reduced chain directly) sidesteps the whole
issue.

---

## 8. Genuinely-missing-math check (bar HIGH) — hard labour vs a certificate need

Per cornrev's equivalence certificate, the remaining content is **established** (corner-mildness ⟺ the
main DLN RLCT theorem; no strictly-easier sub-problem). So the default is **hard labour on a proven
template**, and "genuinely missing" means "needs a decorrelated certificate we do not have." Classified:

**HARD LABOUR (established; the default — commission as build-tides):**
- B5-desc subred's corank-Gram chain-length descent (**math PROVEN** — Gaussian/Bartlett + exact
  witnesses; Lean = the dominant-minor cover + `J=det⁺(Gram)^{−b/2}` on-chart-unit + the recursion).
- B5a `normalSlice_transfer` at opaque widths (math-complete, task #109; Lean = block-matrix algebra +
  MP + prefix-length induction).
- B5c the toric-corner CoV (finiteness banked; the CoV composition is standard blow-up chart algebra;
  `vslice_corner.py` is the exact target).
- B5d bounded-below unit supply (technique banked; residual = a.e.→uniform bridge, elementary).
- B2 opaque-width Schur block algebra; B4 top-stratum leaf (certified).
- B5-desc-ℕ min-tail-width threshold → `minAdm` (new ℕ-lemma, analogue of `minAdm_eq_frontPeel`).

**NAMED ANALYTIC / STRUCTURAL OBLIGATIONS (real, not yet a banked lemma — surface, don't launder):**
- **(i) The det-inverse Jacobian — a genuine det-weight, but PROVEN handled by the dominant-minor
  cover.** Two faces of one fact: (normalslice-cert) cleaning the loss to `‖R‖²` needs `|det α|^{−m₀}`;
  (subred) the corank-Gram descent Jacobian is `J = det⁺(Gram A_{≥2})^{−b/2}`, unbounded on `{rank A_{≥2}
  < min(M₂,q)}`. So the no-det-inverse "compass" genuinely fails at the LOSS/descent layer (it holds at
  the RANK layer). **subred PROVES the mechanism that spends it:** on the **dominant-minor cover** of
  `A_{≥2}`, `J` is a unit on-chart and the free-core's shrinking image exactly cancels the off-chart
  blow-up (the `[free-core·J]` factorization is invalid precisely because the cancellation is real,
  Gaussian/Bartlett-exact). The residual LABOUR is the Lean cover assembly + the `⅟`→`⁻¹` integrand
  conversion + verifying no Beta-divergence survives on the cover boundary — **not** a wall. Applies to
  the descent regardless of architecture. **← still worth a `local-codex-consult` on the Lean shell/cover
  finiteness (see §9), but the MATH is settled by subred.**
- **(ii) [native `(S,J)` route ONLY] the SIX measure/prose repairs of §5.2** — the triple measure, the
  Case-1(1) label-move rule, the `J=K_S` boundary transition, the `S=1` base convention, the
  Case-2-iterates clause, and the comparability-preservation lemma. All EVAPORATE under architecture (A).
- **(iii) [native `(S,J)` route ONLY] per-layer nuisance-row separation (Codex Q5b).** After a layer
  completes, the new free matrix is `μ_{S+1} × m_{S+2}`, NOT `m_{S+1} × m_{S+2}`; when `μ_{S+1} <
  m_{S+1}` the unused rows of `C^{(S+1)}` are **smooth nuisance variables** whose separation + whose
  differentials must be recorded (they are Aoyagi's "regular block" reappearing per layer, contributing
  ½ each). Under architecture (A) these are the `M₀q` Morse block of B5b, already accounted.

**GENUINELY MISSING (would need a certificate — NONE found, but flag the risk locus):**
- The claim that **no resolved stratum has RLCT `< ½·codim` at general width** rests on Aoyagi §5's
  product-rank-flag induction, whose general-width per-stratum normal-crossing PROOF is "no evidence of a
  sub-½codim stratum" (crnrt §4, HEURISTIC in cornrev's read). The `(2,3,3,4)=5/2` non-degenerate case
  validates the mechanism; MC + cited Aoyagi + 3 decorrelated Codex reads agree on the VALUE. **Risk
  locus:** if the general-width induction needs a center beyond `{A=0},{Y=0},{im A⊆ker Y}` — cornrev
  FOLLOW-UP-2 found ONE such: the **proportionality locus `(x₂,p₂)∥(x₃,p₃)`** (the `5/2` carrier in
  `(2,3,3,4)`) must be added to the incidence-center list. **This is actionable, not missing — but it
  means the center-list B5a resolves is INCOMPLETE as first stated; add the proportionality center.**

**Net:** no wall, no genuinely-missing certificate. ONE architecture-independent analytic obligation
(pivot-charge shells) + one center-list completion (proportionality locus). Under the native `(S,J)`
route, add the six measure/prose repairs (§5.2) + the per-layer nuisance-row separation; under
`normalSlice_transfer` (A) those all evaporate. All commissionable — the residuals are hard labour on a
proven template, plus one Codex-worthy finiteness check (the pivot-charge shells).

---

## 9. Reflection (scout close)

- **The Level A / Level B discipline is now baked into the DAG (§1.5):** every descent/finiteness brick
  proves an honest `< ⊤` (Level A → `(□)`); the exact-value `= ½·minAdm` read-off is Level B (separate,
  optional, upper bound cited). No Level-A brick is named as if it proved the RLCT value.
- **Most likely to ADVANCE the build:** **B4** (the `b=1` + top-stratum leaf) as the first tide — fully
  banked inputs, no recursion, closes an entire chart class, de-risks the pivot-Schur wiring
  (already commissioned as task #114). Then **B5a′** (opaque-width block-shear) in parallel — pure linear
  algebra, `L=2` banked.
- **The recursion spine is now PROVEN (subred):** the deeper-strata descent is the corank-Gram
  chain-length reduction (threshold `min(tail)−b+1`, dominant-minor cover, `J=det⁺(Gram)^{−b/2}`),
  Gaussian/Bartlett-exact + exact witnesses. This settles the descent MATH; the residual is Lean labour
  (the cover assembly) + one ℕ-lemma (min-tail-width → `minAdm`). It also **resolves the architecture
  question**: the descent is by CHAIN-LENGTH (matches the banked kernel `remaining_lt_of_support_ssubset`),
  so the native inner-loop's six measure/prose repairs (§5.2) evaporate — build the descent via subred's
  chain-length reduction (with `normalSlice_transfer` for the charge bookkeeping), NOT Aoyagi's literal
  Case-1/Case-2 inner loop.
- **Most likely to BREAK:** the **det-inverse cover boundary** (§8-i). subred proves the math (the
  dominant-minor cover spends `J=det⁺(Gram)^{−b/2}`, the shrinking-image cancellation is exact), but the
  Lean cover assembly + verifying no Beta-divergence survives on the cover seam is the delicate labour.
  Worth a `local-codex-consult` on the Lean cover finiteness before the opaque-width lift. Secondary risk:
  the **contracting-tail twist** silently ignored — a formaliser using the free-`Q` threshold `q−b+1`
  overestimates on every `M₂<M_last` chart (and permutation-invariance says those occur at binding cuts).
  Commission B5-desc / B3 on a contracting-tail chart so the twist is exercised.
- **Center-list completion (cornrev FOLLOW-UP-2):** the incidence-center list for the deeper resolution
  needs the **proportionality locus `(x₂,p₂)∥(x₃,p₃)`** added (the `5/2` carrier in `(2,3,3,4)`) beyond
  `{A=0},{Y=0},{im A⊆ker Y}`. Actionable, not missing.
- **Next computation that clarifies:** the `(3,3,3,4)` `q∈{1,2}` first Lean milestone — subred's
  descent (B5-desc) + `normalSlice_transfer` charge (B5a) + the corner blow-up (B5c) on a
  **contracting-tail** chart, front-loading the det-inverse cover. That single vertical slice validates
  the proven B5 spine before the opaque-width lift.

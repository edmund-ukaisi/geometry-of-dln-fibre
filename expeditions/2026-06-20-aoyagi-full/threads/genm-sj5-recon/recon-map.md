# recon-map — #5 `DecoratedStepHyp` route-B tide (banked-state map + tide-readiness verdict)

**Seat:** self-recon (READ-ONLY internal reconnaissance). **Date:** 2026-07-12. **NO Lean edits, NO build.**
**Charge:** map our OWN banked state for the #5 `DecoratedStepHyp` build (the recursive STEP leg of
`DecoratedDescent`, the route-ii native discharge of `(□) = RouteMBoxThresholdFinite`) so the eventual #5
tide's spec names banked pieces rather than starting blind. Scrutinise the coupled-corner "deepest
soundness" hardest.

**Checkpoint read:** canonical `expedition/aoyagi-full @a9da8a0e` (this worktree). Design docs:
`joint-corner-cert.md` (§1–§8), `stephyp-buildplan.md` (§5′/§6″), `stephyp-intersection-cert.md`,
`nocollapse-soundness-hunt.md`, `genm-sj4-recon/{recon-map,p0-gamma-clause-cert}.md`. Contract: canonical
`RouteMSJDecoratedRec.lean`. Bricks grep'd on canonical.

**Legend:** [BANKED] in-repo sorry-free on canonical · [ADJ] banked-adjacent (small lemma off a banked one)
· [OWED] genuine new build · [OWED★] the crux owed build · [#4] gated on the #4 tide's landed γ' shape.

---

## 0. The frame — what #5 must produce, and against which `adm`

The contract (`RouteMSJDecoratedRec.lean:144`, canonical, sorry-free):

    DecoratedStepHyp adm :=
      ∀ (L) (M : Fin (L+1+1+1) → ℕ),
        (∀ M' D', adm (L+1) M' D' → DecoratedBoxThresholdFinite D')   -- DECORATED strong IH
        → ∀ (D : SJDecoration M), adm (L+1+1) M D → DecoratedBoxThresholdFinite D

where `DecoratedBoxThresholdFinite D := ∀ c' < carrierThreshold M, D.integral c' < ⊤`
(`RouteMSJDecorated.lean:148`), `carrierThreshold M = ½·minAdm M` (`:64`), and

    D.integral c' = ∫⁻ z in D.dom, ∫⁻ u in unitBox D.d,
        ofReal ((∏_ℓ |u ℓ|^(D.jac ℓ)) · (D.decLoss u z)^(-c'))        (`RouteMSJDecorated.lean:139`)

with `D.decLoss u z = D.carrier.loss u (ctx z).1 (ctx z).2` (`:128`), `carrier.loss = ∑ᵢ (monomial·residual)²`
(`RouteMSJLinGen.lean:120`). So #5 is stated on a GENERAL admissible carrier decoration `D` — **not** the
trivial one; the trivial-decoration recovery (`decoratedBoxThresholdFinite_trivial_iff`) is used only at the
TOP (`routeMBoxThresholdFinite_of_decoratedStep`) to recover `(□)`.

**★ Which `adm`?** Canonical `RouteMSJAdm.lean:115` is the SIMPLE valuation-predicate
`adm = genuineCarrier D ∧ (admCorankA M = 0 ∨ admCorankB M = 0 ∨ admValuation D)`, `admValuation D :=
D.d = 0 ∨ pSimultaneous D.carrier.supp` — it carries NO provenance / Γ×R split / ρ-Equiv / `minAdm ≤ a·n`.
The RICHER `FaithfulSJAt` γ' (`res = rmatMul (Γ z)(Z_tail r)(ρ i)`, split iso `eΓ`, ρ an `≃`, dims
`minAdm ≤ a·n`, δ≡0, α, β, **units DROPPED**) that #5's route-B analytic core consumes is being landed by the
#4 tide on `origin/wip/genm-sj4-base-fixedz` and is NOT on canonical yet (`genm-sj4-recon/recon-map §0`;
`p0-gamma-clause-cert §1`). **#5 is co-dependent with #4's landed γ' — see the Verdict.**

---

## 1. Route-B mechanism (the settled #5 plan; §6/§7 naive corner is DEAD)

At `M`'s binding cut `t★` (`minAdm M = peelCharge M t★ + minAdm (redChain t★ M)`, `exists_binding_cut`,
`RouteMSJDecoratedCharge.lean:79`), one decorated peel:

1. **Schur block-elim (rowMix)** — reindex generators into pivot⊕corank (`ι ↦ ιₚ ⊕ ι_cor`); the freed corank
   block is a fresh `a×b` matrix `Γ`, `a = M₀−t★`, `b = M₁−t★`, `peelCharge = a·b`.
2. **Radial attach** — the fresh fully-shared exceptional divisor `u₀` (`loss ↦ u₀²·loss`).
3. **Integrate-Γ-FIRST (the asymmetric coupling — the load-bearing idea).** On the units sector
   `{σ_min(Z_tail) ≥ ε}` (`Z_tail = A₂···A_L`, the WHOLE deeper tail — the §9 γ-lock correction, NOT `A₂`
   alone), integrate the freed `Γ`-block (freed Morse, dim `P = a·b`). This SHIFTS the exponent by exactly
   `½·peelCharge = a·b/2`, landing the reduced integral on `D'.integral (c'−a·b/2)` where `D'` is the peeled
   reduced decoration on `redChain t★ M`.
4. **Black-box decorated IH.** `c'−½peelCharge < ½·minAdm(redChain)` STRICTLY (`carrierThreshold_shift`), so
   the reduced integral is inside the IH range; invoke `DecoratedBoxThresholdFinite D'` as a BLACK BOX (its
   internal resolved structure is NOT needed — only its finiteness, which carries the jac monomial that a
   plain IH could not — the Q2 reason the plain `DecoratedPeelStep` is dead).

Charges ADD to `½peelCharge + ½minAdm(redChain) = ½minAdm M` — **NOT** a symmetric Hölder split (infeasible at
saturation) and **NOT** the naive `½Σ` corner (units-only; refuted §8). The off-sector `{σ_min(Z_tail)<ε}`
does NOT get a separate cover — it IS the driver's arity recursion (a deeper stratum, higher `Mval`, closed by
the same route one arity down), with the rank-drop neighbourhood split off (not null-deleted, Codex Q3).

**Value de-risked.** `nocollapse-soundness-hunt.md` (decorrelated, conclusion-withheld Codex + exact toric +
paired MC): `rlct = ½·minAdm` at every binding branch checked incl. deep-sharing `(4,4,4,4)→11/2`,
`(5,5,5,5)→17/2`; the shared-radial Jacobian `r₁^{#shared−1}` makes discrepancies ADD, so sharing RAISES the
ratio — no collapse. The one un-reproven piece is Aoyagi's resolution EXHAUSTIVENESS at arbitrary width
(cited Aoyagi). Anchor `(3,3,3,4)→7/2` recovered exactly.

**Is the mechanism a complete Lean-friendly spec?** The exponent arithmetic composes EXACTLY against banked
bricks (§2). But the mechanism as written mixes two representations — the **matrix** form (`freedSchurLoss`,
`frobSq(Γ·Z)`) that the banked Morse/Rayleigh bricks live in, and the **carrier** form (`D.decLoss =
carrier.loss`) that `D.integral` and the IH live in. The bridge between them (the peelOp CoV) is UNBUILT —
see §3 N4′ and the Verdict. This is the load-bearing observation of this recon.

---

## 2. Reusable-to-consume (banked bricks, on canonical @a9da8a0e)

| Piece | File:line | Signature / role | Plugs into #5? |
|---|---|---|---|
| `exists_binding_cut` | `RouteMSJDecoratedCharge:79` | `∃ u ≤ min(M₀,M₁), minAdm M = peelCharge M u + minAdm(redChain u M)` | YES — the peel cut `t★`. [BANKED] |
| `peelCharge` | `RouteMSJDecoratedCharge:45` | `= (M₀−u)(M₁−u) = a·b` | YES — the shift `½peelCharge`. [BANKED] |
| `carrierThreshold_shift` | `RouteMSJDecorated:71` | `carrierThreshold M − ½peelCharge M u ≤ carrierThreshold(redChain u M)` | YES — lands `c'−ab/2 < ½minAdm(redChain)`. [BANKED] |
| `half_minAdm_sub_half_peelCharge_le` | `RouteMSJDecoratedCharge:67` | ℝ form of the above | YES. [BANKED] |
| `freedSchurLoss_inner_peel_le` | `RouteMSJInnerDescent:166` | `∫_{Γ∈s}(freedSchurLoss x Γ Q)^{−c'} ≤ det(Q_bQ_bᵀ)^{−a/2}·Cresid(ab)c'·(w + frobSq(C·Q̃ₚ(1−P_{Q_b})))^{−(c'−ab/2)}`, hyps `c'>ab/2`, `Q_bQ_bᵀ PosDef`, pivot `w>0` | YES — the integrate-Γ-first VALUE with the `ab/2` shift + Gram divisor `det^{−a/2}`. [BANKED] |
| `freedSchurLoss_inner_peel_lt_top` | `RouteMSJFreedPeel:114` | `<⊤` collapse of the above | YES (the atom branch `c'>ab/2`). [BANKED] |
| `freedSchurLoss_inner_bounded_le` / `_lt_top` / `_bounded_shear_lt_top` | `RouteMSJInnerDescent:112`, `RouteMSJFreedPeel:156`, `RouteMSJInnerDescent:143` | bounded branch `c'≤ab/2` (pivot `w>0` alone; no shift; finite box) | YES — the ~94/480 atom-inapplicable charts. [BANKED] |
| `volume_genBox_lt_top`, `measure_shearbox_lt_top` | `RouteMSJInnerDescent:53,66` | entry/shear box finite volume | YES — discharges the `hs` obligation. [BANKED] |
| `pivotEnergy_inverse_free` | `RouteMSJInnerDescent:94` | `P(Qp+P⁻¹B₁₂Qb) = PQp+B₁₂Qb` (P⁻¹ cancels) | YES — the `{w=0}` locus is a clean bilinear condition, P⁻¹-free. [BANKED] |
| `frobSq_mul_ge` | `RouteMSJLeafRayleigh:38` | `(Z·Zᵀ − c•1) PSD ⟹ c·frobSq Γ ≤ frobSq(Γ·Z)` (eigenvalue-free) | YES — the units-sector Rayleigh (route B additive comparison). [BANKED] |
| `frobSq_mul_rpow_le` | `RouteMSJLeafRayleigh:62` | value-majorant form | YES. [BANKED] |
| `exists_gram_sub_smul_one_posSemidef_of_rank_eq` | `RouteMSJUnitsBridge:156` | `Z.rank = n ⟹ ∃c>0, (Z·Zᵀ − c•1) PSD` | YES — the per-peel units RE-SUPPLY on the sector (a CONDITIONAL, not a carried clause — Codex: invoke ONLY after sector-restriction). [BANKED] |
| `posDef_gram_of_rank_eq`, `exists_pos_smul_one_le_of_posDef`, `linearIndependent_row_of_rank_eq` | `RouteMSJUnitsBridge:52,63,43` | the units-bridge internals | YES (inside the bridge). [BANKED] |
| `corank_survival_ae` | `RouteMSJCorankSurvival:88` | `b ≤ Zdeep.rank ⟹ ∀ᵐ A, (A·Zdeep).rank = b` (minor-cut null) | YES — invariant-(ii) preservation / `p=0` (the `b` corank rows survive full-row-rank). [BANKED] |
| `minAdm_redChain_succ_ge`, `_ge_corankWidth`, `minAdm_binding_convexity_le` | `RouteMSJTransversality:48,68,35` | the convexity `C_t+(a+b−1) ≤ C_{t+1}` ⟹ deeper rank `≥ b` | YES — `p=0` + `minAdm≤a·n` preservation. [BANKED] |
| `minAdm_backPeel_cominimizer_ge_corankWidth`, `exists_minAdm_backPeel_cominimizer_corankWidth` | `RouteMSJBackPeel:108,123` | the QIP back-peel co-minimiser `ρ ≥ b` | YES — the deeper rank `≥ b` witness (#2b feeder). [BANKED] |
| `loss_blockSplit` | `RouteMSJLinGen:290` | `G.loss = ∑ pivot² + ∑ corank²` over `ιₚ⊕ι_cor` | YES — the SHAPE of the split (NOT the reindexing; see caveat below). [BANKED] |
| `radialStep` / `loss_radialStep`; `SJDecoration.radialAttach` / `radialAttach_decLoss` | `RouteMSJLinGen:176,192`; `RouteMSJDecorated:242,262` | fresh shared divisor `u₀`, `loss ↦ u₀²·loss` (M-preserving) | YES — the (b) attach-radial half of the peel. [BANKED] |
| `rowMix` / `gen_rowMix_const` / `sharedDivisorExp_rowMix_const`; `SJDecoration.rowMix` / `rowMix_decLoss` | `RouteMSJLinGen:204,251,274`; `RouteMSJDecoratedRowMix:56,100` | the (a) clear-first Schur mix at CONSTANT support (M-preserving) | PARTLY — see caveat. [BANKED-with-caveat] |
| `sharedDivisorExp_prependColumn_zero/_succ/_one_zero` | `RouteMSJLedger` | fresh `u₀` shared exp `=1`; old divisors preserved | YES — the α (pSimultaneous) preservation. [BANKED] |
| `measurable_decLoss`, `measurable_integrand`, `lintegral_unitBox_succ_cons` | `RouteMSJDecoratedMeas:66,94,111` | decoration measurability + the `d+1` unit-box peel | YES — measurability plumbing. [BANKED] |
| `mulLeftₚ`/`det_mulLeftₚ`/`lintegral_comp_mulLeftₚ`/`lintegral_box_le_absorption` | `RouteMSJDecoratedPeelMeas:37,51,69,90` | matrix-space Haar CoV over the RAW pi type (dodges the module diamond) | YES — the absorption Jacobian for the CoV. [BANKED] |
| `freedSchurLoss_absorption`, `freedSchurLoss_smul` | `RouteMSJDecoratedPeelCore:41,64` | the corner absorption + `u₀`-scaling of `freedSchurLoss` | YES — the corner algebra. [BANKED] |
| `corankLeaf_rpow_lt_top` | `RouteMSJLeafFinite:76` | `∫_{matBox}(frobSq(rmatMul Γ Z))^{−c'} < ⊤` (Rayleigh→free-Γ Morse) | YES — the freed-Γ leaf finiteness (also #4's base engine). [BANKED] |
| `decoratedBoxThresholdFinite_of_decoratedStep`, `routeMBoxThresholdFinite_of_decoratedDescent` | `RouteMSJDecoratedRec:161,216` | the arity strong-induction driver consuming `DecoratedStepHyp adm` | YES — the wrapper; #5 supplies `DecoratedStepHyp`. [DRIVER, BANKED] |

**★ Caveat on `rowMix` / `loss_blockSplit` (read `RouteMSJLinGen:221-231,281-289`).** These are ALGEBRAIC
IDENTITIES, not the peel: `loss_blockSplit` "carries none of `frobSq_blockDiag_split`'s Schur-complement
content … the reindexing from the actual block-diagonalisation is the deferred recursion"; `gen_rowMix`'s
support-homogeneity `hsh` for a REAL Schur block-elim matrix `R` "does NOT hold for an arbitrary R … it is the
substantive obligation, deferred to the recursion" (`gen_rowMix_const` discharges it only at CONSTANT support,
i.e. right after a shared radial). So the SCAFFOLD is banked; the actual pivot⊕corank reindexing + the `hsh`
discharge for the true Schur unit are OWED (part of N4′).

---

## 3. Production obligations (per stephyp-buildplan §6″ / §5′; banked-vs-owed)

**★ NO banked `peelOp` exists.** A grep for `SJDecoration M → SJDecoration (redChain …)` / `peelOp` returns
NOTHING. The only decoration transforms banked are M-PRESERVING (`radialAttach`, `SJDecoration.rowMix`). The
redChain-RE-TYPING peel transform — the #5 centerpiece — is entirely unbuilt.

- **N4′ — the peelOp `SJDecoration M → SJDecoration (redChain t★ M)` + the integral CoV. [OWED★ — the crux]**
  Must (i) re-type `M → redChain t★ M` with `Z : Params M → Params(redChain t★ M)` keeping `ν = product index
  type FIXED` (FLAG-2: record the row-elimination in `coeff`/`supp`, do NOT shrink `ν`); (ii) realise the
  pivot⊕corank reindex + discharge `gen_rowMix`'s `hsh` for the true Schur unit; (iii) the CoV connecting
  `D.integral c'` to `[freed-Γ inner]·D'.integral(c'−ab/2)` — including the **carrier→matrix weld**
  (`decLoss → freedSchurLoss` / `frobSq(Γ·Z)`, the P⁻¹-free pivot form, `transversality §10`/#141-Q2) and the
  **Gram-divisor→`jac'` threading** (`det(Q_bQ_bᵀ)^{−a/2}` from `freedSchurLoss_inner_peel_le` rides into
  `D'.jac`); (iv) measurability. Scaffold banked (radialAttach, rowMix, freedSchurLoss, PeelMeas CoV,
  DecoratedMeas); the transform-as-such + the CoV is the OWED assembly, and it is genuinely-new construction,
  not banked-brick glue.
- **ρ-Equiv PRODUCTION. [OWED, fidelity]** peelOp must produce `ρ' : D'.ι ≃ (Fin a × Fin Dt)` (one generator
  per resolved-corner entry, `|ι'| = a·Dt`, none spurious/omitted) — the fidelity #4 CONSUMES as a hypothesis
  and #5 must re-establish. (On the WIP branch `WeightedLeafForm`'s `ρ` is a bare function; the ρ-Equiv is
  owed at both #4-P2 and here.)
- **UNIFORM transversality (owed piece A / N1). [OWED, geometric]** `σ_{ρ+1}(Z_tail)² ≍ dist(·,{rank≤ρ})²`
  UNIFORM on compact charts — the sector-coercivity source. Generic `m=1` immersion is INSUFFICIENT
  (`[[1,t],[t,0]]` is affine+immersive yet `σ_min ≍ t²`, §8-1). The buildplan calls this banked-adjacent to
  `normalSlice_transfer` (#109) — **but `normalSlice_transfer` / `RankLocusClosed` are NOT present in
  `DLNFibre/Core/` on this branch** (grep-confirmed). So N1 has no local anchor here; it is genuinely owed
  (possibly on another branch). The units-sector coercivity itself is supplied by
  `exists_gram_sub_smul_one_posSemidef_of_rank_eq` GIVEN full-row-rank of `Z_tail` on the sector — N1 is what
  certifies that rank/order on the good tube.
- **Invariant preservation α / β / δ≡0 / dims / units.**
  - **α (pSimultaneous)** — [BANKED, ledger] `sharedDivisorExp_prependColumn_one_zero/_succ` (fresh `u₀` shared
    exp `1`; old preserved). `p=0` via `minAdm_redChain_succ_ge_corankWidth` + `corank_survival_ae`.
  - **β (threshold ≥ ½minAdm)** — [BANKED] `carrierThreshold_shift` + `minAdm = peelCharge + minAdm(redChain)`.
  - **δ≡0 (residualSupport ≡ 0)** — [BANKED/ADJ] peelOp prepends a uniform column ⟹ uniformity preserved.
  - **dims `minAdm ≤ a·n`** — [BANKED-ADJ] `minAdm_redChain_succ_ge` convexity (`RouteMSJTransversality`).
  - **provenance/split (`res = (Γ·Z_tail)_ρ`, `eΓ` MP, `dom` factorisation)** — [OWED, #4-gated] the peel is a
    measure-preserving chart producing `D'` with `res' = (Γ'·Z_tail')_{ρ'}`; CO-CONSISTENT with #4's γ' but
    the PRODUCTION is #5's. This clause is the one that makes the route-B Rayleigh step connect (see Verdict).
  - **units** — NOT carried; re-derived per-peel on `{σ_min(Z_tail)≥ε}` via `#147` (`p0-gamma-clause-cert §1`
    verdict DROP; decorrelated-Codex-concurred). Off-sector `{σ_min<ε}` recurses (arity descent).
- **The measure-level sector supply. [OWED, assembly]** The three hyps of `freedSchurLoss_inner_peel_le`
  (`Q_bQ_bᵀ PosDef`, pivot `w>0`, `c'>ab/2`) FAIL pointwise; supplying them as a MEASURE statement is the
  genuine #5 measure work: the cover `{σ_min(Z_tail)≥ε} ⊔ {<ε}`, the UnitsBridge on the sector (ONLY after
  sector-restriction — Codex unsoundness subtlety), the off-sector into the driver's arity recursion, uniform
  constants + finite subcover (no null-deletion, Codex Q3). `Core.RankLocusClosed` (the minor-cut strata) is
  the buildplan's anchor for the stratification — **also not present in Core on this branch** (grep). The
  `c'>ab/2` vs `c'≤ab/2` split is banked at the inner level (atom vs bounded branch).

---

## 4. Pitfalls (lean/CLAUDE.md + prior threads)

1. **Heavy-spectral-`def` isDefEq/whnf timeout.** #5's twoBlock spectral assembly (front-first) MUST use the
   abstract-`Aux`-over-abstract-binding form + `rw` (not `unfold`), `rw`-chains (not defeq-heavy `calc`); `set`
   does NOT help. (Confirmed `RouteMSJFrontFirst`, `genm-sj5`, 2026-07-11.) The units bridge is already
   eigenvalue-FREE (`exists_pos_smul_one_le_of_posDef`) — prefer it; do not reach for eigenvectors.
2. **Opaque-width `Fin`-cast quirk.** Matrix-apply `simp` "no progress" at dependent non-syntactic widths
   (`Fin (M 1)`, `Fin (redChain …)`). Pattern: prove each entry as a `have` at explicit `⟨_, by decide⟩`/`by
   omega` indices, then `exact` into the `fin_cases` goal (Fin proof-irrelevance unifies). Bites the
   `redChain` re-type + the `tailProd` suffix product.
3. **Dependent-matrix reassociation kernel.** `rw [Matrix.mul_assoc]`/`simp`/`conv` will NOT match `(a·b)·c`
   through the dependent `HMul`; use a fully-applied `mul_three_reassoc` term. Cast bookkeeping at the EQUIV
   level, never entrywise (`finCongr_refl` → `Matrix.reindex_refl_refl` via `erw`). Peel layer-products by
   prefix/suffix induction (`prodAux_succ`), not entrywise. Bites the peelOp `Z : Params M → Params(redChain)`
   re-index and any `Z_tail` product.
4. **Measure-CoV instance diamond (`Matrix.module` vs `NormedSpace.toModule`).** Transcribe matrix-space CoV
   over the RAW pi type (`Fin c → Fin t → ℝ`) — already done in `RouteMSJDecoratedPeelMeas.mulLeftₚ`; REUSE it,
   don't re-derive on the `Matrix.module` branch.

---

## 5. Dead / ruled-out routes (#5 must NOT reach for these)

- **The plain-IH `DecoratedPeelStep`** (`RouteMSJDecoratedRec:78`; skeleton `RouteMSJDecoratedPeelStep.lean`,
  UNTRACKED, holds the isolated `innerCorankDescent_lt_top` sorry). Q2-DEAD: the plain undecorated IH `∀M',
  RouteMBoxThresholdFinite M'` has NO budget for the extra Gram weight `H⁻⁴` the peel emits at the zero-slack
  cut. #5 uses the DECORATED IH. (Its `innerCorankDescent_lt_top` shape — the freedSchurLoss triple integral
  over `A'`×`x`×`Γ` — is still a useful MODEL for the inner core, but the IH must be decorated.)
- **The §6/§7 naive-corner / corank-of-Z stratification** (`joint-corner-cert §8` REFUTATION, exact-verified).
  Two errors: (C) Eckart–Young "single matrix m=1, base bottoms out" is a CATEGORY ERROR (`[[1,t],[t,0]]`);
  "charges ADD to ½Σ" is UNITS-SECTOR-ONLY (scalar chain `∏aᵢ` gives `lct=½=½minAdm`, a MIN not a SUM). The
  corank-≥2 shared-divisor collapse (`d²(x²+y²)` shared `lct=½` MIN vs unshared `lct=1` ADD, identical widths)
  binds at `(3,3,4)`. SUPERSEDED by route B / the decorated descent = the coupled `diag(b)` (R1 #122). The
  well-foundedness is the DRIVER's arity recursion, NOT a separate corank-of-Z descent.
- **Carrying the units-sector coercivity as an `adm` clause** (`p0-gamma-clause-cert`, decorrelated DROP).
  z-DEPENDENT, UNSATISFIABLE `∀r ∈ dom` at intermediate arity (`r=0 ⟹ Z_tail=0`, `−c•1` not PSD). Re-supplied
  per-peel on the sector via `#147`, never carried.
- **`½(D_q+d_q)` per-cell value / `D/m ≥ n₀` criterion** (`stephyp-intersection-cert §8`). View-DEPENDENT;
  over-asserts on narrow fronts. The VIEW-FREE invariant is `½(M₀ρ + min(M₀q, D_q))` with
  `min_q = ½minAdm`, `m=1` per direction (NOT `det(PPᵀ)` order `2q`), `D_q ≤ M₀q` at binding.

---

## 6. ★ VERDICT — DESIGN SETTLED (no pen-and-paper wall); tide NOT bounded-labour — front-loaded on ONE genuinely-new construction (N4′), co-dependent with #4

**The coupled-corner "deepest soundness" has NO unproven analytic sub-claim and NO unpinned constant.** The
estimate is fully reduced: `freedSchurLoss_inner_peel_le` gives the EXACT `ab/2` exponent shift + the Gram
divisor `det^{−a/2}`; `carrierThreshold_shift` lands `c'−ab/2 < ½minAdm(redChain)` STRICTLY; `frobSq_mul_ge` +
`exists_gram_sub_smul_one_posSemidef_of_rank_eq` supply the units on the sector; the atom (`c'>ab/2`) vs
bounded (`c'≤ab/2`) split is banked; the value `½minAdm` is de-risked ∀ width; the dead routes are excised.
The exponent arithmetic composes exactly. **So NO design/pen-and-paper pass is needed FIRST** — the mechanism
(route B) is complete and decorrelated-confirmed.

**BUT the tide is NOT "bounded formalisation labour over banked bricks."** The coupled-corner soundness
reduces to the banked INNER bricks only THROUGH connective tissue that is entirely unbuilt and is
genuinely-new construction, not glue:

- **The crux gap is N4′ — the peelOp CoV** (`SJDecoration M → SJDecoration (redChain t★ M)` + the integral
  reduction). NO banked `peelOp` exists; the banked transforms are all M-preserving. The banked route-B
  "pieces" (`freedSchurLoss_inner_peel_le`, `loss_blockSplit`, `frobSq_mul_ge`) live in the MATRIX
  representation, while `D.integral` and the IH live in the CARRIER representation (`decLoss = carrier.loss`).
  **The bridge between them for a GENERAL admissible `D` — the carrier→matrix weld + the pivot⊕corank reindex
  (discharging `gen_rowMix`'s `hsh` for the true Schur unit) + the Gram-divisor→`jac'` threading — is exactly
  where the coupled-corner soundness sits at the Lean level, and it is unbuilt.** The dead route-A did this
  weld ONLY for the trivial decoration (via `gammaPeelIntegral_schurShearFree_eq`, starting from the plain
  product box); there is no analogue for a general carrier. `RouteMSJDecorated`'s own docstring calls this
  peel the "~65–75% genuinely-new construction."

- **Where a hidden gap could still hide (scrutinise hardest): the reduced-core FIDELITY.**
  `freedSchurLoss_inner_peel_le`'s output base is `w + frobSq(C·Q̃ₚ·(1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b))` — the
  Schur-complement residual. For the decorated IH to fire, this must be PROVEN to equal a genuine
  `redChain`-decoration `D'.decLoss` that SATISFIES `adm D'`. This "`decLoss → carrier.loss` post-corner
  base-connection (P⁻¹-free pivot form)" (`stephyp-buildplan §5′ N4′ (2)` / `transversality §10` / #141-Q2) is
  UNVERIFIED. If the reduced core is NOT a faithful redChain product loss, the IH does not apply and the peel
  does not close. This is the #1 residual soundness risk — recommend a short pen-and-paper (or an `example`
  witness at `(3,3,2,2)→(2,2,2)`) confirming the Schur-complement residual IS the redChain carrier loss BEFORE
  committing the N4′ tide.

- **The analytic core is NOT γ'-shape-independent (mild correction to the pipeline brief).** Route B's
  units-sector Rayleigh step connects the carrier corank block to `frobSq(Γ·Z_tail)` THROUGH the γ' provenance
  clause `res = rmatMul (Γ z)(Z_tail r)(ρ i)` + the ρ-Equiv. The CANONICAL `adm` here (valuation-predicate)
  lacks these. So #5's core CONSUMES the richer `FaithfulSJAt` γ' the #4 tide is landing — the units RE-SUPPLY
  is γ'-DEPENDENT, not merely the "γ'-preservation bookkeeping." **#5 must be sequenced after / co-committed
  with #4's landed γ', and its spec parameterised on the interface facts (`stephyp-buildplan N5`), not the
  canonical valuation form.**

- **Two secondary owed builds** (banked-adjacent, genuine but smaller): (A/N1) UNIFORM transversality
  `σ_{ρ+1}² ≍ dist²` on compact charts — the buildplan's anchors `normalSlice_transfer` (#109) /
  `Core.RankLocusClosed` are NOT on this branch, so N1 has no local base here; and (E) the measure-level
  sector supply / off-sector recursion assembly (finite subcover, uniform constants, no null-deletion) — the
  QIP threshold arithmetic (dmcheck) is necessary but NOT sufficient for the neighbourhood cover.

**Net.** No design wall — the math is settled and de-risked. But this is a LARGE, multi-tide build whose
critical path is a single genuinely-new construction (N4′ peelOp CoV), with a real un-verified fidelity claim
inside it (the reduced-core = redChain carrier loss) that warrants a ~1-page pen-and-paper BEFORE the N4′ tide,
and a hard sequencing dependency on #4's landed γ'. "Tide-ready" only in the sense that the spec below can be
written now; NOT in the sense of bounded banked-brick assembly.

---

## 7. Proposed tide-spec skeleton (build order; banked pieces named; γ'-parts flagged [#4])

**Sequencing:** start AFTER (or co-committed with) the #4 tide landing `FaithfulSJAt` (Γ×R γ', ρ an `≃`, units
dropped) on canonical. State `DecoratedStepHyp` parameterised on `adm`'s interface facts, not the canonical
valuation form.

- **S0 (pen-and-paper, PRE-tide, ~1 page) — the reduced-core fidelity.** Confirm the Schur-complement residual
  `w + frobSq(C·Q̃ₚ(1−P_{Q_b}))` (output of `freedSchurLoss_inner_peel_le`) EQUALS a genuine `redChain t★ M`
  carrier loss `D'.decLoss` satisfying `adm D'`. Anchor: `(3,3,2,2) →_{t=2} (2,2,2)` (the regression already in
  `RouteMSJAdm.lean:163`). Output: the exact `D'` construction the N4′ peelOp targets. STOP-flag if the
  residual is not a faithful redChain loss.

- **S1 — peelOp construction (N4′, [OWED★]).** `peelOp t★ : SJDecoration M → SJDecoration (redChain t★ M)`:
  (a) rowMix pivot⊕corank reindex, discharging `gen_rowMix`'s `hsh` at the fresh-block constant support
  (`gen_rowMix_const`, `sharedDivisorExp_rowMix_const`); (b) `radialAttach` the shared `u₀`
  (`radialAttach_decLoss`, `loss_radialStep`); (c) the `Z : Params M → Params(redChain)` re-index keeping
  `ν` FIXED (FLAG-2), reusing the dependent-matrix reassociation kernel; (d) `jac' = jac ++ Gram divisor`. Bank
  measurability via `measurable_integrand` / `RouteMSJDecoratedMeas` + the raw-pi CoV `RouteMSJDecoratedPeelMeas`.

- **S2 — the integral CoV + carrier→matrix weld.** `D.integral c' → [inner-Γ over freedSchurLoss] ·
  D'.integral(c'−ab/2)`: the weld `decLoss → freedSchurLoss` via the γ' provenance `res = (Γ·Z_tail)_ρ` [#4] +
  the ρ-Equiv reindex (`Equiv.sum_comp`); `loss_blockSplit` for the pivot⊕corank shape; `freedSchurLoss_smul`
  / `freedSchurLoss_absorption` (`RouteMSJDecoratedPeelCore`) for the corner algebra.

- **S3 — the sector cover + units supply.** Cover `dom = {σ_min(Z_tail)≥ε} ⊔ {<ε}`. On the sector: full-row-
  rank ⟹ `exists_gram_sub_smul_one_posSemidef_of_rank_eq` ⟹ `hG`/`hpiv` for `freedSchurLoss_inner_peel_le`
  (invoke ONLY after sector-restriction — Codex). Off-sector: recurse via the driver's arity descent (deeper
  `Mval`, threshold `≥½minAdm` per-branch). [OWED assembly] finite subcover + uniform constants (no
  null-deletion). Requires **N1 uniform transversality** [OWED, geometric — no local anchor on this branch].

- **S4 — the two exponent branches.** `c'>ab/2`: `freedSchurLoss_inner_peel_le` (shift `ab/2`, Gram divisor).
  `c'≤ab/2`: `freedSchurLoss_inner_bounded_shear_lt_top` (bounded, no shift). Both banked.

- **S5 — close via the IH.** `carrierThreshold_shift` ⟹ `c'−ab/2 < ½minAdm(redChain)`; invoke the DECORATED IH
  `DecoratedBoxThresholdFinite D'` (black box) on `peelOp t★ D`.

- **S6 — `adm D'` preservation (peel-closure).** α [BANKED ledger] + `p=0` (`minAdm_redChain_succ_ge_corankWidth`
  + `corank_survival_ae`); β [BANKED `carrierThreshold_shift`]; δ≡0 [BANKED]; dims [BANKED-ADJ
  `minAdm_redChain_succ_ge`]; **provenance/split/ρ-Equiv [#4 — gated on #4's landed γ' shape; the ρ-Equiv
  PRODUCTION is #5's own fidelity obligation]**. Units NOT carried (re-supplied S3).

- **Wire.** Supply `DecoratedStepHyp adm` (with `adm_trivial` + the #4 `DecoratedBaseHyp`) to
  `routeMBoxThresholdFinite_of_decoratedDescent`; `#print axioms` clean `[propext, Classical.choice,
  Quot.sound]`.

**γ'-preservation parts flagged [#4]:** S2's carrier→matrix weld (consumes provenance), S6's provenance/split/
ρ-Equiv preservation. These are gated on #4's landed FaithfulSJAt γ' (Γ×R, ρ an `≃`, units dropped) — the
#4 recon-map §8 tide-spec is the co-consistency contract. Everything else (S1 scaffold, S3 sector/units, S4
branches, S5 IH, S6 α/β/δ/dims) is γ'-shape-STABLE now.

# recon-map — front-end machinery for the (□) CAPSTONE (`headSplit_domination`)

**Charge (self-recon, read-only):** map the front-end reduction machinery for filling
`headSplit_domination` @ `RouteMSJDeeperFlagCore.lean:545` (the (□) Brick-D analytic sorry;
`deeperFlag_shell_le@752` is proven modulo it + Brick F). Base inspected: `origin/genm-sj5-brickdcont`
(tip `5c4f7f607`, 2026-07-15). All file paths below are `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJ*.lean`
unless noted. NO Lean edits/builds were run — this is a source + log sweep; `#print axioms` is flagged as a
capstone verification step (I could not run it).

---

## HEADLINE — what to reuse / avoid / what's staged (fold into the tide spec)

**The entire reduction `shellSpineIntegrand → deeperFlagCoreIntegrand (= G) → finiteness` is ALREADY BANKED
as a downstream `_impl` tower** — `RouteMSJHeadSplitDom` ← `RouteMSJPivotDom` ← `RouteMSJPivotFin`. Every
step reproduces its stub's signature verbatim and is **source-clean except two genuinely-open leaf sorries**.
The capstone is therefore an **ASSEMBLY + WIRING + 2-mechanical-fill** job, **not new heavy analysis**.

**The live finiteness route is the FULL-BLOCK Loewner-floor route (S3-free, chart-free), approved
2026-07-14.** It is `RouteMSJPivotFin`'s `pivotDom_finiteness_impl` (`:1313`). **The controller's brief route
("`G < ⊤` via charts 4+5 + incidence gluing + exponent gate") is STALE** — that machinery
(`RouteMSJIncidenceChart4Polar`, `RouteMSJIncidenceGluing`, `RouteMSJIncidenceExponent`, `transverseSchurGram`)
is **banked but ORPHANED**: `git grep` finds ZERO consumers of `chart4_Htilde_fibre_lt_top`,
`incidenceCell_lintegral_le`, `transverseSchurGram` anywhere, and `clsCodim_gate` /
`lintegral_lt_top_of_finite_cover` are used only inside their own files. The full-block route bypasses
the S3 corank peel AND the incidence atlas entirely (`pivotPeel_domination` docstring: "the route bypasses
the S3 corank peel entirely — Codex-corroborated ... `hcvg`/`hmM`/`ε'`/`U_sf`/frame hypotheses are UNUSED").

**Consequence for blocker (a):** **chart-5 is MOOT for `headSplit_domination`.** The capstone does NOT need to
dependency-invert on a chart-5 hypothesis. See §(iv).

**The genuinely-new labour (§(iii)) is:** (1) fill `shellSpine_le_hsQ_box` (mechanical measure
reorganisation; all deps banked) + `pivotDom_uzero` (u=0 edge; not analytic); (2) an **R-A wiring refactor**
— the `_impl`s sit *downstream* of the stubs (cyclic-import), so wiring needs a new top file, not a one-line
`exact` (established precedent, lessons.md:3141); (3) **three stub-signature corrections** on
`headSplit_domination` itself (`hc0`, `hε'le`/fixed-ε', `hjr`-vs-saturated-`j=min`, `hGmeas`); (4) an
axiom-clean verification (the tower is currently CI-orphaned — its sorries pass `lake build DLNFibre`
silently).

---

## THE REDUCTION CHAIN (the call graph + status)

Import direction is DOWNSTREAM (`A ← B` = B imports A). Aggregator `DLNFibre.lean` imports **only**
`RouteMSJDeeperFlagCore` (`:1438`); the whole `_impl` tower is NOT in the root closure.

```
DeeperFlagCore (aggregator-visible)
  deeperFlag_shell_le            :752  PROVEN mod {Brick F, Brick D}   (the headline)
    = deeperFlag_spineToCore     :656  PROVEN mod {F, D} + in-tide clauses
        ∘ deeperFlag_shell_core_le (L1) :368  PROVEN, sorry-free      (G → comparator.integral)
    Brick F  exists_headSplitFrame :492  SORRY :501   ← impl ready (see below)
    Brick D  headSplit_domination  :513  SORRY :545   ← THE CAPSTONE TARGET; impl ready
      │
      ▼ (headSplit_domination_impl, verbatim sig, HeadSplitDom:238; PROVEN mod 2)
HeadSplitDom  (imports DeeperFlagCore)
  headSplit_domination_impl      :238  = le_trans (shellSpine_le_hsQ_box) (headSplit_pivotDom)
  shellSpine_le_hsQ_box          :210  SORRY :234   ← GENUINELY OPEN #1 (mechanical head/row split)
  headSplit_pivotDom             :85   SORRY :108   ← impl ready (ratio trick)
      │
      ▼ (headSplit_pivotDom_impl, verbatim sig, PivotDom:122; PROVEN mod 3)
PivotDom  (imports HeadSplitDom)
  pivotDomLHS :44 / pivotDomRHS :57   (defs: LHS = freed-loss @ hsQ; RHS = deeperFlagCoreIntegrand@clean data)
  headSplit_pivotDom_impl        :122  = ratio trick (exists_finite_mul...) over the 3 stubs below
  pivotDom_finiteness            :74   SORRY :89    ← impl ready (full-block route)
  pivotDom_RHS_ne_zero           :96   SORRY :103   ← impl ready (pivotDomRHS_ne_zero_aux)
  pivotDom_uzero                 :109  SORRY :115   ← GENUINELY OPEN #2 (u=0 edge, not analytic)
      │
      ▼ (PivotFin, verbatim-sig impls; SOURCE-CLEAN)
PivotFin  (imports PivotDom; nothing imports PivotFin)
  pivotDom_finiteness_impl       :1313 PROVEN (full-block route) — transitively uses pivotDom_uzero (open)
  pivotDomRHS_ne_zero_aux        :757  PROVEN (source-clean)     — feeds pivotDom_RHS_ne_zero
  pivotPeel_domination           :1240 PROVEN (LHS ≤ C·RHS via ratio + full-block)
```

**Two integrands (the endpoints of the reduction):**

- `shellSpineIntegrand` (`DeeperFlagCore:444`): `∫_{A'∈paramsBox(tailChain)∩shell} ∫_{x∈outerDom} ∫_{Γ:Γ+schurShift x∈genBox} ofReal(freedSchurLoss x Γ ((prod(tailChain M) A').submatrix (blockSplitEquiv κ) id)^(-c'))`.
- `deeperFlagCoreIntegrand = G` (`DeeperFlagCore:339`): `∫_{z∈paramsBox(redChain)} ∫_{v∈unitBox d} ofReal(∏|v_ℓ|^{jc_ℓ}) · (∫_{A_cor∈matBox} ∫_{Γ∈sΓf z} ofReal((D.decLoss v z + frobSq(Ccrossf z + Γ·(A_cor·Zf z)))^(-c')))`. At the capstone's clean data `k=![1]`, `jc=![minAdm−1]`, `Ccrossf=0`, `sΓf=genBox` (this instance is `pivotDomRHS`, PivotDom:57).

---

## (i) CONSUME — banked, reuse verbatim (names + file:line)

### Front-end reduction primitives (the `shellSpine → hsQ-box` / D-substitution / row-split machinery)
- `pivotInner_Dsubst` `PivotFin:238` — **the `{IsUnit P}` shear (Step 1).** Freed-Γ inner integral (`{Γ | Γ+schurShift x ∈ genBox}`) `=` block-front integral over raw `D∈genBox` via `freedSchurLoss_eq_frobSq_block` + measure-preserving translation `D := Γ+schurShift x` (`measurePreserving_add_right`, no `Matrix.module` diamond — raw pi type). Needs `IsUnit(of x.1.1)` = the 4th `outerDom` conjunct.
- `freedSchurLoss_eq_frobSq_block` `PivotFin:208` — freed Schur loss = plain block loss of reconstructed `[[P,B₁₂],[C,Γ+schurShift x]]` (`schurLoss_of_blockSplitD_symm_shift` + `frobSq_schur_split_inv`).
- `blockFront_rowSplit` `PivotFin:267` — **the pivot/corank row split (Step 2).** `frobSq(fromBlocks P B₁₂ C D · Q) = frobSq(P·Q_p + B₁₂·Q_b) + frobSq(C·Q_p + D·Q_b)` (`frobSq_sum_rows` `:225`).
- `pivotDomLHS_eq_blockFront` `PivotFin:336` — folds the freed-Γ spine into the clean block-front integral over `D∈genBox` (threads `pivotInner_Dsubst` through outer `(z,A_cor)`).
- `blockFront_inner_eq` `PivotFin:541` — `(P,B₁₂,C)×D` over `outerDom×genBox` = block-coordinate integral over `genBox ∩ {IsUnit toBlocks₁₁}` (`blockSplitD` MP; `blockSplitD_preimage_outerDom`).

### The FULL-BLOCK finiteness route (the LIVE `G < ⊤` engine — S3-free, chart-free)
- `frobSq_mul_ge_of_gramFloor` `PivotFin:376` — the joint Loewner floor `frobSq(B·Q) ≥ ε²·frobSq(B)` on the shell (`Q·Qᵀ ⪰ ε²·1`).
- `shell_fullBlock_le` `PivotFin:456` — the checkpoint: block-front integral over the block box `≤ ofReal((ε²)^(-c')) · ∫_{matBox(u+a)(u+b)} frobSq^(-c')` (pointwise floor + `matReindexEquiv` reindex, `|det|=1`).
- `matBox_frobSq_neg_lintegral_lt_top` `PivotFin:410` — pure-cube finiteness for `c' < (p·q)/2` (via `matReshapeEquiv` to the flat cube + `lintegral_box_sq_neg_lt_top`).
- `minAdm_add_peel_le` `PivotFin:579` — the nat chain `minAdm(redChain u M) + (M₀−u)(M₁−u) ≤ (u+(M₀−u))·(u+(M₁−u))` (via `hpiv`, `tailMinWidth ≤ M 1`).
- `pivotDomRHS_eq_top_of_critical` `PivotFin:1073` — comparator-side divergence `RHS = ⊤` for `c' ≥ (minAdm+ab)/2` (the threshold extractor; uses `vfibre_top` `:911`, `prodFrobSq_pos_ae` `:620`).
- `exists_finite_mul_of_finite_imp` `PivotFin:365` — the generic ℝ≥0∞ ratio trick: `R≠0` + (`R<⊤ → L<⊤`) ⟹ `∃ C<⊤, L ≤ C·R`.
- `pivotDomLHS_lt_top_of_pos` `PivotFin:1135` / `pivotDomLHS_lt_top_of_zero` `PivotFin:1179` — the `0<c'` and `c'=0` finiteness edges.
- `pivotPeel_domination` `PivotFin:1240` — assembles `∃ C<⊤, pivotDomLHS ≤ C·pivotDomRHS` (**PROVEN, docstring "sorry-free and axiom-clean, full-block route"** — but see §(iii): transitively depends on the open `pivotDom_uzero` and on `pivotDomRHS_ne_zero_aux`).
- `pivotDomRHS_ne_zero_aux` `PivotFin:757` — `pivotDomRHS ≠ 0` (source-clean; the `0·∞` guard the ratio trick needs).

### The mechanical head/row-split helpers (staged for `shellSpine_le_hsQ_box`)
- `hsSplit` `HeadSplitDom:114` + `measurePreserving_hsSplit` `:128` — the MP equiv `Params(tailChain) ≃ᵐ Params(redChain u M) × corankRows` (`paramsHeadSplit` + `rowSplitEquiv` + reassoc).
- `hsSplit_snd/_fst_zero/_fst_succ` `:142/147/152` — forward-action `rfl` lemmas.
- `hsSplit_good_of_shell` `HeadSplitDom:182` — **PROVEN.** Ky-Fan / shell ⊆ good-set: on the shell, `weakEigCount ε' (deeperFlagZdeep) ≤ M₂ − m` (via `prod_headSplit` + `shell_subset_goodSet` + `weakEigCount_mono`).
- `weakEigCount_mono` `:157`, `freedSchurLoss_submatrix_congr` `:168` — PROVEN plumbing.
- `rowSplitEquiv`/`measurePreserving_rowSplitEquiv`/`rowSplit_lintegral_eq` `RouteMSJRowSplit.lean:47/53/101` — the row Tonelli split.
- `paramsHeadSplit`/`paramsHeadSplit_mp` `RouteMSJHeadSplit.lean:51/57`, `prod_headSplit` `:93` — the head-split MP + `prod = A₀·Z_deep`.
- `shell_subset_goodSet` `RouteMSJShellContain.lean:161` — the D-C containment.

### Comparator / decLoss / L1
- `cornerComparator` `RouteMSJCornerComparator.lean:50`; `pivotRHS_decLoss_eq` `PivotFin:156` — `decLoss v z = (v 0)²·frobSq(prod z)` at clean data.
- `deeperFlag_shell_core_le` (L1) `DeeperFlagCore:368` — **PROVEN.** `G ≤ C · cornerComparator.integral(c'−½·peelCharge)` via `shell_corankOffSector_le_unif`. (This is the "ratio-trick → comparator.integral" step the brief mentions; it is DONE and lives above the capstone target — the capstone need only produce `G`, i.e. `deeperFlagCoreIntegrand`, not `comparator.integral`.)
- `deeperFlagCore_decLoss_pos_ae` `DeeperFlagCore:552` — PROVEN (`hpos` clause).

### Brick F (separate isolated brick, but blocks the same headline)
- `exists_headSplitFrame_impl` `RouteMSJHeadSplitFrame.lean:181` — **source-clean** impl of Brick F (Borel functional calculus on the one primitive `measurableEigendecomp`). Ready to wire alongside D.

---

## (ii) ASSEMBLY SHAPE — how `G < ⊤` is built + where the Jacobian sits

**The live shape is NOT the brief's chart atlas.** It is:

1. **`shellSpine → hsQ-box` (`shellSpine_le_hsQ_box`, OPEN):** head-split the outer `A'` into `(z, A_cor)`
   via `hsSplit` (MP); rewrite `Zf z = deeperFlagZdeep` on the shell (`hsSplit_good_of_shell` + `hagree`);
   drop the shell indicator (`≥0`); Tonelli + `rowSplit_lintegral_eq`; recombine to the `(z, A_cor)`-box
   freed-loss integrand at `Q = hsQ` (pivot rows `prod(redChain u M) z`, corank rows `A_cor·Zf z`),
   restricted to `pivotShell` (`{A_cor | hsQ·hsQᵀ ⪰ ε²·1}`). **No analytic content** — pure measure
   reorganisation; every ingredient banked.

2. **`hsQ-box → finiteness` (`headSplit_pivotDom` ← ratio trick ← `pivotDom_finiteness`, IMPL ready):**
   the ratio trick (`headSplit_pivotDom_impl`, PivotDom:122) turns the domination into a **finiteness
   comparison**: `RHS=⊤ ⟹ C:=1`; else `C:=LHS/RHS` (`ENNReal.div_mul_cancel`, needs `RHS≠0`), valid iff
   `LHS<⊤`. So `∃ C<⊤, LHS ≤ C·RHS` is `pivotDom_finiteness : RHS<⊤ → LHS<⊤` plus the two guards
   (`pivotDom_RHS_ne_zero`, `pivotDom_uzero`).

3. **The finiteness `LHS < ⊤` (`pivotDom_finiteness_impl`, PivotFin:1313, full-block):**
   fold to block-front (`pivotDomLHS_eq_blockFront`) → reassemble inner (`blockFront_inner_eq`) → drop the
   `{IsUnit P}` restriction → on `pivotShell` bound the **WHOLE block** `T=[[P,B₁₂],[C,D]]` by the joint
   Loewner floor (`shell_fullBlock_le` via `frobSq_mul_ge_of_gramFloor`) → the `Q`-uniform pure-cube
   constant `ofReal((ε²)^(-c'))·∫_{matBox(u+a)(u+b)} frobSq^(-c')` (finite for `c'<(u+a)(u+b)/2` by
   `matBox_frobSq_neg_lintegral_lt_top`) × finite `(z,A_cor)`-box volume. The threshold closes via
   `pivotDomRHS_eq_top_of_critical` (`RHS<⊤ ⟹ 2c'<minAdm+ab`) + `minAdm_add_peel_le` (`minAdm+ab ≤ (u+a)(u+b)`).

**Where the Jacobian goes (the brief's `|det D|^{n−b−a−u}` worry):** in the full-block route there is **NO
det-power Jacobian to compose**. The only change-of-variables are (i) the shear `D := Γ+schurShift x`
(translation, `|det|=1`), (ii) `blockSplitD` and `matReindexEquiv`/`matReshapeEquiv` (permutation/reshape
reindexings, all measure-preserving, `|det|=1`). The pivot's radial `r^{u·M₁−1}` monomial (D-A blow-up) is
**not on this path** — it belonged to the superseded direct-domination route. So the "assembly guard" the
brief warns about (Jacobian composition across charts 1/3/5) does not arise here.

**Guards' Lean encoding (brief item 4) — where each is threaded, and their live status:**
- JOINT (not per-`z`): the Loewner floor is stated on the FULL block `T·Q` (`shell_fullBlock_le`), not
  block-by-block — inherently joint.
- INTEGRATED (not pointwise): the whole comparison is between lintegrals; the ratio trick is a finiteness
  comparison of integrals, never a pointwise `≤` (the pointwise bound is FALSE as `σ_min(Q_p)→0`, per the
  PivotDom soundness note). Correctly encoded.
- `a+b ≤ M₂` scope / coupled Gram: **the full-block route does not use these** (they gated the S3 corank
  peel, now bypassed). `hcvg`/`hmM` are inert in `pivotPeel_domination`. This is why the route is "S3-free".
- The load-bearing guard that IS live: **keep the corank block** — do NOT drop `freedSchurLoss ≥ pivot`
  (over-estimates to ⊤ in `c'∈(uρ/2, minAdm/2)`; PivotDom soundness note, `(3,3,3),u=2` witness). The
  full-block bound keeps the whole `T`, so it respects this.

---

## (iii) GAP LIST — the genuinely-new capstone labour (KEY DELIVERABLE)

**Not new analysis. The open items are 2 mechanical fills + a wiring refactor + 3 signature corrections +
axiom verification.**

### GAP-1 — `shellSpine_le_hsQ_box` (`HeadSplitDom:234`, OPEN, mechanical)
The one front-end reduction step with NO impl. Docstring claims "NO analytic content — pure measure
reorganization." All dependencies banked (`hsSplit`, `measurePreserving_hsSplit`, `hsSplit_good_of_shell`,
`rowSplit_lintegral_eq`, `prod_headSplit`, `shell_subset_goodSet`). Labour = assemble the MP-equiv chain +
Tonelli + indicator-drop + the shell⊆good rewrite. **Real (non-trivial plumbing) but not novel math.**

### GAP-2 — `pivotDom_uzero` (`PivotDom:115`, OPEN, non-analytic edge)
The `u=0` degenerate edge (`LHS ≤ RHS`). Docstring plan: front block vanishes ⟹ `freedSchurLoss=frobSq(Γ·Q_b)`,
`(P,B₁₂,C)`-integral over a singleton, `hpiv` forces `minAdm(redChain 0 M)=0` ⟹ RHS monomial `|v0|^0=1`,
Tonelli factorisation ⟹ `LHS=RHS`. **NOT the analytic crux** (no pivot energy). Needed because
`pivotDom_finiteness_impl` calls it in the `u=0` branch (so the full-block finiteness is NOT axiom-clean
until this is filled).

### GAP-3 — the WIRING refactor (cyclic-import; NOT a one-line `exact`)
Every `_impl` sits DOWNSTREAM of its stub (import chain `DeeperFlagCore ← HeadSplitDom ← PivotDom ←
PivotFin`), so the stub file cannot `exact <impl>` (the impl file imports the stub file). The established
fix is **R-A** (lessons.md:3141, the L2 precedent): create a NEW TOP file
(e.g. `RouteMSJDeeperFlagWiring.lean`) that imports the whole tower, **move `deeperFlag_spineToCore` +
`deeperFlag_shell_le` there** (the two theorems consuming the F/D stubs), and wire
`headSplit_domination := headSplit_domination_impl …` and `exists_headSplitFrame := exists_headSplitFrame_impl …`
there; then re-point `DLNFibre.lean` (and any consumer of `deeperFlag_shell_le`) to the new top file.
Similarly the PivotDom stubs (`pivotDom_finiteness`, `pivotDom_RHS_ne_zero`) are dischargeable only in a file
that sees PivotFin — i.e. at or below `PivotFin`. **This is the #1 non-obvious capstone task; the controller
holds the engine/app-split architecture and should decide the file layout before the tide starts.**

### GAP-4 — three STUB-SIGNATURE corrections on `headSplit_domination` (`DeeperFlagCore:513`)
`headSplit_domination_impl` (HeadSplitDom:238) needs hypotheses the stub does not carry. These are genuine
signature gaps, not just plumbing:
- **`hc0 : 0 ≤ c'`** — impl needs it; stub has only `hcT : c' < carrierThreshold M` (an upper bound). Must
  be threaded from the RLCT `NNReal` exponent context (`c' ≥ 0`). Add to the stub or thread from the caller.
- **`hε'le : ε' ≤ ε / √(M₁·M₂)`** (or fix `ε' := ε/√(M₁M₂)`) — impl needs it; stub quantifies over ALL
  `ε'>0`. **The stub statement is likely FALSE for large `ε'`** (the good set `G` shrinks, `hagree` goes
  vacuous, shell ⊄ G, domination fails). Per lessons.md:287 ("a sorry on a false statement is a landmine"),
  **restate the stub signature in the same pass** (the caller `deeperFlag_spineToCore` sets `ε'=ε/√(M₁M₂)`,
  so the narrowing is free).
- **`hjr : j < min(M₀−t, M₁−t)` (STRICT)** vs stub's `hj : j ≤ min(…)` — the impl (and
  `hsSplit_good_of_shell`) needs strict; **`j = min` is the SATURATED branch, a separately-HELD explicit
  hole** (satcover hunt, scoping doc). So `headSplit_domination` as stated (∀ `j≤min`) is NOT fully
  dischargeable by the impl — only `1≤j<min`. Decide: re-scope the stub to `j<min`, or route `j=min` to the
  saturated-branch hole.
- **`hGmeas`** (measurability of the good set) — impl needs it; likely dischargeable inline (`weakEigCount`
  measurable), thread or prove in the wiring.

### GAP-5 — axiom-clean verification (the tower is CI-orphaned)
`DLNFibre.lean` imports only `DeeperFlagCore`; the `_impl` tower is NOT in the root closure, so its sorries
**pass `lake build DLNFibre` silently** (lessons.md:166 — orphaned modules; only `scripts/sorries` globs
them). After wiring, the capstone MUST run the FULL-trunk build + `scripts/sorries` + **`#print axioms
deeperFlag_shell_le`** and confirm `[propext, Classical.choice, Quot.sound]` only. I could not run these; the
"source-clean" reads above (`PivotFin`, `HeadSplitFrame`) mean no literal `sorry` token, NOT verified
axiom-clean — `pivotDom_finiteness_impl` transitively carries GAP-1/2's `sorryAx` until filled.

### GAP-6 — Brick F (`exists_headSplitFrame`, `DeeperFlagCore:501`)
Separate isolated brick, but `deeperFlag_shell_le` needs it too. Impl `exists_headSplitFrame_impl`
(HeadSplitFrame:181) is source-clean and ready; wire it in the same R-A top file. (Outside the strict
"front-end" charge, but flagged because the headline is not sorry-free without it.)

---

## (iv) CHART-5 hypothesis shape — MOOTED on the live path

**Blocker (a) dissolves:** the full-block route needs no chart-5 statement, so the capstone does NOT
dependency-invert on chart-5. For completeness, the shape as spec'd in `chart45-spec.md` (were the chart
route revived):
- `chart5_rank_eq {u d ℓ} (W11 : ℓ×ℓ) (W12 W21 W22) (h11 : IsUnit W11.det) : (fromBlocks W11 W12 W21 W22).rank = ℓ + (W22 − W21·W11⁻¹·W12).rank` (block-LU / Schur; `{E=0} ↔ rank W ≤ ℓ`).
- `chart5_bigcell_cov` — the measure CoV on `{det W₁₁ ≠ 0}`, Jacobian `≡ 1` (translation in the `W₂₂`
  block), via `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.
- Exponent hook: radial exponent `C_{ℓ,s} = clsCodim` (`RouteMSJIncidenceExponent`); `clsCodim_gate` gives
  `q < T1 ⟹ 2q < C_{ℓ,s}`.

If a future re-scope ever needs the chart route, parameterise on
`(chart5_rank_eq_hyp, chart5_bigcell_cov_hyp)` as explicit hypotheses and land them on `genm-sj5-chart5`.
**But for THIS capstone: skip charts 4/5 entirely.**

---

## (c) LESSONS / pitfalls that bite this build

- **Orphaned-module CI silence** (lessons.md:166): the `_impl` tower is not in the root closure; its sorries
  don't show in `lake build DLNFibre`. Gate with `scripts/sorries` + full-trunk build + forced `#print axioms`.
- **A `sorry`'d body type-checks but is not done** (lessons.md:120): "source-clean" (no `sorry` token) ≠
  axiom-clean. Confirm the artifact, not the remembered "compiles".
- **ℝ≥0∞ `a·b < ⊤ ⟺ both < ⊤` is FALSE** (`0·∞=0`, lessons.md:393): the ratio trick's `C:=LHS/RHS` needs
  `RHS ≠ 0` — exactly why `pivotDom_RHS_ne_zero` / `pivotDomRHS_ne_zero_aux` exist. Don't drop that guard.
- **False-statement sorry = landmine** (lessons.md:287): GAP-4's `hε'le` — restate the SIGNATURE, not just
  the docstring. A caveat may narrow a claim, never contradict it.
- **`Matrix.module` diamond on translation CoV**: the shear (`pivotInner_Dsubst`) deliberately substitutes on
  the RAW pi type `Fin a → Fin b → ℝ` (`measurePreserving_add_right`), NOT the matrix type — preserve that
  when touching the shear.
- **Keep the corank** (PivotDom soundness note, `RouteMSJPivotDom.lean:22`): numerically-verified that
  dropping it over-estimates `LHS` to `⊤` in `c'∈(uρ/2, minAdm/2)`. The full-block bound keeps the whole
  block `T`; any "simplification" that drops it is UNSOUND.
- **Block-matrix `rw` gotchas** (brickdcont build notes): `Matrix.neg_neg` won't `rw`/`simp` (use `abel`);
  `nonsing_inv_mul_cancel_left` takes `A` explicitly; `fromCols 1 X` needs the `1` ascribed;
  `Measure.map_addHaar_smul` puts `|·|` OUTSIDE the inverse.

---

## (d) DEAD / ruled-out routes to AVOID

- **The chart-4/5 + incidence-gluing + exponent-gate route for `G<⊤`** — SUPERSEDED by the full-block route
  (approved 2026-07-14, PivotFin header; Codex-corroborated). Banked but ORPHANED (zero consumers). Do NOT
  wire `chart4_Htilde_fibre_lt_top` / `incidenceCell_lintegral_le` / `lintegral_lt_top_of_finite_cover` /
  `clsCodim_gate` / `transverseSchurGram` into the capstone. (Keep them on the branch; a future tight-RLCT
  computation may want them, but they are off the finiteness path.)
- **The S3 corank-peel DIRECT domination** (D-A `pivotBlock_radial_blowup` `RouteMSJPivotBlowup.lean:154`;
  D-B `lintegral_cube_frobSq_neg_of_finrank_range` `RouteMSJRankRCodim.lean:357`) — banked but consumed
  ONLY by docstrings (`git grep`: the sole non-decl mentions are docstring text in HeadSplitDom/PivotDom +
  AxCheck). The `headSplit_pivotDom` / `pivotDom_finiteness` DOCSTRINGS still describe this D-A/D-B route —
  **those docstrings are STALE**; the actual impl (`pivotDom_finiteness_impl`) uses the full-block route.
- **The A_cor-free pull-out of the pivot weight** (`shell_corankPivot_coupled_le`, `PivotFin:306`) — this
  *coupled* S3 lemma is present and PROVEN (its docstring "STATEMENT for review, fill pending" is STALE —
  the body is complete), but it is NOT on the full-block critical path. Its own docstring records that the
  naive A_cor-free pull-out is the "unsound one archfin ruled out". Avoid the decoupled pull-out.
- **Pointwise domination `shellSpine ≤ C·G`** — FALSE as `σ_min(Q_p)→0`. Must stay INTEGRATED (the ratio
  trick). (PivotDom soundness note.)

---

## Contradictions / stale references flagged (verify against live tree, not the log)
1. **Controller brief route ("charts 4+5 + gluing + exponent → G<⊤") is STALE** — superseded by the
   full-block route on `brickdcont` itself.
2. **`headSplit_pivotDom` / `pivotDom_finiteness` docstrings describe the D-A/D-B route** they no longer use.
3. **`shell_corankPivot_coupled_le` docstring says "fill pending"** but the lemma body is complete (proven).
4. **`headSplit_domination` stub statement is over-general in `ε'`** (GAP-4) — likely false for large `ε'`.
5. **"source-clean" `PivotFin`/`HeadSplitFrame`** are NOT axiom-clean until GAP-1/2 land (transitive `sorryAx`).

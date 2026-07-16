# genm-rescoperecon — re-scope recon-map: the shell-restricted coupled-residual route

**Seat:** self-recon (read-only INTERNAL reconnaissance), aoyagi-full endgame. **Date:** 2026-07-14.
**NO build, NO edits.** Maps our OWN banked state for the re-scope off the (now-FALSE) full-block
off-shell route back to the SHELL-RESTRICTED coupled-residual (couplingfin's original OBSTACLE-A).

**Read:** `threshold-verdict-cert.md` (DEGRADES verdict + mechanism), `coupling-verdict-cert.md`
(§156-174 shell-restricted design), `endgame-lanes.md` (thresholdhunt/t2adjud/pradial/finfin/wallfin
entries), the driver `RouteMSJDeeperFlagCore.lean` (working tree), and the branch states
`genm-sj5-step2` local@`e60260db` (shell-restricted RIPPLE) / origin@`e395121c9` (shell-0 crux) /
`genm-sj5-finfin|shearfin|wallfin|flagpeel` (the false full-block route).

---

## ★ HEADLINE VERDICTS (the four decision inputs)

1. **DRIVER TRACE → option (i) [restore-shell] is REQUIRED; option (ii) [argmin-restrict] is INSUFFICIENT.**
   The driver instantiates the wall at cut `u = t★ + j`, `j` ranging `0..r` (`r = min(M₀−t★, M₁−t★)`),
   and the LHS is genuinely shell-**j**-restricted (`singularShell ε r ⟨j⟩`). `j ≥ 1` are non-argmin cuts
   that the cover needs. The correct fix is the shell-**j** restriction (RHS domain = shell-j), NOT
   full-matBox (thresholdhunt: RHS diverges), NOT pivotShell = shell-0 (t2adjud's misread; only sound at j=0).

2. **BANKED / SALVAGEABLE.** The shell-**0** crux is DONE sorry-free (`pivotPeel_domination`, row-Gram-floor
   route, origin step2). The corank ½ab charge is DONE sorry-free (`shell_corankOffSector_le_unif`,
   `shell_corankPivot_coupled_le`). The CoV/plumbing (`pivotBlock_radial_blowup`, ratio-trick trio, block-box
   reindex) is shell-agnostic and salvageable. **The `j ≥ 1` finiteness was NEVER built sorry-free on any
   branch** — the full-block route only ever produced scaffolding toward the false `frobSqBlockFull_lt_top`;
   `stackedGram_flagPeel_le` (wallfin's k>1 design) is not a theorem on any branch.

3. **EXACT RESTORATION.** Re-restrict the crux `A_cor` domain from `pivotShell` (shell-0) to `singularShell j`
   (matching the LHS), which turns the broken bridge `shellSpine_le_hsQ_box` into a clean measure-preserving
   reindex (same singular values, same domain — t2adjud's disjoint-domain problem dissolves), and prove a
   shell-j crux `headSplit_pivotDom_j`: j=0 IS the DONE `pivotPeel_domination`; j≥1 is the new strong/weak split.

4. **TRACTABILITY → CANDIDATE WALL, not clean labour. GATE before building.** The `1≤j<r` shell finiteness
   is (a) **soundness-UN-ADJUDICATED** (does shell-j ∧ IsUnit-P exclude thresholdhunt's divergence and restore
   finiteness up to `carrierThreshold` per `j`? couplingfin certified only j=0; thresholdhunt refuted the
   IsUnit-DROPPED full box; the shell-j ∧ IsUnit-KEPT object is in between and never adjudicated), and (b)
   even if sound, the BUILD = the strong-minor-chart stratification (wallfin's k>1), multi-hundred-line and
   NEVER built. **Recommend a decorrelated obstruction hunt on the shell-j∧IsUnit object BEFORE commissioning
   a build.**

---

## 1. DRIVER TRACE (settles the re-scope severity) — option (i) REQUIRED

### 1(a) The cut is `u = t★ + j`, `j ∈ 0..r` — j≥1 ARE non-argmin, so argmin-restrict is insufficient

`RouteMSJDeeperFlagCore.headSplit_domination` (Brick D, `RouteMSJDeeperFlagCore.lean:513`, a `sorry` stub)
and the headline `deeperFlag_shell_le` (`:750`) are stated at `(t j : ℕ)` with

- `ht : t ≤ min (M 0) (M 1)` (the binding cut `t★`),
- `hj : j ≤ min (M 0 - t) (M 1 - t) =: r`,
- cut `u = t + j` everywhere (`redChain (t + j) M`, `κ : Fin (t + j) ↪ Fin (M 1)`).

So the driver needs the wall at **every** `j ∈ 0..r`. Since `j ≥ 1 ⟹ u = t★ + j` is a strictly-deeper cut
than the binding `t★`, and thresholdhunt certified the off-shell full-block threshold is `u`-independent
(`minAdm(M)/2`) while the wall commits to cut `u` (`(minAdm(redChain u M)+ab)/2`), those `j ≥ 1` cuts are
exactly the NON-argmin cuts where the full-block wall overcharges. **⟹ thresholdhunt option (ii)
(argmin-restrict `u`) is INSUFFICIENT — the driver genuinely instantiates non-argmin cuts. Option (i)
(restore the shell) is the only fix that covers the cuts the driver needs.**

### 1(b) The wall is used SHELL-j-restricted (over `singularShell j`), NOT full-matBox

The LHS of Brick D / the headline is `shellSpineIntegrand M (t+j) κ ε r ⟨j,_⟩ c'`
(`RouteMSJDeeperFlagCore.lean:541`), and `shellSpineIntegrand` (`:444`) integrates the outer variable `A'`
over

    paramsBoxM (tailChain M) 1  ∩  {A' | prod (tailChain M) A' ∈ singularShell ε r ⟨j⟩}

i.e. the deep-tail product `prod (tailChain M) A'` (an `M₁ × M_last` matrix) is pinned to flag level `j`
(`singularShell ε r j = {Z | min(weakEigCount ε Z, r) = j}`, `RouteMSJShellCover.lean:94`; exactly `j`
singular values `< ε` for `j<r`, `≥ r` for `j=r`). **The driver LHS is shell-j-restricted.**

The false step is downstream, in the PROOF of Brick D (`headSplit_domination_impl`), not in the driver:
it enlarges the shell-j LHS to a full-matBox / shell-0 RHS. See §3.

### 1(c) CONFIRMED: the correct fix is the shell-**j** restriction

`hsQ M u Zf z A_cor := fromRows(pivot rows prod(redChain u M) z, corank rows A_cor·Zf z)`
(`HeadSplitDom.lean:44`, @e60260db) is the whole front product `W` reindexed — **identical singular values**
to `prod (tailChain M) A'`. Hence:

- `singularShell 0 = {σ_min ≥ ε} = pivotShell M u ε Zf z` (`HeadSplitDom.lean:63`) — the two agree at j=0;
- `singularShell j` (j≥1) has `σ_min < ε` ⟹ **DISJOINT** from `pivotShell` (t2adjud's concrete refuter).

So the three candidate RHS domains and their status:

| RHS domain | LHS ≤ RHS holds? | RHS finite? | verdict |
|---|---|---|---|
| `pivotShell` (= shell-0) | only j=0 (disjoint for j≥1) | yes | **t2adjud: false for j≥1** |
| full matBox (drop indicator) | yes (monotone) | **NO** (thresholdhunt: diverges non-argmin) | **false target** |
| `singularShell j` (match LHS) | yes (identity) | **the open question** | **the correct fix** |

---

## 2. BANKED SHELL-RESTRICTED-ROUTE STATE (inventory)

### 2A. DONE sorry-free — reusable AS-IS (shell-agnostic or shell-0)

- **`shell_corankOffSector_le_unif`** — SORRY-FREE, working tree `RouteMSJDeeperFlagCore.lean:259`.
  The ½ab corank charge over the FULL matBox in `A_cor` with the DEEP floor `hshell : Z·Zᵀ ⪰ ε²·U_s·U_sᵀ`:
  `∫_{A_cor∈matBox} ∫_Γ (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'} ≤ deeperFlagUnifConst · w^{−(c'−ab/2)}`
  for FIXED scalar pivot energy `w > 0`, `ab/2 < c'`. Consumes `corankBlock_morsePeel_setLE`,
  `shellCorankWeight_le_unif`, `corank_survival_ae`. **This is the whole `j≥1` corank side already** — but
  only against a fixed-scalar `w`; the coupling to the actual (A_cor-dependent) pivot energy is Brick D's job.
- **`shell_corankPivot_coupled_le`** — SORRY-FREE, origin step2 `RouteMSJPivotFin.lean:306`. The σ-COUPLED
  S3-variant: same ½ab det-Gram charge but for a GENERAL weight `wf : (Fin b→Fin M₂→ℝ) → ℝ`, `wf A_cor > 0`
  (the pivot energy AS a function of A_cor). Bounds by `det((A_cor·Z)(A_cor·Z)ᵀ)^{−a/2}·Cresid·(wf + frobSq(
  Ccross·(1−proj)))^{−(c'−ab/2)}`. This is couplingfin §2's "the coupling is benign" formalised for the
  corank block. Reusable for the shell-j corank side.
- **`pivotBlock_radial_blowup`** (D-A) — SORRY-FREE, working tree `RouteMSJPivotBlowup.lean:154`. Pure CoV
  identity `∫_W φ(frobSq(W·Q)) = ∫_ω ∫_r r^{uw−1}·φ(r²·frobSq(reshape(ω)·Q))` — shell-AGNOSTIC, Q any fixed
  matrix. The P-radial blow-up machine. Salvageable for any route.
- **`shell_fullBlock_le`** — SORRY-FREE, origin step2 `RouteMSJPivotFin.lean:456`. The row-Gram floor
  `frobSq(B·Q) ≥ ε²·frobSq(B)` route: on the **shell-0** floor `Q·Qᵀ ⪰ ε²·1` (all σ ≥ ε), bounds
  `∫_B frobSq(B·Q)^{−c'} ≤ ε^{−2c'}·∫_B frobSq(B)^{−c'}`. **DOES NOT transfer to shell-j** (σ_min < ε there)
  — this is the exact reason j≥1 needs the strong/weak split.
- **`pivotPeel_domination`** — DONE sorry-free + axiom-clean, origin step2 `RouteMSJPivotFin.lean:1240` (crux
  fidelity PASS, cruxreview). The **shell-0 (pivotShell) crux** via `shell_fullBlock_le` + the ratio-trick.
  Handles `j = 0` COMPLETELY. Its statement/proof are shell-0-only (t2adjud).
- **Ratio-trick plumbing** — SORRY-FREE, origin step2 `RouteMSJPivotFin.lean`: `pivotDomRHS_ne_zero_aux:757`,
  `pivotDomRHS_eq_top_of_critical:1073`, `exists_finite_mul_of_finite_imp:365`, `frobSq_mul_ge_of_gramFloor:376`,
  `blockFront_rowSplit:267`, `pivotInner_Dsubst:238`, `freedSchurLoss_eq_frobSq_block:208`,
  `minAdm_add_peel_le:579`. Shell-agnostic; reusable to convert "shell-j finiteness" into the domination form.
- **Ky-Fan / frame** — SORRY-FREE: `shell_subset_goodSet` (`RouteMSJKyFan`), `exists_headSplitFrame` is a
  `sorry` stub (Brick F, `DeeperFlagCore.lean:492`), `hsSplit_good_of_shell` (`HeadSplitDom.lean:182` @e60260db).
- **`deeperFlag_shell_core_le`** (L1) — the comparator step, working tree `DeeperFlagCore.lean:368`; consumes
  `shell_corankOffSector_le_unif` at `w = decLoss`. (In the working tree it still carries the tracked stub;
  the analytic content it depends on is the SORRY-FREE `_unif`.)

### 2B. The RIPPLE shell-restricted scaffold (local `genm-sj5-step2` @e60260db) — the ORIGINAL OBSTACLE-A shape

This is couplingfin's shell-restricted design as Lean skeletons (all `sorry`, correct-shaped):

- `pivotDomLHS` (`PivotDom.lean:44`): `∫_z ∫_{A_cor ∈ matBox ∩ pivotShell M u ε Zf z} ∫_x∈outerDom ∫_Γ
  freedSchurLoss(x,Γ, hsQ)^{−c'}` — **shell-restricted** (but on `pivotShell` = shell-0; see §3).
- `pivotDom_finiteness` (`PivotDom.lean:74`, sorry) — `hRHS < ⊤ → pivotDomLHS < ⊤`, the isolated crux; carries
  `hpiv`, `hcvg`, `hfloor`, `hUs`, `hrank`. This IS OBSTACLE-A (couplingfin §156-174) as a Lean stub.
- `headSplit_pivotDom` (`HeadSplitDom.lean:85`, sorry) — the domination form over `pivotShell`.
- `shellSpine_le_hsQ_box` (`HeadSplitDom.lean:210`, sorry) — the bridge; maps `shellSpineIntegrand(shell-j)`
  → `∫ over pivotShell` (the t2adjud-false step for j≥1).
- `headSplit_domination_impl` (`HeadSplitDom.lean:238`) — composes bridge ∘ crux; sorry-free MODULO the two
  sorries above.

### 2C. NOT salvageable — the full-block detour (dead target)

`genm-sj5-finfin|shearfin|wallfin|flagpeel` `RouteMSJHeadSplitFin.lean`: `pivotDomLHS_full_lt_top` and
`frobSqBlockFull_lt_top` (finfin:365 / shearfin:369,400 / wallfin,flagpeel:394,425) — **`frobSqBlockFull_lt_top`
was NEVER proven** (4–6 sorries per branch; always the isolated wall). thresholdhunt certified it FALSE.
`stackedGram_flagPeel_le` (wallfin's designed k>1 brick) is **not a theorem on any branch** — design only.
The IsUnit-drop `lintegral_mono_set` in `pivotDomLHS_full_lt_top` is the precise unsound step (thresholdhunt §5).
**Salvage from this route = only the shell-agnostic plumbing already listed in 2A** (reindex, CoV, ratio-trick),
NOT any finiteness content.

---

## 3. THE EXACT RESTORATION

The bug is entirely in the PROOF of Brick D (`headSplit_domination_impl`), which currently reads
(both the shell-0 e60260db version and the full-box finfin version):

    shellSpineIntegrand(shell-j)  ≤[shellSpine_le_hsQ_box]  ∫ over {pivotShell | full matBox}  ≤[crux]  C·comparator

with the middle domain NOT equal to the LHS shell-j domain — the enlargement/relabel is the false step.

**Restoration (make the middle domain = shell-j, so the bridge is an identity):**

1. **Define a shell-j pivotDomLHS** — the `A_cor`-integral restricted to
   `{A_cor | hsQ M u Zf z A_cor ∈ singularShell ε r ⟨j⟩}` (equivalently `min(weakEigCount ε (hsQ …), r) = j`),
   replacing `pivotShell M u ε Zf z` (which is exactly the `j=0` case) in `PivotDom.lean:44`.

2. **Rewrite the bridge `shellSpine_le_hsQ_box` as a clean reindex** (no indicator-drop, no enlargement):
   `hsSplit` (`HeadSplitDom.lean:114` @e60260db) is measure-preserving and carries `prod (tailChain M) A'` to
   `hsQ` (same singular values). So `{A' | prod(tailChain M) A' ∈ singularShell j}` maps to
   `{(z,A_cor) | hsQ ∈ singularShell j}` — an EQUALITY of integrals, not an inequality. t2adjud's
   disjoint-domain refuter no longer applies (LHS and RHS are the SAME region).

3. **Prove the shell-j crux `headSplit_pivotDom_j`** — `∫ over shell-j ≤ C·comparator`:
   - **j = 0**: IS the existing `pivotPeel_domination` (shell-0 = pivotShell; row-Gram floor). Done.
   - **j ≥ 1**: the NEW content. On shell-j, `hsQ` has `(M₁−j)` strong (σ ≥ ε) and `j` weak (σ < ε) column
     directions. Split `hsQ = [strong | weak]`: the strong block gets the row-Gram floor (a
     `shell_fullBlock_le` restricted to the strong minor, σ ≥ ε there), the `j` weak directions carry the
     corank charge (route through `shell_corankPivot_coupled_le` / `shell_corankOffSector_le_unif`, the ½ab
     det-Gram divisor). This is the **strong-minor-chart stratification** (wallfin's k>1 design): per-chart
     Gram–Schmidt/Schur pivots selecting the strong minor, a uniform Jacobian, additive `minAdm + ab` charge.

The shell-j-restricted crux keeps the outerDom `IsUnit P` restriction (never dropped), which is what excludes
thresholdhunt's low-rank-B divergent stratum.

**The shell-j-restricted wall, precisely** (couplingfin's coupled-residual, per flag level `j`):

    ∫_{A_cor : hsQ∈shell-j} ∫_{x∈outerDom} ∫_Γ [freedSchurLoss x Γ (hsQ)]^{−c'}  <  ⊤   for c' < carrierThreshold(M),

with `carrierThreshold(M) = (minAdm(redChain u M) + ab)/2`, `a = M₀−u`, `b = M₁−u`. (= couplingfin
§156-174's `∫[r²·frobSq(P̂·Q_stack)]^{−(c'−½ab)}·det(Gram)^{−a/2}·r^{D−1}` on the singular shell, restricted
to flag level `j` rather than only `j=0`.)

---

## 4. TRACTABILITY READ (the decision-critical judgment) — CANDIDATE WALL; GATE FIRST

**Honest verdict: this is NOT clean labour. It is a candidate wall with a soundness gate that has never been
cleared for `j ≥ 1`.** Two distinct risks, in order:

### Risk A (primary) — SOUNDNESS of the shell-j ∧ IsUnit-P object is UN-ADJUDICATED

The thing we would build (`headSplit_pivotDom_j` finiteness, `1≤j<r`) has never been adjudicated bounded:

- couplingfin certified **BOUNDED only at `j = 0`** (the good set / shell-0; explicitly "flag level j=0 / the
  good set G", coupling-verdict-cert §"the exact lemma").
- thresholdhunt certified **UNBOUNDED for the IsUnit-DROPPED full box** (all cuts; the `lintegral_mono_set`
  enlargement admits the low-rank-B stratum).
- The **shell-j ∧ IsUnit-KEPT** object (`1≤j<r`) sits between these two and was NEVER separately certified.
  thresholdhunt itself flagged this exact gap: "Whether IsUnit-restricted-but-off-shell reaches [the
  threshold], or whether the shell must be restored, needs its own adjudication (couplingfin's off-shell pivot
  degradation suggests caution)."

The plausibility argument FOR soundness: the paper's flag stratification gives `C_j ≥ minAdm(M)` per level
(final-assembly-design-cert; offsector's 3161-cut / 0-undershoot charge sweep), and keeping `IsUnit P`
excludes thresholdhunt's low-rank-B stratum. But this is a **coverage/exhaustiveness claim across all
`j∈[1,r)`** — exactly the class of claim the endgame's forward-guard says review passes over and a HUNT
catches (this is the 3rd time the "off-shell degrades / shell load-bearing" boundary has bitten:
couplingfin → t2adjud → thresholdhunt). Do NOT assume bounded because the charge arithmetic checks out;
the arithmetic checked out for the full-block route too, and the object still diverged.

### Risk B (secondary, conditional on A clearing) — the BUILD is genuine new content, never landed

Even if sound, the `j≥1` finiteness = the strong-minor-chart stratification (`stackedGram_flagPeel_le`,
k>1), which:

- is **not a theorem on any branch** (design only; wallfin's "3-way LABOUR verdict" was for this brick as a
  step toward the now-FALSE `frobSqBlockFull_lt_top`, so that verdict does not transfer);
- needs a per-point strong-minor chart (Gram–Schmidt/Schur; wallfin's TRAP-1: AVOID the global measurable
  eigendecomp `RouteMSJMeasurableEigendecomp`, 2 genuine Mathlib-gap sorries), a uniform Jacobian, a per-chart
  shifted pivot comparator, and the additive `minAdm + ab` charge — a multi-hundred-line finite-dim CoV +
  Schur + GS + det build. wallfin's TRAP-2 (σ_min ↛ det, use the Schur complement) applies.

Banked pieces that WOULD feed a sound build: `shell_corankPivot_coupled_le` + `shell_corankOffSector_le_unif`
(½ab charge, both sorry-free), `pivotBlock_radial_blowup` (D-A CoV), `shell_fullBlock_le` (the row-Gram floor,
adaptable to the strong minor), the ratio-trick trio, `pivotPeel_domination` (the j=0 base case). Missing/new:
the strong/weak chart split itself, its uniform Jacobian, and the per-chart comparator wiring — plus Brick F
(`exists_headSplitFrame`, still a sorry stub).

### Recommendation

**GATE before committing a build.** Commission a decorrelated pen-and-paper OBSTRUCTION hunt on the
shell-j ∧ IsUnit-P object (`1≤j<r`, e.g. the `(4,4,4)@u=3` / `(6,6,6)@u=4` non-argmin witnesses
thresholdhunt used, now WITH the shell-j restriction and `IsUnit P` in force): does restricting to flag level
`j` and keeping `det P ≠ 0` restore finiteness up to `carrierThreshold(M)` for each `j`? Mirror thresholdhunt's
method (exact codim of the surviving singular stratum inside shell-j ∩ {IsUnit P}; smooth-point Jacobian rank;
decorrelated Gaussian/Wishart cross-check).

- **CONFIRMED bounded** ⟹ Risk A clears; the build is Risk-B labour (banked ½ab + D-A + row-Gram-on-strong-minor
  + the new strong/weak chart split); commission it (a `pradial`-style tide with the strong-minor design first).
- **DEGRADES** ⟹ this is the **terminal wall** — the shell-restricted coupled-residual is itself unbounded for
  some `1≤j<r`, the whole head-split route (a)/(hstrict) does not close as posed, and it must be surfaced to
  the operator (a decorrelated-confirmed soundness finding, like thresholdhunt).

Either way, do NOT re-run the full-block detour, and do NOT revert to `pivotShell`/shell-0 (both refuted).

---

## Pointers (file:line)

- Driver: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeeperFlagCore.lean` — `headSplit_domination:513` (stub),
  `deeperFlag_shell_le:750`, `shellSpineIntegrand:444`, `shell_corankOffSector_le_unif:259` (sorry-free),
  `deeperFlag_shell_core_le:368`, `exists_headSplitFrame:492` (stub).
- Shell def: `RouteMSJShellCover.lean` — `weakEigCount:87`, `singularShell:94`, `singularShell_iUnion:99`.
- D-A CoV: `RouteMSJPivotBlowup.lean:154` (`pivotBlock_radial_blowup`, sorry-free).
- Shell-0 crux + plumbing (origin step2 @`e395121c9`): `RouteMSJPivotFin.lean` —
  `shell_corankPivot_coupled_le:306`, `shell_fullBlock_le:456`, `pivotPeel_domination:1240`,
  `pivotDomRHS_ne_zero_aux:757`, `pivotDomRHS_eq_top_of_critical:1073`, `exists_finite_mul_of_finite_imp:365`,
  residual sorry `pivotDom_finiteness_uzero:1301` (u=0, mooted by u≥1).
- Shell-restricted RIPPLE (local step2 @`e60260db`): `RouteMSJPivotDom.lean` (`pivotDomLHS:44`,
  `pivotDom_finiteness:74`), `RouteMSJHeadSplitDom.lean` (`hsQ:44`, `pivotShell:63`, `headSplit_pivotDom:85`,
  `shellSpine_le_hsQ_box:210`, `headSplit_domination_impl:238`, `hsSplit_good_of_shell:182`).
- Dead full-block target: `genm-sj5-{finfin,shearfin,wallfin,flagpeel}:…/RouteMSJHeadSplitFin.lean`
  (`frobSqBlockFull_lt_top`, never proven; `stackedGram_flagPeel_le` never a theorem).

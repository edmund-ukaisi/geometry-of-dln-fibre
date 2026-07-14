# Brick D (k>1) design — the corank-Schur peel. VERDICT: mechanism COHERENT (Schur-led, NOT front-B spectral) + pinned mechanism correction. **THRESHOLD CORRECTED: T1, not T2 — see `reconciliation-T1.md`.**

> ⚠ **CORRECTION (2026-07-14, `reconciliation-T1.md`).** Finding-1 below (object finite to T2 off-shell)
> is **RETRACTED**. thresholdhunt's exact ℚ-Jacobian wins: the off-shell object is finite ONLY to
> **T1 = ½·minAdm(M)** [full chain], u-independent, and is NON-DESCENDING (circular as a recursion step).
> My MC was on a binding-cut case (T1=T2 coincide) so could not discriminate. The **mechanism** below
> (row-split Schur, transverse Schur complement, coupled `w`, four thrash-guards) is UNCHANGED and correct,
> but the build target is the **SHELL-restricted `deeperFlag_shell_le` at `c' < carrierThreshold M` (=T1)**,
> retaining the shell-j partial floor — NOT the off-shell `frobSqBlockFull_lt_top` at T2. Read
> `reconciliation-T1.md` FIRST; everywhere below, read "T2" as the (false) over-claim and "the target
> threshold" as T1.

**Seat:** pen-and-paper (witness, decorrelated), aoyagi-full Stage 2, `genm-brickd-design`. **Date:** 2026-07-14.
**NO Lean, NO git, NO build.** Exact algebra (Schur block-determinant identity, exact 1-D Gamma-representation
of the front-box integral, joint divergence-threshold tests). Decorrelated `local-codex-consult` (xhigh,
gpt-5.6-sol, NO repo access — clean decorrelation; my conclusion WITHHELD): `codex/brickd-design-{prompt,answer}.md`.
Scripts (this thread): `brickd_exact.py` (multi-scale front-B exponents), `brickd_thresh3.py` (full-object
threshold), `brickd_coupled.py`/`brickd_coupled2.py` (coupled Schur-residual, w=0 vs w>0), `brickd_schur.py`
(Schur identity + det-Gram threshold).

**Consumed / read (signatures, not re-derived):** `frobSqBlockFull_lt_top` docstring + statement
(`origin/genm-sj5-wallfin` `RouteMSJHeadSplitFin.lean:394`); `hsQ`/`pivotShell`/`hsSplit`
(`RouteMSJHeadSplitDom.lean`); `blockFront_rowSplit`, `shell_corankPivot_coupled_le`,
`pivotDomLHS_eq_blockFront` (`RouteMSJPivotFin.lean`); `frontFirst_g_le_of_sector`
(`RouteMSJFrontFirst.lean`), `twoBlock_radial_le` (`RouteMSJTwoBlockRadial.lean`),
`detGram_lintegral_box_lt_top` (`RouteMSJOffSectorBPos.lean`), `corank_survival_ae` (piece-2 design),
`cornerComparator`/`.integral` (`RouteMSJCornerComparator.lean`), `carrierThreshold`/`peelCharge`/`minAdm`;
`shellj-verdict-cert.md` (T1/T2, the c'<T1 route ceiling), `coupling-verdict-cert.md` (shell load-bearing
for the pivot — the corner), `brickdfin/codex/brickd-answer.md` (STEP-0 + the ε²‖B·Π_strong‖² correction).

---

## ★ VERDICT — the k>1 brick is **buildable as the row-split corank-Schur peel** (mechanism II), NOT the front-B spectral peel (mechanism I) the name `stackedGram_flagPeel_le` suggests.

The exact target (open `sorry`, `RouteMSJHeadSplitFin.lean:394`):

    frobSqBlockFull_lt_top :  ∫_z(box redChain u M) ∫_{A_cor}(matBox) ∫_B(genBox (Fin u⊕Fin a)(Fin u⊕Fin b))
        frobSq(B · hsQ M u Zf z A_cor)^(−c')  <  ⊤,      given  2c' < minAdm(redChain u M) + ab,
    where a = M₀−u, b = M₁−u, hsQ = fromRows(Q_p, Q_b), Q_p = prod(redChain u M) z (u rows),
    Q_b = A_cor · Zf z (b rows), and the DEEP floor hfloor: Zf·Zfᵀ ⪰ ε'²·U_sf·U_sfᵀ (U_sf orthonormal
    m-frame, m ≥ a+b). NO shell σ_min(hsQ)≥ε (false for j≥1 — anti-regression).

**Three findings, load-bearing:**

1. **The finiteness is TRUE up to T2 = ½(minAdm_red + ab) off-shell** (my `brickd_thresh3.py`, exact-inner
   1-D + joint MC: finite for c'<2.5, divergent above, on the faithful `u=1,a=1,b=2` case with
   minAdm_red=3). This is NOT a contradiction of couplingfin's off-shell degradation: **`Q_p = prod(redChain) z`
   is INTEGRATED, so the transversality corner {Q_b's rowspace → Q_p's rowspace} is a positive-codimension
   coincidence in the joint (z, A_cor) space, not a fixed slice.** The z-integration is what saves the
   off-shell object; couplingfin fixed the configuration (or worked on the shell) and saw the degradation.

2. **Mechanism CORRECTION (beyond brickdfin, decorrelated Codex Q2, EXACT).** The honest weak-determinant is
   the **transverse Schur complement** `det(Q_b(I−Π_p)Q_bᵀ)`, Π_p = proj onto rowspan(Q_p), NOT the bare
   corank Gram `det(Q_bQ_bᵀ)`. Exact Schur identity (verified `brickd_schur.py`, 3/3):

       det(hsQ·hsQᵀ) = det(Q_pQ_pᵀ) · det(Q_b(I−Π_p)Q_bᵀ).

   The two measure **different** degeneracies: `det(Q_bQ_bᵀ)→0` is Q_b shrinking (corank rows → 0);
   `det(Q_b(I−Π_p)Q_bᵀ)→0` is Q_b's rowspace **aligning with Q_p's** — which occurs even when Q_b is large
   and full-rank (Codex ctrex Q_p=(1,0), Q_b=(1,t): Gram bounded, weak eig ≍ t²). The banked
   `shell_corankPivot_coupled_le` **already produces this** — its residual carries the projector
   `(1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b)` = Π_{rowspan Q_b}^⊥, so `det(Q_bQ_bᵀ)^{−a/2}` is only the Γ↦ΓQ_b **Jacobian**;
   the transversality lives in the coupled residual. The correction is in interpretation, not in the banked
   lemma.

3. **The det-Gram divisor ALONE (uniform-in-A_cor pull-out) is UNSOUND; the pivot weight `w>0` is
   load-bearing.** With w=0 the coupled residual integral `∫ det(Q_bQ_bᵀ)^{−a/2}·frobSq(Ccross·Π^⊥)^{−e}`
   diverges immediately (e=0.8 ≪ 1.5, `top5frac=0.90`, `brickd_coupled.py`). Restoring the pivot weight
   `w = frobSq(P·Q_p)`-type, the coupled integral reaches T2 (finite for c'<2.5, divergent above,
   `brickd_coupled2.py`). **This confirms the wallfin/archfin note "sup_{A_cor} C = ⊤ as A_cor→0" — the
   charges must stay COUPLED inside the A_cor integral.** The hardest lemma is exactly the coupled estimate
   keeping w.

**So the brick is build-ready, but the builder must (a) use the row-split Schur route, not a front-B
spectral peel; (b) keep the pivot weight coupled inside the A_cor integral (no uniform pull-out); (c) target
c' < T2 only** (equivalently, since the mountain supplies c' < T1 ≤ T2, a fortiori). Getting any of these
wrong is exactly what would make the build thrash on the never-landed content.

---

## 1. Route decision: mechanism (II) row-split Schur, not (I) front-B spectral

The name `stackedGram_flagPeel_le` and the wallfin docstring frame the open brick as a **front-B spectral
peel** (mechanism I): eigendecompose `G = hsQ hsQᵀ`, write `frobSq(B·hsQ) = Σ_i λ_i‖col_i(BU)‖²`, and bound
`∫_B` by a multi-scale radial estimate; k=1 closes via `frontFirst_g_le_of_sector` (single σ_min), k>1 needs
a strong-minor chart. **This route is a detour.** Exact reasons:

- **(I) genuinely loses information for k>1.** The multi-scale front-B integral's divergence depends on ALL
  weak scales, not σ_min (exact 1-D exponents, `brickd_exact.py`, p=3,r=3,c'=2.6): both weak `(t,t,1)` →
  exp −1.14; the smallest-only `(t,1e-3,1)` → −0.97; sanity `(t,t,t)` → exactly −c'=−2.6. The `(t,t,1)`
  divergence is far larger in magnitude than what σ_min = smallest scale alone would give, so collapsing to
  σ_min (`Σλ_i‖·‖² ≥ σ_min·‖B_W‖²`) OVER-counts and, integrated over A_cor, concentrates the whole charge on
  the deepest rank-drop locus — it does not reproduce the balanced det-Gram charge (Codex Q1: "over-counting,
  not a product; the largest weak scales are exhausted first; the σ_min bound over-counts, sometimes
  drastically"). There is **no** clean factorization `∏λ_i^{−a/2}` of the front-B integral in a single
  exponent.

- **(II) handles all k uniformly and is already scaffolded.** `pivotDomLHS_eq_blockFront` + `blockFront_rowSplit`
  already row-split the front block `B = [[P (u×u), B₁₂ (u×b)], [C (a×u), D (a×b)]]` in the native
  `Fin u ⊕ Fin a` / `Fin u ⊕ Fin b` index types of the `genBox`, and `shell_corankPivot_coupled_le` already
  does the corank Γ-integral for **general a, b** (via `corankBlock_morsePeel_setLE`). There is no k=1-vs-k>1
  split at the corank-peel level — the difficulty the wallfin doc attributes to k>1 is an artifact of
  choosing (I). Codex Q3/Q6 concurs (independently): "If [the coupled] lemma is proved, mechanism I is
  unnecessary; its k=1 estimate is only an optional local bound. The cleanest formal proof uses mechanism II
  plus minor-chart stratification, not a global spectral peel."

**Recommendation: build `frobSqBlockFull_lt_top` by the row-split Schur route.** `frontFirst_g_le_of_sector`
and `twoBlock_radial_le` remain useful for the PIVOT-rows front-box sub-step (§4), not for a weak-spectrum peel.

## 2. The chart split (PIN-1) — the a.e. full-corank-rank stratum, NOT a global SVD

The A_cor-space stratifies by `rank(Q_b) = rank(A_cor·Zf z)`. TRAP-1 (global measurable eigendecomp /
`RouteMSJMeasurableEigendecomp`, 2 sorries) is AVOIDED: the whole peel runs on the **a.e. full-rank stratum**
`{rank Q_b = b}`, supplied by `corank_survival_ae Zf hbZ` (b ≤ rank Zf, from the deep floor m ≥ a+b ≥ b) —
`∀ᵐ A_cor, rank(A_cor·Zf z) = b`. On this stratum:
- `Q_bQ_bᵀ` is PosDef (`posDef_gram_of_rank_eq`), so `det(Q_bQ_bᵀ) > 0`, the Schur projector
  `Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b` is a **rational** (algebraic) function of A_cor entries — measurable, no SVD.
- The measure-zero rank-drop locus `{rank Q_b < b}` contributes 0 to the extended integral (null set).

So "finitely many strong-minor charts" collapses to the single generic chart + a null set. Codex Q6: "finitely
many algebraic maximal-minor charts; no globally smooth SVD or eigenbasis is needed." This is the whole of
PIN-1. (The `{IsUnit P}` chart for the pivot corner is likewise co-null — `{det P = 0}` is a null hypersurface
in B-space — so the shear of §3 runs after a free restriction to `{IsUnit P}`, per shellj §2.)

## 3. The Schur / corank peel (PIN-2, PIN-4, PIN-5) — banked, exact

Row-split (`blockFront_rowSplit`, EXACT):

    frobSq(B·hsQ) = frobSq(P·Q_p + B₁₂·Q_b) [pivot rows, top u] + frobSq(C·Q_p + D·Q_b) [corank rows, bottom a].

On `{IsUnit P}` the shear `Γ = D − C·P⁻¹·B₁₂` frees the pivot corner (`freedSchurLoss` /
`pivotInner_Dsubst`, banked). The freed corank integral is exactly `shell_corankPivot_coupled_le`
(hyp `hc': ab/2 < c'`, `b ≤ Zf.rank`):

    ∫_{A_cor}∫_Γ (wf A_cor + frobSq(Ccross + Γ·Q_b))^(−c')
      ≤ ∫_{A_cor} det(Q_bQ_bᵀ)^(−a/2) · Cresid(ab,c') · (wf A_cor + frobSq(Ccross·(1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b)))^(−(c'−ab/2)),

with `Ccross = C·Q_p` (corank↔pivot coupling), `wf A_cor` = the post-radial pivot energy (≥0).

- **PIN-4 Jacobian.** The `det(Q_bQ_bᵀ)^(−a/2)` is the EXACT Jacobian of `Γ ↦ Γ·Q_b` on the a×b corner
  (a rows × the b-dim `Q_b` map), re-expressed as a native det-inverse — banked in
  `corankBlock_morsePeel_setLE`. It is unit/absorbable in the sense that its A_cor-integral is finite
  (`detGram_lintegral_box_lt_top`, b ≤ rank Zf); the ½ab charge is exactly this Jacobian's exponent. My
  `brickd_schur.py` confirms `∫det^{−a/2}` finite (charge a/2 within range; marginal at small widths — the
  usual endpoint, and the joint T2 has extra room from the reduced comparator).
- **PIN-5 charge.** `ab/2 = peelCharge M u / 2` (`peelCharge = (M₀−u)(M₁−u) = ab`), matching the exponent
  shift `c' → c'−½·peelCharge` in `deeperFlag_shell_le`. Index pinning (per `shell_corankPivot_coupled_le`
  docstring): a = Ccross/Γ rows = M₀−u; b = A_cor/Q_b rows = M₁−u; the atom's p·q = a·b — symmetric.
- **PIN-2 Schur.** The direct `σ_min(hsQ) ↝ det(Q_bQ_bᵀ)` comparison is FALSE (banked ctrex; Codex Q2's
  independent ctrex agrees). The honest object is the transverse Schur complement (§Verdict-2); the banked
  lemma's residual projector IS it.

## 4. The comparator wiring (PIN-3, PIN-6) — the coupled estimate is the ONE hard lemma

After §3, `frobSqBlockFull_lt_top` reduces to bounding, for c' with `ab/2 < c'` and `2c' < minAdm_red + ab`,

    (∗)  ∫_z ∫_C ∫_{A_cor} det(Q_bQ_bᵀ)^(−a/2) · (wf + frobSq(C·Q_p·Π_{Q_b}^⊥))^(−(c'−ab/2))  ≤  C_j · Comparator(redChain u M).integral(c' − ab/2),

where the RHS is the reduced comparator `∫_z (commonDivisor(z)²·frobSq(prod(redChain u M) z))^(−(c'−ab/2))`,
finite by the **outer induction hypothesis** on the SHORTER chain `redChain u M : Fin (L+2)` (one factor
fewer than `M : Fin (L+3)`) for `c' − ab/2 < ½·minAdm_red` ⟺ `2c' < minAdm_red + ab`. This is the genuine
DESCENT — non-circular exactly because the comparator is on the shorter chain (brickdfin (b), Codex Q2).

**PIN-3 strong⊕weak / corrected floor.** In the row-split, "strong" = the pivot rows, floored via the deep
floor on Q_p's strong directions; "weak" = the corank collapse + transversality, carried by the det-Gram
Jacobian + the coupled residual. The brickdfin correction `‖B·W_strong‖² ≥ ε²‖B·Π_strong‖²` (NOT `ε²‖B‖²`)
is the front-B (mechanism I) statement; in mechanism (II) its content is that the pivot energy `wf` floors
only the pivot projection — which is precisely why `wf` must be **kept coupled** with the residual (Verdict-3),
not pulled out uniformly.

**PIN-6 the hardest lemma — the coupled weighted Schur-projector estimate.** (∗) is the sole substantive
open content. It must:
- keep `wf` (pivot weight) COUPLED inside the A_cor integral — `sup_{A_cor}` pull-out is UNSOUND (Verdict-3;
  Codex Q4: "a supremum pull-out is unsound: along A=tA₀ the divisor scales t^{−ab} and projector constants
  may blow up near rowspace alignment"). `brickd_coupled.py` (w=0, diverges) vs `brickd_coupled2.py` (w>0,
  reaches T2) is the exact witness.
- be per-exponent: `C_j < ⊤` for each c' strictly below T2, `C_j → ∞` as c' → T2 (log endpoint). Do NOT
  claim an endpoint-uniform C_j. The mountain runs strictly below T1 ≤ T2, so per-exponent suffices
  (shellj §4/§5).
- Tonelli reorders (z,C,A_cor) freely, but the integrals do NOT factor — the alignment of Q_b's rowspace to
  Q_p's couples A_cor to Q_p(z) (Codex Q4). The estimate is genuinely joint; the numerics (`brickd_coupled2.py`,
  b=2/k=2) confirm the joint (∗) reaches T2. The cheapest formal handle (Codex): dominate the residual using
  `wf`'s floor on the pivot projection + the det-Gram spread, on the a.e. full-rank chart.

This lemma is what the wallfin docstring calls "the reduced-chain/pivot induction" and what Codex names "the
coupled weighted Schur-projector estimate — the hardest sub-step." It is LABOUR (verified true, mechanism
mapped), not a wall.

## 5. Boundary regimes (PIN-7)

- **Log borderline c' = ab/2** (shifted exponent e = c'−ab/2 = 0): the corner radial integral
  `∫_Γ(w+‖·‖²)^{−ab/2} ≍ 1 + log(1/w)` (Codex Q5, EXACT). The clean shift (∗) is stated for `ab/2 < c'`
  (matching `shell_corankPivot_coupled_le`'s `hc'` and `deeperFlag_shell_le`'s `hc'`). The sub-regime
  `c' ≤ ab/2` (less-singular corner) routes through a **cruder no-shift bound** `∫_Γ(w+…)^{−c'} ≤ C·w^{−c'}`
  (Codex Q5; `shell_corankPivot_coupled_le` docstring same). This is a separate, easier branch — the head
  split at those shells is not near the corner singularity.
- **j = r (a = 0, ab = 0):** NO free corner, no det gain, no inductive progress — a **separate base case**
  (`jreqbuild` thread), not a limit of the a>0 argument (Codex Q5). The k>1 design is for `2 ≤ j < r`
  (equivalently a ≥ 1, b ≥ 2), which is where the corank Schur peel has content.

## 6. Decorrelated Codex (conclusion WITHHELD; prompt framed "argue whichever direction")

`codex/brickd-design-{prompt,answer}.md` (xhigh, no repo access). Independent derivation, CONCURS on the
load-bearing structure and CONTRIBUTED the mechanism correction:
- **Q1 [FACT]** σ_min-collapse over-counts for k>1; no `∏λ_i^{−a/2}` factorization of the front-B integral.
- **Q2 [FACT]** the Schur identity + the transverse Schur complement is the honest weak-determinant, NOT the
  bare corank Gram (with an independent counterexample). **This is the correction beyond brickdfin.**
- **Q3 [INFERENCE]** mechanism (II) is complete IFF the coupled Schur-projector estimate is proved; det-Gram
  integrability alone is insufficient; mechanism (I) is then unnecessary.
- **Q4 [FACT]** the coupled estimate is the hard step; uniform-C pull-out unsound; integrals don't factor.
- **Q5 [FACT]** log at c'=ab/2; no-shift for c'<ab/2; a=0 a separate base case.
- **Q6 [INFERENCE]** hybrid Schur-led; hardest lemma = the coupled estimate; per-point algebraic minor charts,
  no global SVD.
- **Codex's "likeliest break"** (verbatim): "treating det(Q_bQ_bᵀ) as though it controlled pivot–corank
  transversality." — exactly Verdict-3. My `brickd_coupled.py`/`brickd_coupled2.py` is the settling test
  Codex proposed (near-y=0 joint local integral).

## Close

- **Firmest result.** `frobSqBlockFull_lt_top` is TRUE at its stated threshold `2c' < minAdm_red + ab` = 2·T2
  (numerically confirmed finite up to T2, divergent above, off-shell — the z-integration spreads the
  transversality corner). The build route is the **row-split corank-Schur peel** (mechanism II), NOT the
  front-B spectral peel: `pivotDomLHS_eq_blockFront` → `blockFront_rowSplit` → `{IsUnit P}` shear →
  `shell_corankPivot_coupled_le` (det-Gram Jacobian ab/2 + coupled Schur residual) → **the coupled weighted
  Schur-projector estimate (∗)** bounding the residual by the reduced comparator via the shorter-chain IH.
  All primitives banked except (∗). Mechanism correction pinned: transverse Schur complement, pivot weight
  coupled.
- **Most likely to break it.** (i) A builder attacking the literal `stackedGram_flagPeel_le` (front-B
  spectral, multi-weak σ_min peel) will hit the multi-scale collapse wall for k>1 — avoid by row-splitting.
  (ii) Pulling the corank charge out uniformly (`sup_{A_cor}`) is UNSOUND (diverges as A_cor→0) — keep `wf`
  coupled. (iii) Targeting T2-endpoint-uniform C — only per-exponent C_j holds; the mountain needs only
  strict c'<T1. (iv) The `c' ≤ ab/2` and `j=r` regimes are SEPARATE branches — do not fold them into (∗).
- **Next.** The build tide formalizes (∗) on the a.e. full-corank-rank chart (`corank_survival_ae`),
  keeping `wf` coupled, per-exponent C_j, for `ab/2 < c'` and `2c' < minAdm_red + ab`; then assembles
  `pivotDomLHS_eq_blockFront`/`blockFront_rowSplit`/`shell_corankPivot_coupled_le` + (∗) → discharge the
  `frobSqBlockFull_lt_top` sorry. One optional pen-and-paper follow-on: pin the exact per-`(u,a,b)` reduced
  form of the pivot weight `wf` (the P/B₁₂ front-box → reduced comparator sub-step, §4) so the (∗) statement
  names `wf` precisely — the charge arithmetic (T2 = ½(minAdm_red+ab)) is already verified.

# T-Obl3b corner-shrink chart cert — the §6 bordered-Gram primitive does NOT stand; the corner-shrink is a DEEPER-CUT re-peel + PSD weak-elimination (bordered-Gram is diagnostic, not load-bearing)

**Seat:** pen-and-paper WITNESS (chart-correctness adjudication + primitive correction),
genm-sj5-domination, Stage 2. **Date:** 2026-07-13. **NO Lean, NO build.** Exact algebra
(Cauchy–Binet factorisation, Schur/row-peel Jacobian, PSD-det monotonicity, symbolic exponent
counting) + MC guide only. Decorrelated `local-codex-consult` (xhigh, my conclusion WITHHELD):
`codex/tobl3b-cornershift-{prompt,answer}.md`. Reproducible: `scripts/tobl3b/cornershift_diag.py`
(FACT 1/2/3), `scripts/tobl3b/cornershift_verify.py` (row-peel Jacobian + deeper-cut PSD chain).

**Anchor:** `(3,3,3)@t★=1` — `a=b=2`, `r=min(a,b)=2`, `M₂=3`; shell `j=1` (one weak singular value of
`Z<ε`, two strong `≥ε`). Reduced dims claimed by the design: `(a−j,b−j,M₂−j)=(1,1,2)`; charge
`C₁=(a−j)(b−j)+minAdm(redChain 2 (3,3,3))=1+6=7=minAdm(3,3,3)` (tight; both `t=1`,`t=2` binding).

**Consumed / read (statements, not re-derived):** `RouteMSJProductTube`
(`detGram_lintegral_lt_top (hrn:r≤n)(a<n−r+1)`, `measurePreserving_rowsEquiv`, `gram_rowsEquiv`),
`RouteMSJBorderedGram` (`borderedGram_det`, `borderedGramSchur`, `borderedGramSchur_nonneg` — the
ONE-STEP Schur recursion), `RouteMSJGramRowPeel` (`gramSchurSeq`, `gramDet_eq_prod` — the ∏‖qᵢ^⊥‖²
iterate, landed sorry-free 2026-07-13 00:35), `RouteMSJShellUniform` (`uniformWenn_le` — shell-0 PSD-monotone bound),
`RouteMSJShellCharge` (`flagCharge_ge`, `freedCorner_eq_peelCharge`, `deeperCut_le`,
`flagShift_lt_carrierThreshold`), `RouteMSJShellCover` (`lintegral_le_sum_finCover`, `singularShell`,
`singularShell_iUnion`), `RouteMSJCornerComparator` (`cornerComparator`, `cornerComparator_decLoss`,
`cornerComparator_adm`), `RouteMSJDetMono` (`det_le_det_of_posSemidef_sub`); the pin/reformulation certs
(`tobl3b-pin-cert.md` §1–§2, `tobl3b-reformulation-cert.md` §5–§6) whose primitive this cert corrects;
`RouteMLayerSplit` (`redChain`, `minAdm`, `peelCharge`), `RouteMSJDecoratedCharge` (`peelCharge`,
`minAdm_le_peelCharge_add_redChain`), `RouteMSJDecorated` (`carrierThreshold`, `carrierThreshold_shift`).

---

## ★ VERDICT — the cert-§6 primitive does NOT stand. State the correction LOUDLY.

**The §6 claim** — "the corner-shrink `(a,b)↦(a−j,b−j)` is realised by a change-of-variables whose
Jacobian is the `|strong (M₂−j)-minor|` of `A_cor·U`, supplied by iterating the bordered-Gram recursion
`det(QQᵀ)=∏‖qᵢ^⊥‖²`, yielding the reduced weight at dims `(a−j,b−j,M₂−j)`" — **is a NON-SEQUITUR and
must be corrected.** Three exact facts, each reproducible, decorrelated-Codex-confirmed:

```
FACT A (the object §6 names IS now banked as a correct identity — but is the WRONG TOOL).
   RouteMSJGramRowPeel landed sorry-free at 2026-07-13 00:35 (mid-session; AxCheck M3), providing
   gramSchurSeq v i (= borderedGramSchur of the (i+1)-prefix) and gramDet_eq_prod
   ((gram ℝ v).det = ∏ᵢ gramSchurSeq v i, for linearly independent v) — the iterated borderedGram_det,
   i.e. det(QQᵀ)=∏‖qᵢ^⊥‖².  This is a CORRECT, reusable determinant identity.  Its docstring states the
   intended use: "the concrete det(XXᵀ)=∏… form is a two-line corollary … consume gram_rowsEquiv +
   gramDet_eq_prod … alongside the CoV" — i.e. it is slated to be the corner-shrink CoV Jacobian.
   That intended use is exactly the §6 primitive this cert refutes: the identity is right, but as a CoV
   it does NOT realise the corner-shrink (FACT C).  [Earlier draft said these names were absent — stale;
   they were created at 00:35.  The verdict is unchanged and strengthened: the phantom is now a real but
   wrongly-purposed lemma.]

FACT B (weak-direction elimination gives the WRONG, DIVERGENT reduced weight — 3 routes agree).
   At the cut-t★ level the residual weight is  Wenn(Z)=∫_{A_cor∈box(b×M₂)} det((A_cor Z)(A_cor Z)ᵀ)^{−a/2}.
   Eliminating the j weak directions of Z (M₂→M₂−j) — by the Cauchy–Binet strong minor, by row
   Gram–Schmidt, OR by PSD-monotonicity ZZᵀ⪰ε²P_strong — ALL give a reduced weight at
      rows = b,  cols = M₂−j,  exponent = a        (NOT (b−j, M₂−j, a−j))
   which converges iff a < (M₂−j)−b+1 = M₂−j−b+1.  ANCHOR: 2 < 1  → FALSE (divergent).
   This is the design's OWN "crude" condition and the reformulation cert's OBSTRUCTION 3.
   The pin cert's exact script jacobian_factor.py PRODUCES exactly this: det^{−a/2}→|det(B_{12})|^{−a}
   with B_{12}=A_cor·U_s a b×(M₂−j)=2×2 block at exponent a=2 — its comment "reduced (b−j)-row weight
   at exponent (a−j)/2" is CONTRADICTED by the algebra in the same file.

FACT C (the bordered-Gram ROW-PEEL does shrink rows AND exponent — but leaks a DIVERGENT transverse
   factor, so it does not close the fixed cut either).  Peeling one Gram row via q_b = λ·(q_1..q_{b−1}) + v,
   v ⟂ rowspan, is the EXACT identity (verified symbolically, cornershift_verify.py):
      det(G_b) = det(G_{b−1})·‖v‖²      and      dq_b = det(G_{b−1})^{1/2} dλ dv,   so
      det(G_b)^{−a/2} dq_b = det(G_{b−1})^{−(a−1)/2} · ‖v‖^{−a} · dλ dv.
   Residual Gram: rows b−1, exponent a−1.  BUT the transverse factor ‖v‖^{−a} over v∈ℝ^{n−b+1} has
   ∫‖v‖^{−a} = ∞ at the anchor (a=2, transverse dim 2 → log-divergent), and the λ-fibres are
   uncontrolled.  So the row-peel merely RELOCATES the b-corank divergence into a transverse
   divergence: no net gain, no bounded constant.  (Codex Q2, independently re-derived.)
```

**The CORRECTION (the mechanism that actually realises the corner-shrink):** the shrink
`(a,b)↦(a−j,b−j)` is **NOT a Jacobian on the cut-`t★` residual `Wenn(Z)`**. It is a **re-peel at the
DEEPER binding cut `t★+j`**, where the peel's definitions *themselves* give corank rows `b−j` and freed
corner height (hence Γ-Gaussian exponent) `a−j`. At the deeper cut the weak-direction elimination
(`M₂→M₂−j`) is the **banked PSD-monotonicity** `det_le_det_of_posSemidef_sub` — exactly the mechanism of
the LANDED `uniformWenn_le`, generalised from `1` to the strong-projection `P_strong` — and it lands
the reduced weight at dims `(b−j, M₂−j)` exponent `a−j`, **strictly convergent** `a−j < M₂−b+1` (ANCHOR
`1 < 2`). **Bordered-Gram is NOT load-bearing** (its role is diagnostic bookkeeping); **PSD-monotonicity
at the re-indexed `(b−j)`-corank level suffices.** The charge `C_j` is realised by the cut-CHOICE
(banked `flagCharge_ge`+`freedCorner_eq_peelCharge`), not by the chart Jacobian.

**The genuine remaining risk (build-order, not labour-vs-wall):** the cut-`t★` shell-`j` integrand — the
reformulation cert §3 LHS, whose "shape is UNCHANGED" — has `Wenn(Z)~σ_min(Z)^{−1}` (FACT 3 below) and
is (strong evidence) **DIVERGENT** for `j≥1`; a finite comparator cannot dominate a divergent integral,
so the shrink CANNOT be internal to a CoV on it. The T-peel spine must **stratify `Z` into shells FIRST
and peel at cut `t★+j` on shell `j`** (partial `(a−j)×(b−j)` corner), NOT peel the full `a×b` corner at
`t★` and then stratify. Absent the cut-change, an unbanked measure-disintegration is required (Codex Q4).

---

## 1. The corrected CoV chain (task deliverable #1) — exact, per shell `j`, `1 ≤ j ≤ r−1`

On shell `S_j = {exactly j singular values of Z below ε}` (single-`ε`, banked `singularShell`), the
shell-`j` leg re-charts to the deeper comparator by the following **four** steps. The deeper cut is
`u := t★+j` (legal by `deeperCut_le`; `a_u := M₀−u = a−j`, `b_u := M₁−u = b−j`).

**Step 1 — re-peel the freed corner at cut `u=t★+j` (NOT `t★`).** Free the `(a−j)×(b−j)` sub-corner
`Γ_u`; the Γ_u-Gaussian corner peel (`freedSchurLoss_inner_peel_le` / `_bounded_le` at the reduced
corner) yields charge `½(a−j)(b−j)` and residual `det(Q_u Q_uᵀ)^{−(a−j)/2}`, where `Q_u = A_u·Z` and
`A_u` is the `(b−j)×M₂` corank block at cut `u`. This is the ONLY source of the corner-shrink; it is a
change of the CUT, definitional, `charge` banked (`freedCorner_eq_peelCharge`, `flagCharge_ge`).

**Step 2 — weak-direction elimination by PSD-monotonicity (generalising `uniformWenn_le`).** On `S_j`,
`ZZᵀ ⪰ ε²·P_strong`, `P_strong := U_s U_sᵀ` the rank-`(M₂−j)` strong projection (`U_s : M₂×(M₂−j)`,
`U_sᵀU_s=1`). Loewner congruence `A_u(ZZᵀ−ε²P_strong)A_uᵀ ⪰ 0` (`PosSemidef.mul_mul_conjTranspose_same`,
verified `min eig ≥ 0`) + `det_le_det_of_posSemidef_sub` give, for a.e. full-row-rank `A_u`:
`det((A_u Z)(A_u Z)ᵀ) ≥ ε^{2(b−j)}·det((A_u U_s)(A_u U_s)ᵀ)`, hence (antitone negative power)
`det(Q_u Q_uᵀ)^{−(a−j)/2} ≤ ε^{−(a−j)(b−j)}·det((A_u U_s)(A_u U_s)ᵀ)^{−(a−j)/2}`. The uniform factor
`ε^{−(a−j)(b−j)}` is weak-SV-free (ANCHOR `ε^{−1}`). NO bordered-Gram, NO Cauchy–Binet.

**Step 3 — reduce the strong block to `detGram_lintegral_lt_top` at the shrunk dims.** `A_u·U_s` is
`(b−j)×(M₂−j)`. Extend `U_s` to `U ∈ O(M₂)`; the right-mult `A_u ↦ A_u·U` is measure-preserving
(orthogonal per row — the LEGITIMATE role of `measurePreserving_rowsEquiv`/right-orthogonal CoV), so
`∫_{A_u∈box((b−j)×M₂)} det((A_u U_s)(A_u U_s)ᵀ)^{−(a−j)/2} ≤ C_box·∫_{X∈box((b−j)×(M₂−j))} det(X Xᵀ)^{−(a−j)/2}
< ⊤`, the last finite by **`detGram_lintegral_lt_top`** at `r=b−j`, `n=M₂−j`, exponent `a−j`, condition
`a−j < (M₂−j)−(b−j)+1 = M₂−b+1` (ANCHOR `1 < 2` STRICT). `C_box` bounds the box distortion + the
integrated-out `j` weak columns (both bounded, `Z`-independent).

**Step 4 — the reduced comparator + charge.** Drop the nonneg residual `(w+R)^{−e} ≤ w^{−e}` (`R≥0`),
`w = frobSq(Γ'_u·Z)` the `cornerComparator (redChain u M) k jc` loss (`cornerComparator_decLoss`), giving
`(shell-j leg) ≤ const(ε)·(cornerComparator (redChain (t★+j) M) k jc integrand at c'−½(a−j)(b−j))`,
`const(ε) = Cresid·ε^{−(a−j)(b−j)}·C_box·[∫_X det(XXᵀ)^{−(a−j)/2}]`. Closed by `lintegral_mono` + the
arity-`(L+1)` decorated IH (`cornerComparator_adm`); IH fires by `flagShift_lt_carrierThreshold`
(`c'−½(a−j)(b−j) < carrierThreshold(redChain (t★+j) M)`).

## 2. What the product residual `gramSchurSeq`/`borderedGramSchur` actually is (task #2) — CORRECTION

The task's premise "the `∏‖qᵢ^⊥‖²` factors of `det(QQᵀ)` **become** the `|strong (M₂−j)-minor|` Jacobian
of the corner-shrink CoV" is **false**, on three counts:

- **`gramSchurSeq` / `gramDet_eq_prod` (banked 00:35, `RouteMSJGramRowPeel`) are a correct identity but
  NOT the corner-shrink Jacobian** (FACT A). `gramDet_eq_prod : (gram ℝ v).det = ∏ᵢ gramSchurSeq v i`
  iterates `borderedGram_det`; `borderedGramSchur v = ⟪x,x⟫ − w⬝ᵥ(G⁻¹*ᵥw) = dist(v_last, span)²`,
  `borderedGramSchur_nonneg ≥ 0`. All CORRECT, sorry-free. The `|strong (M₂−j)-minor|` and the
  `∏‖qᵢ^⊥‖²` are DIFFERENT objects (the former a Cauchy–Binet term, the latter a Gram–Schmidt residual
  product); neither, used as a CoV Jacobian at the cut-`t★` level, realises the corner-shrink.

- **The strong-minor route gives exponent `a` on a `b×(M₂−j)` block, not `(a−j)` on `(b−j)×(M₂−j)`**
  (FACT B). The **explicit anchor Jacobian** from the Cauchy–Binet factorisation
  (`jacobian_factor.py`, exact): with `B=A_cor·U` (`2×3`), `det(Q_bQ_bᵀ)|_{σ₃→0} = det(B_{12})²·σ₁²σ₂²`,
  `det(B_{12}) = b₁₁b₂₂ − b₁₂b₂₁` — a `b×(M₂−j)=2×2` minor at exponent `a=2`. Reduced weight
  `∫|det(B_{12})|^{−a}` at dims `(b,M₂−j)=(2,2)` exponent `2`, condition `2<1` — DIVERGENT.

- **The bordered-Gram row-peel Jacobian is `det(G_{b−1})^{1/2}` with a divergent transverse factor**
  (FACT C, the exact identity). Peeling one corank row at the anchor (`b−1=1`):
  `det(G₂)^{−1} dq₂ = det(G₁)^{−1/2}·‖v‖^{−2}·dλ dv`, `v = q₂^⊥ ∈ ℝ²`; `∫‖v‖^{−2}` log-**diverges**. So
  the `∏‖qᵢ^⊥‖²` iterate produces the right `(b−1, a−1)` counts but leaks an uncontrolled `‖v‖^{−a}`
  — it does **not** furnish a bounded Jacobian and does not realise the corner-shrink.

**The Jacobian that DOES land the reduced weight** is the PSD-monotonicity factor `ε^{−(a−j)(b−j)}`
(Step 2, ANCHOR `ε^{−1}`) times the bounded orthogonal-CoV distortion `C_box` (Step 3) — no determinant
minor of `A_cor·U` at all. Explicit at the anchor: `det(Q_u Q_uᵀ)^{−1/2} ≤ ε^{−1}·‖A_u U_s‖^{−1}`,
`A_u U_s ∈ ℝ^{1×2}` (a single row), `‖A_u U_s‖^{−1} = det((A_u U_s)(A_u U_s)ᵀ)^{−1/2}` — the `(b−j)×(M₂−j)
= 1×2` det-Gram at exponent `a−j=1`. (When `b−j ≥ 2`, `borderedGram_det` MAY be used to peel the `(b−j)`
strong corank rows inside `detGram_lintegral_lt_top` — but even there the banked lemma already integrates
the full `(b−j)`-row Gram directly, so bordered-Gram remains optional, not load-bearing.)

## 3. The `(a,b)→(a−1,b−1)` shrink is the DEEPER CUT, not a `rowsEquiv` measure CoV (task #3) — CORRECTION

The task's premise "the per-level `(a,b)→(a−1,b−1)` corner-shrink is realised as a MEASURE CoV consuming
`measurePreserving_rowsEquiv`" is **false**: `measurePreserving_rowsEquiv` is
`(Fin r→Fin n→ℝ) ≃ᵐ (Fin r→EuclideanSpace ℝ (Fin n))` — it **reindexes/identifies rows with Euclidean
tuples, measure-preservingly; it cannot DELETE `j` rows** (Codex Q4: "row reindexing merely permutes rows
and cannot delete `j` of them"). The dimension drop `b→b−1`, `a→a−1` is **definitional**: at cut `t★+1`
the corank block has `b−1` rows and the freed corner has height `a−1` (`a_u=M₀−u`, `b_u=M₁−u`). Its
`charge` is `peelCharge M (t★+j) = (M₀−t★−j)(M₁−t★−j) = (a−j)(b−j)` (banked `freedCorner_eq_peelCharge`).
`measurePreserving_rowsEquiv` (and a right-orthogonal measure-preserving map) enters ONLY inside Step 3,
to transport the strong block to `detGram_lintegral_lt_top`'s Euclidean-row form — never to shrink dims.

## 4. The charge `C_j` adds EXACTLY (task #4) — YES, via the cut-choice (banked)

`C_j = (a−j)(b−j) + minAdm(redChain (t★+j) M) ≥ minAdm M`, TIGHT at `j=0` and (anchor) `j=1`, is the
banked `flagCharge_ge` = `minAdm_le_peelCharge_add_redChain` at the deeper cut `u=t★+j`
(`freedCorner_eq_peelCharge`). ANCHOR: `C₁ = (2−1)(2−1) + minAdm(redChain 2 (3,3,3)) = 1 + minAdm(2,3) =
1 + 6 = 7 = minAdm(3,3,3)`; `½C₁ = 3.5 = carrierThreshold(3,3,3)`, so `c' < 3.5 ⟹ c'−½·1 < 3 =
carrierThreshold(2,3)` STRICT — the arity-`(L+1)` IH on `(2,3)` fires (`flagShift_lt_carrierThreshold`).
**The chart REALISES this charge by the cut-choice** (Step 1 gives `½(a−j)(b−j)`; Steps 2–3 make the
reduced weight FINITE so no charge leaks; the IH supplies `½minAdm(redChain(t★+j))`). The chart does NOT
assert `C_j ≥ minAdm`; it consumes the banked `flagCharge_ge`. Swept `C_j ≥ minAdm`, 0/125 violations
(`cornershift_diag.py`, reproducing `verify_flag.py`).

## 5. Width-general Lean-shape statements (matching banked names) — what the tide OWES

The corrected build replaces the reformulation cert §6's "corner-shrink minor CoV" with two clean pieces
on the banked `uniformWenn_le`/`det_le_det_of_posSemidef_sub`/`detGram_lintegral_lt_top` — **no
bordered-Gram**. For a binding cut `t★`, shell `1 ≤ j ≤ r−1`, `u=t★+j`, `a_u=a−j`, `b_u=b−j`:

**OWED-1 — `uniformWenn_proj_le` (NEW; generalises `uniformWenn_le` from `1` to a strong projection).**
```
theorem uniformWenn_proj_le {a' b' M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b' ≤ m)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε^2) • (U_s * U_sᵀ)).PosSemidef) :        -- ZZᵀ ⪰ ε²·P_strong on shell j
    (∫⁻ A in matBox b' M₂ 1, ENNReal.ofReal (((of A * Z)*(of A * Z)ᵀ).det ^ (-(a':ℝ)/2)))
      ≤ ENNReal.ofReal (ε ^ (-((a':ℝ)*b')))
        * ∫⁻ A in matBox b' M₂ 1, ENNReal.ofReal (((of A * U_s)*(of A * U_s)ᵀ).det ^ (-(a':ℝ)/2))
```
Instantiate at `a'=a−j`, `b'=b−j`, `m=M₂−j`. Proof: `uniformWenn_le` VERBATIM with `1 → P := U_s U_sᵀ`
(`A·(ε²•P)·Aᵀ = ε²•((A U_s)(A U_s)ᵀ)`, `det_smul` gives `(ε²)^{b'}`, `posDef_gram_of_rank_eq (of A · U_s)`
for full-rank `A U_s`). Clean LABOUR; the only edit is `Matrix.mul_one → the P-congruence`.

**OWED-2 — `strongBlock_lintegral_lt_top` (NEW, small; the reduced weight at the shrunk dims).**
```
theorem strongBlock_lintegral_lt_top {b' m M₂ : ℕ} (U_s : Matrix (Fin M₂) (Fin m) ℝ)
    (hUs : U_sᵀ * U_s = 1) (hbm : b' ≤ m) {a' : ℝ} (ha' : a' < (m:ℝ) - b' + 1) :
    (∫⁻ A in matBox b' M₂ 1, ENNReal.ofReal (((of A * U_s)*(of A * U_s)ᵀ).det ^ (-a'/2))) < ⊤
```
Route: extend `U_s` to `U ∈ O(M₂)` (`Matrix.exists_orthogonal_extension`-style), right-mult by `U`
measure-preserving, integrate out the `m→M₂` weak columns (bounded box factor), reduce to
`detGram_lintegral_lt_top (hrn : b' ≤ m) (ha' : a' < m−b'+1)`. Instantiate `a'=a−j`, `b'=b−j`, `m=M₂−j`;
`a−j < (M₂−j)−(b−j)+1 = M₂−b+1` STRICT for `j≥1` at a binding cut (`a ≤ M₂−b+1`, banked; 0/3161).

**OWED-3 — `deeperFlag_shell_le` (the mountain, corrected LHS/route).** The LHS is the **cut-`u`**
integrand (freed corner `(a−j)×(b−j)`, corank block `(b−j)×M₂`), produced by the T-peel spine peeling at
`t★+j` on `S_j` — **NOT** the cut-`t★` integrand of reformulation §3. Assembly: Step-1 freed-corner peel
(`freedSchurLoss_inner_peel_le`) → OWED-1 → OWED-2 → drop residual → `cornerComparator (redChain (t★+j) M)`
at `c'−½(a−j)(b−j)` (banked `cornerComparator_decLoss`, `cornerComparator_adm`, `flagShift_lt_carrierThreshold`).

**Cover / saturated / borderline (unchanged, banked):** single-`ε` exhaustive cover
(`singularShell_iUnion`, `lintegral_le_sum_finCover`); shell-0 (`uniformWenn_le`, borderline `θ<1`);
saturated `S_r` (`(a−r)(b−r)=0`, no det weight — `tobl3b-saturated-anb-pin-cert.md` branch untouched).

## 6. Where `borderedGram_det` / `gramDet_eq_prod` genuinely stand, and where they do not

`borderedGram_det` / `borderedGramSchur_nonneg` / `gramDet_eq_prod` (`RouteMSJGramRowPeel`) are **correct,
banked, reusable** determinant facts. They are **not** the T-Obl3b corner-shrink primitive: (i) the
corner-shrink is the cut-choice, not a Jacobian;
(ii) the weak-elimination is PSD-monotonicity, not Schur; (iii) the fixed-cut row-peel they enable leaks a
divergent `‖v‖^{−a}` (FACT C). Their only possible T-Obl3b role is a convenience inside OWED-2 when
`b−j ≥ 2` (peel strong corank rows), but `detGram_lintegral_lt_top` already integrates the full `(b−j)`-row
Gram, so even there they are optional. **The reformulation cert's "bordered-Gram is the irreducible
primitive" rests on computing PSD-monotonicity at the WRONG level** (keeping the full `a×b` corner, cut
`t★`), which spuriously fails (OBSTRUCTION 3); at the correct level (cut `t★+j`) PSD-monotonicity gives the
design convergence directly.

## 7. Decorrelated Codex verdict (my conclusion WITHHELD from the prompt)

`codex/tobl3b-cornershift-{prompt,answer}.md` (xhigh; the objects + banked tools + the prior design note
supplied; my deeper-cut/PSD conclusion WITHHELD). **Codex CONCURS, decorrelated, and independently
derived the correction:**
- **Q1 [exact]** weak-elimination gives rows `b`, cols `M₂−j`, exponent `a`; diverges (`a<M₂−j−b+1` false
  at anchor). (= my FACT B.)
- **Q2 [exact]** the bordered-Gram row-peel gives rows `b−1`, exponent `a−1` with Jacobian
  `det(G_{b−1})^{1/2}` — but leaves `‖v‖^{−a}` transverse (`∫|v|^{−2}=∞` at anchor) + uncontrolled λ-fibres;
  "does not supply a bounded constant." (= my FACT C, independently re-derived.)
- **Q3 [exact]** `Wenn(Z)` blows up `~σ_min^{−1}`; the `(b−j)`-row/`(a−j)`-exponent version stays bounded.
  (= my FACT 3.)
- **Q4 [inference]** "a valid direct mechanism is instead to re-peel at `t★+j`, where the definitions
  themselves give corank rows `b−j` and corner height — hence determinant exponent — `a−j`. Row reindexing
  merely permutes rows and cannot delete `j` of them. Without permission to change the cut, an additional
  measure-disintegration theorem … is required; none is banked."
- **Q5 [inference]** "At the re-indexed cut `t★+j`, PSD monotonicity directly produces rows `b−j`, columns
  `M₂−j`, exponent `a−j`. Thus bordered-Gram is unnecessary … its true role is diagnostic."
- **VERDICT:** "bordered-Gram is NOT load-bearing; the corner-shrink is a re-peel at `t★+j` followed by PSD
  weak-direction elimination." No inference of mine was fed in; the concurrence is decorrelated.

---

## Close

- **Firmest result (exact + decorrelated).** The §6 corner-shrink primitive does NOT stand. The named
  object (`gramSchurSeq`/`gramDet_eq_prod`, banked 00:35) is a correct identity but the WRONG tool for the
  corner-shrink; the weak-direction elimination the primitive invokes gives the divergent weight
  `(b, M₂−j, a)` (FACT B, the pin cert's own `jacobian_factor.py`); the `gramDet_eq_prod` row-peel it
  iterates leaks a divergent transverse `‖v‖^{−a}` when used as a fixed-cut CoV (FACT C, exact). **The corner-shrink
  `(a,b)→(a−j,b−j)` is the DEEPER-CUT re-index (banked charge), and the weak-elimination is banked
  PSD-monotonicity at the `(b−j)`-corank / `(a−j)`-exponent level, landing the strictly-convergent reduced
  weight `(b−j, M₂−j, a−j)` via `detGram_lintegral_lt_top`. Bordered-Gram is diagnostic, not load-bearing.**
- **Most likely to break it / the genuine open part.** The cut-`t★` shell-`j` integrand (reformulation §3
  LHS, `Wenn(Z)~σ_min^{−1}`) is (strong evidence, not yet a full divergence proof of the coupled integral)
  **divergent** for `j≥1`; if so, no finite comparator can dominate it and the shrink cannot be internal.
  **The T-peel spine (tile #5) must stratify `Z` FIRST and peel at `t★+j` per shell** — a build-order
  correction, not the "internal CoV, LHS unchanged" of reformulation §3/§6. If the spine cannot re-choose
  the cut, an unbanked measure-disintegration is required (Codex Q4) — that would be the one genuine wall.
- **Next.** (a) The tide builds OWED-1/OWED-2/OWED-3 on `uniformWenn_le`+`det_le_det_of_posSemidef_sub`
  +`detGram_lintegral_lt_top` (no bordered-Gram). (b) A pen-and-paper confirmation that the T-peel spine
  CAN peel at `t★+j` on `S_j` (does the FaithfulSJAt parent admit the deeper cut as its peel cut on the
  shell?) — this is the load-bearing open question, and the one thing that turns "labour" into "wall" if
  it fails. Recommend that check before the mountain build.

# Brick D formalization — design-first decomposition of the joint incidence-rank resolution

**Seat:** lean-formaliser, aoyagi-full Stage 2. **Date:** 2026-07-14. Branch `genm-sj5-brickdbuild`.
Source of truth: `genm-incidencepp/incidence-cert.md` (the PROVEN estimate) + its `inc_sweep.py` exponent cert.
This is the design; the build follows.

## Target (matches the existing `headSplit_domination` stub, with `hcT`)
Fresh partial-floor `headSplit_domination` → `deeperFlag_shell_le` at `ab/2 < c' < carrierThreshold M`:
`shellSpineIntegrand M (t+j) κ ε r ⟨j⟩ c' ≤ C_hle · deeperFlagCoreIntegrand M (t+j) ![1] ![minAdm−1] Zf 0 genBox c'`,
then the banked L1 `deeperFlag_shell_core_le` + spineToCore + `cornerComparator_adm` close `deeperFlag_shell_le`.

**Scope (LOAD-BEARING, cert §Verdict-2):** `a+b ≤ M₂` (= `hcvg ∧ hmM`, already in the stub). Without it the
corank-Gram `∫det(QbQbᵀ)^{−a/2}` diverges. Thread it everywhere.

## The three non-negotiable build-guards (cert + controller)
1. **JOINT (z, A_cor, front) resolution, NOT per-z.** Pointwise-in-z is FALSE (rank-drop Qp ⟹ δ^{5−2q}
   blow-up, witness (3,3,5)@u=2). The z-integration participates: the Qp rank-stratum codim absorbs the
   front blow-up.
2. **Scope `a+b ≤ M₂`** threaded (else det-Gram diverges).
3. **det-Gram COUPLED** — no `sup_{A_cor}` pull-out (unbounded); it rides inside the incidence tube.

## The object after the banked front-end (cert §1)
Banked reductions (row-split `blockFront_rowSplit` + `{IsUnit P}` shear + Γ-integration via
`shell_corankPivot_coupled_le`) take shellSpineIntegrand → the cert's `G`:
`G = ∫_z ∫_{A_cor∈S_j(z)} det(QbQbᵀ)^{−a/2}·[∫_{P,B,C}(‖P·Qp+B·Qb‖²_F + ‖C·Qp(I−Πb)‖²_F)^{−q}]`, q=c'−ab/2.
Ratio-trick: `G ≤ K·comparator` reduces (comparator finite by IH on redChain, comparator≠0 banked) to
**`G < ⊤` for c'<T1** — the joint incidence-rank resolution finiteness. THIS is the whole hard content.

## Decomposition into tides (the joint resolution `G < ⊤`)

| # | Lean piece | status | notes |
|---|---|---|---|
| A | shellSpine → shell-j hsQ-box reindex (replaces false full-floor `shellSpine_le_hsQ_box`) | NEW, medium | measure-preserving `hsSplit` (banked MP) + carry the `singularShell j` constraint (same singular values). |
| B | row-split + {IsUnit P} shear + Γ-integration → `G` | banked (`blockFront_rowSplit`, `shell_corankPivot_coupled_le`) + wiring | the det^{−a/2} + shift q + coupled transverse-Schur residual. |
| C | **minor-chart CoV** Qb=D[I|X] + transverse-Schur monomialization ‖Qp(I−Πb)‖²=tr(W(I+XXᵀ)⁻¹Wᵀ) | NEW, HEAVY | GL_b minor chart; measure-preserving CoV on A_cor box; the pi-diamond CoV pattern (CLAUDE.md). Jacobian \|det D\|^d. |
| D | output shear H=PU+BD (det-1) + Jacobian \|det D\|^{n−b−a−u} | NEW, HEAVY | pi-space Haar CoV; det factors via det_pi. |
| E | the C_{ℓ,s} strata cover + per-stratum radial finiteness ∫r^{C−1−2q}dr<⊤ for q<C/2 | NEW, HEAVIEST | finite partition into rank(W)/rank(Y) strata; each a banked box-integral (`matBox_frobSq_neg_lintegral_lt_top`, `detGram_lintegral_box_lt_top`). |
| F | exponent cert: min_{ℓ,s} C_{ℓ,s}/2 = T1_q AND T1_q ≤ uM₂/2 | NEW, nat-arithmetic | `inc_sweep.py` verified widths 2..8 EXHAUSTIVELY but NOT proven ∀M — the general nat proof is its own sub-target. |
| G | ratio-trick wrapper (G<⊤ ∧ comparator → domination) | banked pattern (cf. `pivotPeel_domination`) | reuses `exists_finite_mul_of_finite_imp` + comparator≠0. |
| H | general-L lift (Qb = A_cor·Zf, deep floor) via `uniformWenn_proj_le` | banked + wiring | the cert works the L=0 leaf; the deep floor lifts it. |

## Scale assessment (honest)
This is a **multi-tide programme**, not a single-tide close. Tides A, C, D, E each are substantial new
modules (measure-preserving matrix CoVs with explicit Jacobians + a finite stratification). E + F carry the
analytic core. The banked box-integral finiteness lemmas (`matBox_frobSq_neg_lintegral_lt_top`,
`detGram_lintegral_box_lt_top`) are the per-stratum engines, so no resolution-of-singularities framework is
needed — but the finite stratification + per-chart CoV + Jacobian bookkeeping is genuine labour across
several modules. F (the exponent min ∀M) needs a general nat proof that `inc_sweep.py` only verified for a
finite range.

## LANDED this tide (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)
- `RouteMSJIncidenceChart.lean`: `chartGram_congr` (the minor-chart Gram congruence `(D·[I|X])(D·[I|X])ᵀ =
  D·(I+XXᵀ)·Dᵀ`) and **`det_chartGram`** (the cert §0 load-bearing identity `det(Q_bQ_bᵀ) = (det D)²·det(I+XXᵀ)`).
  This is Codex's decomposition lemma #2 (det part) — the algebraic core the resolution is built around.

## Codex Lean-route verdict (`codex/leanroute-{prompt,answer}`, decorrelated xhigh)
FEASIBILITY: **bounded labour IFF the pen proof supplies explicit pivot/blow-up COORDINATES — not merely
rank-stratum codimensions.** Mathlib has the CoV engine (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`);
no resolution framework needed. 8-lemma decomposition (mine ≈ Codex's): chart cover → minor CoV (det done) →
deep U/W chart → output shear H=PU+BD → **`incidenceCell_lintegral_le` (HARDEST)** → banked box-integrals →
exponent gate `min C_{ℓ,s}/2 = T1_q` → `G<⊤` via `lintegral_le_sum_finCover`.

**THE FORMALIZABILITY RISK (SD-7 flag):** the hardest lemma `incidenceCell_lintegral_le` is the finite
MEASURABLE pivot-neighbourhood/blow-up atlas for the rank-ℓ(W)/rank-s(Y) strata. Mathlib has NO
determinantal-stratification or tubular-neighbourhood API; lower-rank strata are null sets, so the
integration pieces must be explicit blow-up CELLS, not `{rank W = ℓ}`. Codex: "substantial labour, but NOT a
Lean wall IF the explicit chart formulas are known. If the paper proof stops at 'codim C_{ℓ,s} and ≍,' then
the missing stratified-CoV theorem becomes a genuine wall." **incidencepp's cert currently gives codim +
≍, NOT the explicit measurable blow-up charts** — so this sub-step needs incidencepp to supply the explicit
per-stratum blow-up coordinates + Jacobians, else it is a Lean wall.

CHEAPER ALTERNATIVE (Codex): only in the regime `κ := n−b−a−u ≥ 0` — separate D, peel the `ub`-dim H-block,
reduce `YW` to the banked depth-two `routeMBoxThresholdFinite_mnp M0 u d` (ε-interpolation at the borderline
`q=ub/2`). Does NOT cover the general scope (`κ ≤ −1` allowed), where the shrinking H-domain volume is
essential (a fixed-box H gives `|det D|^κ` which diverges near a rank-`(b−1)` D).

## Recommended tide sequence
1. **Tide-F first (nat-arithmetic, decorrelated-checkable):** prove `min_{ℓ,s} C_{ℓ,s}/2 = T1_q` ∀M (or
   isolate it as the exponent certificate). Self-contained, no integrals — the "reusable cert." De-risks E.
2. **Tide-C/D (the CoV kernels):** the minor-chart + shear measure-preserving maps + Jacobians. Reusable.
3. **Tide-E (the strata finiteness):** assemble C/D + F + banked box-integrals into `G < ⊤`.
4. **Tide-A/B/G/H (assembly):** reindex + corank-peel + ratio + general-L lift → `headSplit_domination` →
   `deeperFlag_shell_le`. Retire `shellSpine_le_hsQ_box`.

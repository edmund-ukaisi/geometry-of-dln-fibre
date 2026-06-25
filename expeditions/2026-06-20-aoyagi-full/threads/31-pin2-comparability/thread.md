# Thread 31 — PIN2 comparability re-architecture (the L2 geometric heart)

**Seat:** pen-and-paper (obstruction). **Direction asked:** validate-or-refute the brief's option 2
(weaken `h00/h01/h10` to a two-sided comparability `Sreg ≍ ∑deepestEPivot²`, folding the Y·T leak into
γ₁/γ₂). **Level:** the loss-squeeze germ (the matrix-block / energy-comparability level, below the RLCT
cap). **Verdict: option 2 is UNSOUND.** Both directions of `Sreg ≍ ∑deepestEPivot²` are false by exact
witnesses. The real fix is to read the regular energy off the **FULL product** (which the leaf lemma
`dlnLoss_two_sided_of_frame` already does) and to **not** identify `Sreg` with `∑deepestEPivot²` at all.

All algebra exact (sympy, exact-rational/symbolic). MC used only as a guide and clearly flagged.

---

## The objects (as instantiated for the smallest separating case)

`L = 2`, `H = [2,2,2]`, `r = 1`. Each layer block-split `1 ⊕ (H−r)=1 ⊕ 1`:
`C0 = [[1+X0, Y0],[Z0, T0]]`, `C1 = [[1+X1, Y1],[Z1, T1]]`. `B = corM = [[1,0],[0,0]]`.
Deepest point: all 8 deviations `= 0`. The 8 are independent **raw** chart coordinates
(`X,Y,Z` off the `(reg,spec)` slot through the homeomorphism `regGaugeSlotEquiv`; `T` off the separate
core slot `.2.1`). `split` is a homeomorphism onto a neighborhood, so all 8 are jointly free near 0.

- `Sreg`  = FULL-product reg energy `(P11−1)²+P12²+P21²` of `C0·C1` (what `hconj` + the leaf lemma read).
- `Ereg`  = `∑deepestEPivot²` = the SAME three blocks of the **T=0** product `C0|_{T0=0}·C1|_{T1=0}`
  (verified to equal the actual `framedParamsRegPivot` product reg-energy at `J=id`, frames `=1`).
- `coreΦ` = `deepestCoreF((coreAbsorb ·).2.1)` = `‖∏ S_s‖²`, the product of the **per-layer Schur**
  cores `S_s = T_s − Z_s(1+X_s)⁻¹Y_s` (`deepestCoreAbsorb` = the cutoff Schur shear `schurCutoffShift`).
- `Φ`     = `∑deepestEPivot² + coreΦ` = `Ereg + coreΦ` (the squeeze headline target).

## The leak (witness 1, exact)

`(C0·C1)₁₂ = (1+X0)Y1 + Y0·T1`; the T=0 product `₁₂ = (1+X0)Y1`. **Leak = `Y0·T1`** (and symmetrically
`Z1·T0` in `₂₁`). `Y0` is a `(reg,spec)`-slot deviation, `T1` a core-slot deviation — independent. So
the exact equality `h01 : P01 = (T=0 product)₁₂` is false in every neighborhood. (Matches the brief.)

## The obstruction (witnesses A, B — option 2 dies BOTH ways)

`P11` is identical for FULL and T=0 (no T enters it here); the leak lives only in `P12, P21`.

- **Line A** (`X0=X1=Z0=Z1=T0=0, Y1 = −T1·Y0`; free `Y0,T1`): a **2-surface** through the deepest pt.
  - FULL product `= [[1,0],[0,0]] = corM` exactly ⇒ `Sreg = 0`, `coreΦ = (S0·S1)² = (0·T1)² = 0`,
    `dlnLoss = 0`.
  - T=0 product `= [[1, −T1Y0],[0,0]]` ⇒ `Ereg = (T1Y0)² > 0`, so `Φ = (T1Y0)² > 0`.
  - ⇒ option-2 **lower** bound `γ₁·Ereg ≤ Sreg` becomes `γ₁·(T1Y0)² ≤ 0`: impossible for `γ₁>0`.
  - ⇒ squeeze **lower** bound `c₁·Φ ≤ dlnLoss` becomes `c₁·(T1Y0)² ≤ 0`: impossible. (The headline
    squeeze statement, not just its `Sreg=Ereg` phrasing, is false on line A.)
- **Line B** (`X0=X1=Y1=Z0=Z1=0`; free `Y0,T1,T0`): `Sreg = (T1Y0)² > 0`, `Ereg = 0`.
  ⇒ option-2 **upper** bound `Sreg ≤ γ₂·Ereg` fails.

The brief's premise "the leak is higher-order, dominated by `‖Y‖²` in `∑E²`" is **false**: `Y0·T1` is
degree-2, the same order as the `Y1`-type signal, and it produces exact cancellation (line A) — it is
not a higher-order perturbation foldable into a constant.

## Why this does NOT refute the headline RLCT (the gauge resolution — decorrelated Codex)

Independent re-derivation (Codex `xhigh`, decorrelated; gauge claim then re-verified exactly here):
`Y0` is a **gauge** direction, not a product transversal. Linearizing the internal gauge action
`(C0,C1) ↦ (C0·G, G⁻¹·C1)` at the deepest point: `δC0 = corM·A`, `δC1 = −A·corM` with `A=[[a,b],[c,d]]`
gives gauge tangents `{X0−X1, Y0, Z1}`; transversals `{X0+X1, Y1, Z0}`. On line A the explicit gauge
element `G=[[1,−Y0],[0,1]]` sends `C0·G = corM`, `G⁻¹·C1 = [[1,0],[0,T1]]` — i.e. line A is a pure gauge
orbit of the point `(corM, diag(1,T1))`, whose loss is genuinely `T1²` (carried by the CORE, where it
belongs), NOT `(T1Y0)²`. So the geometry is fine; the **chart** is the problem: `deepestEPivot` reads
the reg blocks off the **T=0 product**, where the gauge coordinate `Y0` contributes a spurious
`(T1Y0)²` that the true loss does not see.

## The correct comparable quantity (the fix the data points to)

`dlnLoss ≍ Sreg + Score` where BOTH are off the **FULL** product:
`Sreg = (P11−1)²+P12²+P21²` (full), `Score = ‖P22 − P21 P11⁻¹ P12‖²` (full global Schur). This is
**exactly** what the banked leaf lemma `dlnLoss_two_sided_of_frame` proves (`hconj` reads `P00,P01,P10,P11`
off `reindex(P0·N·QL)`; the bound is `(Sreg+Score) ≍ dlnLoss` with explicit endpoint-frame constants).
- Verified (sympy + MC): `inf(dlnLoss / (Sreg+Score)) → 1` as scale → 0 on line-A-biased neighborhoods,
  including the **corank-2** case `H=[3,3,3], r=1` (global Schur `D − C A⁻¹ B = det(P)/A`).
- Codex's note: `D − C A⁻¹ B = det(C0)det(C1)/A` — the invariant reduced core, matching the FULL global
  Schur, NOT the raw `T0T1` or the per-layer `∏S_s`.

So the bug is **localized** to the downstream identification, not the leaf core: `deepest_loss_squeeze`
lines 1531–1547 set `Sreg/Score` to the FULL blocks (correct), then `hSreg_eq` (line 1541) rewrites
`Sreg` into `∑deepestEPivot²` via the false `h00/h01/h10`. Delete that rewrite path; phrase the squeeze
target as the FULL `Sreg + Score` (or the RLCT-equivalent reparametrization), not `∑deepestEPivot²`.

## RLCT-sufficiency (brief's question 2) — the SUBTLE part, resolved

The brief asserts "comparability ⟹ rlctAt equal, so the headline value is unaffected." Two corrections:

1. **Comparability is the thing that FAILS** — so the squeeze cannot be the instrument. The
   `DeepestGaugeChart` structure (`DeepestGaugeChart.lean:275`) HARD-CODES the squeeze target as
   `Φ_struct = ∑(regStraighten (split w)).1² + deepestCoreF(coreAbsorb (split w)).2.1`, with
   `regStraighten` required to fix the core/spectator slots (`dE(0)=id`). With `regStraighten`'s output
   `= deepestEPivot` (the T=0 reg blocks), `Φ_struct` has zero set `V(Φ_struct) ⊊ V(dlnLoss)` (line A ∈
   `V(dlnLoss)`, ∉ `V(Φ_struct)`), so NO `c₁>0` gives `c₁·Φ_struct ≤ dlnLoss`. **`loss_squeeze` as
   currently typed is FALSE.** (Confirms the harness's own g161 note line 231 — "loss_squeeze over the
   raw reg slot is FALSE" — was right and `deepestEPivot` did not fix it; the leak is inter-layer.)

2. **The headline RLCT value is very likely SAFE — but via a NONLINEAR diffeo, not comparability.**
   Exact, on the minimal gauge slice (free `Y0,Y1,T1`, rest 0): `dlnLoss = (Y1+Y0T1)²`,
   `Φ_struct = Y1²`. The squeeze `c₁·Y1² ≤ (Y1+Y0T1)²` FAILS pointwise (line A `Y1=−Y0T1`). YET
   `rlct(dlnLoss) = rlct(Φ_struct) = ½`, because `u := Y1 + Y0T1` is a local diffeo (`∂u/∂Y1 = 1`), so
   `(Y1+Y0T1)²` and `Y1²` are analytically equivalent. **Comparability is sufficient for rlct-equality,
   not necessary** — a `dE(0)=id` change of coords also does it. The FULL reg blocks have unit
   transversal Jacobian (`A−1 ~ X0+X1`, `B ~ Y1`, `C ~ Z0`, the 3 = `nReg` transversal dirs) with the
   leaks `Y0T1, T0Z1, Y0Z1` PURE QUADRATIC — exactly absorbable by a `dE(0)=id` straightening. So the
   genuine `E` IS the FULL reg blocks straightened; `deepestEPivot` is `E` with the quadratic leaks
   wrongly dropped (T=0). **This is the actual fix: `regStraighten` must straighten the FULL product's
   reg blocks, not the T=0 product's.**

**Caveat I cannot close (controller's call):** that `rlct(Φ_struct) = rlct(dlnLoss)` on the minimal
slice does NOT prove it for the full 8-dim (or general `H`) problem — the diffeo `u=Y1+Y0T1` is slice-
local. Whether the global `Φ_struct` (T=0) still has the right rlct despite the failed squeeze, OR
whether the chart genuinely needs the FULL-reg `regStraighten`, is the open soundness question. The
SAFE route is to make `regStraighten` produce the FULL reg blocks (option-1-flavoured) so the squeeze
becomes the leaf lemma's TRUE comparability — not to gamble that the wrong-zero-set `Φ_struct` happens
to have the right rlct.

## Secondary issues (brief's (i),(ii))

- (i) last-layer column: NOT a real inconsistency. `framedParamsRegPivot`'s last layer uses
  `pivotThresholdSplit r (H last.succ) (pivotJSucc J)` on the column side; the bundle's `hcorner` is
  `reindex(rThr, pivotThr J)(deepestPoint_last · Q_last) = fromBlocks 1 0 0 0` — also pivot-column.
  Consistent **provided** the same `J` threads through both (`deepest_gauge_construction`'s `hpivJ:
  pivotJSucc J = Jb` does this). It's a typecheck tripwire, not a soundness hole.
- (ii) `endpoint_telescoping` needs `hinterface (s) : Q_s = 1 ∧ P_{s+1}=1` for every **interior**
  `(s:ℕ)+1 < L`. `hQf0/hPfL` cover only the two boundary frames. For `L=2` there are no strict-interior
  interfaces, so `hQf0/hPfL` suffice. For `L ≥ 3` the missing hyp is `deepestPoint_interior_frame_id`
  (`Q_s = 1 ∧ P_s = 1` for `1 ≤ s ≤ L−2`), banked in `DeepestFrame.lean:108`. Thread it into `hinterface`.

## PIN1 survival under E_zero→E_full (the gating question for the repair — SETTLED)

**PIN1 (`deepestEPivot_regSlice_fderiv`) survives VERBATIM** (exact sympy + decorrelated Codex xhigh,
`codex/pin1-survival-*`, independent re-derivation agreeing):
- `E_full − E_zero = (0, Y0·T1, T0·Z1)` — purely degree-2.
- Reg-slice Jacobian at 0 (core+spec held 0): `D(E_full)(r0,0,0) = D(deepestEPivot)(r0,0) = F` (the
  invertible `regBlockCLE`). Leaks vanish at core=0; `O(‖h‖²)` ⇒ zero strict derivative at 0.
- Core-direction Jacobian at 0: `∂E_full/∂T0(0)=∂E_full/∂T1(0)=0`.
- So `D(E_full)(0) = [F | 0 | G]` (reg-in `F` invertible, core-in `0`, spec-in `G`).

**BUT the chart architecture must change** (the deeper consequence): the squeeze's reg term MUST be
`Sreg` (FULL reg blocks), which DEPENDS on the core. So `regStraighten`'s reg OUTPUT must read the core
— `E_pivot : (reg,spec)→reg` becomes `E_full : (reg,core,spec)→reg`. The corrected chart
`regStraighten q = (E_full q, q.2.1, q.2.2)` has derivative `[[F,0,G],[0,I,0],[0,0,I]]` at 0
(block-tri, diag `(F,I,I)`, det = det F ≠ 0 — INVERTIBLE), so the IFT/`#72` peel input is intact.
Verified `∑(new regStraighten).1² = ‖E_full‖² = Sreg` matches `dln=0` on line A — over-count gone.

**Architecture verdict (brief Q2):** PIN1 RE-USED as-is (the reg-slice fact + 1-line bridge
`E_full(·,0,0)=deepestEPivot(·,0)`), NOT a new analog, NOT orphaned. The new Lean work is generalizing
the `regStraightenOf`/`regStraightenTotalCLM` straightening object from `(reg,spec)→reg` to
`(reg,core,spec)→reg` (existing invertibility argument with `proj:=id`). Full build-ready spec:
`restatement-spec.md`. This also CLOSES the open rlct risk I flagged earlier — the safe full-reg route
makes the squeeze the leaf lemma's TRUE comparability, so the headline rlct no longer rests on the
unverified `rlct(Φ_struct)=rlct(dlnLoss)` gamble.

## Files

- Cert scripts: `/tmp/witness_yt.py`, `comparability.py`, `lower_confound.py`, `exact_lineA.py`,
  `epivot_exact.py`, `full_with_schur.py`, `option2_test.py`, `gauge_check.py`, `corank2.py`,
  `inf_correct.py`, `ratio_inf.py`, `pin1_survival.py`, `route_decision.py`, `arch_final.py`,
  `rlct_compare.py`, `rlct_minimal.py`, `diffeo_unit.py` (one-off; algebra reproduced in this thread).
- Codex artefacts: `codex/squeeze-soundness-{prompt,answer}.md`, `codex/pin1-survival-{prompt,answer}.md`.
- The false lemmas: `lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean`
  `framedParams_split_eq_frame_raw` (~1327, the `h00/h01/h10` exact-equality conjunctions) +
  `deepest_loss_squeeze` (~1478, `hSreg_eq` ~1541).

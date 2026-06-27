# Thread 31 — PIN2 comparability re-architecture (the L2 geometric heart)

## hproducer (b) repair (6th catch, 2026-06-25): option A (comparability) is SOUND — see `r2-frontpivot-cert.md`

`hproducer` conjunct (b) `∑deepestEFull² = Sreg` is FALSE as an EQUALITY for non-front `J` (banked
`hproducer-verdict.md`). Adjudicated: the COMPARABILITY `∑deepestEFull² ≍ Sreg` HOLDS (the contained
repair, no headline restructure, no PIN1 touch). The FACT-3 floor witness (`17.98≠23.65`) was
INCOHERENTLY BASED — it didn't transport the basepoint; banked `deepestEFull_base : deepestEFull 0 = 0`
means both energies vanish at w0, so no `w→w0` floor path exists. Structural reason (from the def): the
`framedParamsPivot` last layer places the corner AND the deviation reads through the SAME `pivotThr.symm`
column reindex, so both are squared-norms of the same residual-deviation product under invertible column
reindexings (`QL`·permutation) ⇒ positive-definite quadratic forms with EQUAL kernel ⇒ comparable. EXACT
cert (r=1,H0=1,H2=2): both Gram spectra `{3.394,10.606}`, generalized eig `[c₁,c₂]=[0.5195,1.9250]`;
witness `17.98/23.65=0.76 ∈ [0.52,1.93]` ✓. CONTRAST dead option-2 (T=0 vs FULL = kernel mismatch);
here SAME product, invertible reindex = kernel-preserving. Build: restate (b) as `≍`, fold into the
squeeze's existing two-sided `c₁/c₂`. Soundness-critical: the proof must use the SHARED-`pivotThr.symm`
corner placement (NOT colPerm the corner). Codex independently verified A SOUND + B (front-pivot WLOG)
sound as the fallback (loss identity exact, MP, no PIN1 touch). Decorrelated Codex: `codex/r2-frontpivot-*`,
`/tmp/s5c_codexclean/answer.md`.

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

## S5c MATRIX CORE (r≥2 / M>1) — adjudicated; GERM-not-box (2026-06-25)

The headline needs M=H−r>1. Adjudicated: the scalar unit `u` becomes a matrix MIDDLE FACTOR — EXACT
identity `R = S0·(I − Z1·A⁻¹·Y0)·S1` (the LDU Schur-of-product; `W=I−Z1A⁻¹Y0`, rank-≤1 perturbation,
det W = a0a1/A → 1; telescopes over L). **CONFOUND (decorrelated Codex caught, my first MC missed):** the
standalone box comparability `∑‖R‖²≍∑‖∏S‖²` is FALSE for M>1 — Codex witness `S0=εE12,S1=εE21` with
`W[1,1]=0` ⇒ `R=0`, `∏S≠0`. BUT that needs off-pivot `Y0Z1≈−1` (off-pivot O(1)) — NOT a germ. On a TRUE
germ (ALL dev→0): `R−∏S = O(ε⁴)` while `∏S=O(ε²)` (strictly higher-order, verified) ⇒ `‖R‖²/‖∏S‖²→1`.
So **TRUE on a germ, NOT uniform on a box**; `rlctAtOn` germ-invariance makes the germ form sufficient.
Build-ready: the EXACT middle-factor identity + the in-sum remainder charge `|∑‖R‖²−∑‖∏S‖²| ≤ C·∑E²` on
a `𝓝 0` germ (NOT a `[m,M]` ratio bound). MC (true germ, rank-1 S-adversary): sup ratio →1 (1.0008 at
1e-2). **r≥2 matrix-PIVOT confirm — CLOSED (2026-06-25):** verified r=2/M=1 (sympy germ-orders + numeric
3-decade + Codex `codex/s5c-r2pivot-*` independent block-LDU). The identity is the SAME `W = I_M −
Z1·A⁻¹·Y0` (now `A=a0a1+Y0Z1` a MATRIX, A→I_r, A⁻¹ bounded); germ orders survive (`R−∏S=O(ε⁴)`,
`∏S=O(ε²)`); the `(I+X)⁻¹=I−X+…` X-linear contamination does NOT leak into `W−I` (carries Y0·Z1, two
off-pivot factors ⇒ O(ε²)) so `R−∏S` stays O(ε⁴) not O(ε³). **No residual flag remains** — S5c fully
closed germ-scoped (matrix pivot + matrix core both confirmed). Cert: `s5c-r2-cert.md`; consult
`codex/s5c-r2-*`, `codex/s5c-r2pivot-*`. This corrects the r=1 `s5c-cert.md` "standalone" phrasing —
narrow it to a germ for consistency (r=1 is standalone-safe since scalar `W=u` can't rank-cancel, but the
germ framing unifies). Last named open dependency in the framedParams-body design — CLOSED (germ-scoped).

## S5c — the `Rcore ↔ coreAbsorb` core identification (adjudicated WITNESS, 2026-06-25)

NOT banked (g156 only ASSERTS it in prose, and that prose `R−∏S ∈ ideal(reg)` claim is FALSE — Groebner
remainder `−Y1Z0 ≠ 0`). Adjudicated: the true statement is an EXACT unit-rescaling, cleaner than ideal
membership. `Rcore = u·∏S_s`, `u = ∏_s(1+X_s)/A` a bounded unit (→1 at 0); both `= ∏det(C_s)` over the
global pivot `A` resp. ∏ layer-pivots (rank-1 determinant identity). So `∑Rcore² ≍ ∑(∏S_s)²` STANDALONE
on a nbhd (NO `∑E²` charge). Build-ready atom + the squeeze wiring (feed the GLOBAL `Rcore` to
`core_comparability_squeeze`, NOT `∏S` — the gap `Rcore−∏S` is NOT `E`-controllable) in `s5c-cert.md`.
Decorrelated Codex (by-hand re-derivation) agrees on every point. **Scope: r=1 EXACT (L=2,3 verified);
matrix-r (M>1) MC-supported [0.99,1.02] at scale 1e-2, FLAGGED as a follow-on for the general-`(C,θ)`
headline.** Cert: `s5c-cert.md`; consult: `codex/s5c-*`.

## framedParams_split_eq_frame_raw BODY decomposition (post-integration, 2026-06-25)

After the PIN2 repair integrated green (`bcfb8b60`), the cert BODY is a `sorry` with a TRUE conclusion
(`∑(deepestEFull (split w))² = Sreg` + leak + core). Build-ready sub-lemma decomposition in
`framedbody-cert.md` (decorrelated Codex `codex/framedbody-*`, which REORDERED my risk ranking). Key
findings:
- The step-(1) decode the old docstring called the "sub-blocker / genuine bulk" is **already banked**
  (`reindex_fromBlocks_reads_eq_deviation`, sorry-free) — the docstring predates it.
- **Highest risk is S0/S3 frame-source reconciliation**, not the S1' pivot decode (Codex Q4). Largely
  discharged by the co-sourced bundle `deepestPoint_frame_pivot_exists` (same `Pf,Qf,J`), BUT a
  CONFIRMED subtlety: the bundle's `hcorner` normalizes `deepestPoint_last`, NOT `B` — so S3b
  (`reindex(P0·B·QL)=fromBlocks 1 0 0 0`) routes through `prod(deepest)=B` (banked) + telescope-of-deepest
  + product-of-corners. Real sub-step, low-risk (all pieces banked / core-0 collapse).
- **S5 hides three obligations** Codex flagged (my decomposition under-compressed them): S5a `P00`-unit +
  shrink `U`; S5b the leak estimate `∑(P10⅟P00 P01)² ≤ t²·Sreg` (a neighborhood Cauchy-Schwarz, NOT a
  corollary of `fullProduct_core_split`); S5c the `Rcore ↔ deepestCoreF(coreAbsorb)` identification (the
  genuine new geometry — the global-Schur ↔ per-layer-coreAbsorb ideal-membership; may need its own cert).
- S1' pivot-column decode pre-derived exact (option α): the banked 4-case `ext` with
  `pivotThresholdSplit_symm_*` swapped in; cast/bookkeeping risk only.

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

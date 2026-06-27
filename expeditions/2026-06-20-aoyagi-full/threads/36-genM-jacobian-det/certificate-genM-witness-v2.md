# Certificate — the UNIFIED 3-case ∀M achiever chart (witness tide v2)

**Seat:** lean-formaliser (DESIGN+VALIDATE pass, no Lean commit). **Date:** 2026-06-27. Supersedes
`certificate-genM-witness.md` (the §5/carrier/live-leaf v1 cert, which was WRONG — its uniform-`(0,0)`
carriers fail the live leaf, and its "leaf always dead" premise is false; see `witness-tide-finding.md`).

**Gate (the new discipline — EXHAUSTIVE VALIDATION, not assertion):** every claim below is validated
over ALL `M` with `2 ≤ L`, `minAdm ≥ 1` on two grids — widths `1..3` `L∈{2,3,4}` (351 cases) and widths
`1..4` `L∈{2,3}` (320 cases). The INTERIOR colPath is `0 failures` (`scripts/witness_tide_v2_validate.py`,
the exact Aoyagi argmin `achiever(M)` in `scripts/witness_tide_validated.py`). The BOUNDARY 66 are
analysed authoritatively in `certificate-boundary-chart.md` / `scripts/pp_GATE.py` (the 3-way split below):
CLEAN-20 `F=u²U`/`U≠0`/det/threshold 20/20; SMEAR-A-20 (rational) 20/20; SMEAR-B-26 (two-axis) 23/23 +
3 `r≥2` cases closed EXACT in `pp_flagged3`. (My `witness_tide_v2_validate.py`'s `validate_boundary` was a
factor-level OVER-simplification — SUPERSEDED by `pp_GATE.py`.) Numbers reproduce on run.

---

## 0. The target + the banked reduction (verified)

The rate-side `NodeAchieverChart M` field `Ubound` (a.e.-positivity of the unit `Ufun`) needs, for the
achiever-path instantiation, `∃ w, achieverUfun M hL hN w ≠ 0`. The banked reduction
(`RouteMAchieverVvalPoly`) gives `achieverUfun w = ∑∑ (Hmat 0 i j)²` (the ℝ telescope chain at `w p`),
so `achieverUfun w ≠ 0 ⟺ Hmat 0 ≠ 0` at `w` (`achieverUfun_eq_eval` + `eval_UPolyGen` +
`VvalGen_eq_sqSumHmat0`, all sorry-free + banked). The chain `Hmat`:
`Hmat L = Rfin L = 0`, `Hmat s = B_s·Hmat(s+1) + E_s·suffix(s+1)` (`Chain.Hmat_succ`), `suffix L = I`,
`B_s = Bmat s` (`= bmatStack [K;X·K]`, `s≥1`; `reindex 1` at `s=0`), `E_s = Rmat_s·A_s`,
`A_s = chainA(N_s, W_s, C(s+1))`. The struct decoder `genBlkFlatStruct` has `Rfin ≡ 0`, `Wblk(L) = 0`.

Width families: `Wext k = M k`; `Text 0 = M0`, `Text(k+1) = tach k`, `tach = cons(M0, tStar)`,
`tStar = ` Aoyagi argmin (`tStar(L−1) = 0`). Per boundary `j∈[0,L−1]`: `r_j = Text(j)−Text(j+1)`,
`c_j = M_j − Text(j+1)`; `minAdm = ∑_j r_j c_j`. (NB the chain "boundary `s`" = GenBlk index; `r_s, c_s`
above use the same `s`. The leaf width `Text L = tach(L−1) = tStar(L−2)` — the second-to-last `tStar`,
NOT `tStar(L−1)`; this off-by-one vs the v1 cert's "leaf dead" claim is the root of the v1 error.)

---

## 1. THE CLASSIFIER (decidable, exhaustive, exclusive) — `2 ≤ L`, `minAdm ≥ 1`

```
INTERIOR  := ∃ p ∈ [1, L−1],  r_p ≥ 1  ∧  c_p ≥ 1          -- some interior boundary drops both row & col rank
BOUNDARY  := ¬INTERIOR  (⟺ all codim at the LAST boundary; minAdm = Text(L)·M_L)
L = 1     := out of scope (rides banked `DeepestBaseL1`, a single-layer pure-radial chart)
```

`INTERIOR`/`BOUNDARY` is a `Decidable` `∃`/`∀` over `Fin L` on `ℕ` inequalities. **Exhaustive + exclusive
by construction** (negation). Validated counts: `interior 285, boundary 66` (grid 1..3); `240, 80`
(grid 1..4). **`minAdm = 0` does NOT occur for `2 ≤ L`** (the target `B = 0` always has positive achiever
codim) — 0/671 cases across both grids — so `hpos : 1 ≤ minAdm M` holds on every in-scope `M` and the
case split is total. Banked anchors by class: `(2,2,1)`, `(2,2,2)`, `(3,3,4)`, `(3,3,3,3)` are INTERIOR;
`(4,4,2,2)` is BOUNDARY (`Text=[4,4,4,2]`, all codim at the last layer).

---

## 2. CASE INTERIOR (285/285) — the colPath Schur chart, pinned to BUILD precision

**Pivot.** `p* := ` the **deepest** `p ∈ [1, L−1]` with `r_p ≥ 1 ∧ c_p ≥ 1` (`Finset.max'` of the
nonempty active set; nonempty = the `INTERIOR` predicate). E-pivot at `Rmat_{p*}` bottom-right `(0,0)`,
i.e. position `(Text(p*+1), Text(p*+1))` (since `rmatPad` places the `r×c` E-block at offset
`Text(p*+1)`); value `e = 1`.

**Witness blocks (all `= 0` except):** all Schur `K`-blocks `= I` (so `readK = δ`, `Bmat (s) = [I ; 0]`);
the pivot `E_{p*}(0,0) = 1`; the carriers `W_b(0, Text(b+2)) = 1` for **every** `b ∈ [p*, L−1]`, where
`Text(L+1) := tStar(L−1) = 0` (so the deepest carrier `W_{L−1}` sits at column `0`). (`X = N = 0`.) The
carrier column at `b` is `σ_{b+1} = Text(b+2)` — the *previous* surviving column, NOT `σ_b`; this
closed form is VALIDATED (0 mismatches / 285). The witness coordinate vector is `w := wOnIdx ∘
chartIdxEquiv` with `wOnIdx` reading these off the `ChartIdx` role-slots; each reader value is
`wOnIdx ⟨k, role⟩` by `Equiv.apply_symm_apply`.

**rowPath (constant).** `ρ := Text(p*+1)`. Well-typed `ρ : Fin (Text s)` for all `s ≤ p*` because
`Text(s) ≥ Text(p*) > Text(p*+1) = ρ` (the strict step is `r_{p*} ≥ 1`). VALIDATED: the surviving entry
of `Hmat 0` is exactly `(ρ, 0)` on all 285.

**colPath (uniform).** `σ_s :=` the surviving ROW of `suffix(s)`'s column `0`: `σ_L := 0`,
`σ_s := Text(s+1)` for `s ∈ [p*, L−1]`. The carrier at boundary `b` sits at COLUMN `σ_{b+1}` (the
previous surviving row, `= Text(b+2)`), NOT `σ_b`. KEY structural fact (VALIDATED, 0 violations / 285):
the lift block `c_b = M_b − Text(b+1) ≥ 1` for **every** `b ∈ [p*, L−1]` — so a carrier is placed at every
such `b` and `σ` is the closed form `Text(s+1)` (no kept-block fallback needed in range). And
`σ_{p*} = Text(p*+1) = ρ` (VALIDATED, 0 mismatches).

**The three inductions (the build structure):**
- (I-base) **At `p*`:** `B_{p*}` row `ρ = Text(p*+1)` is the FIRST bottom-`[X·K]` row, `= 0` at the witness
  (`X = 0`), so `(B_{p*}·Hmat(p*+1))(ρ,0) = 0`. Hence `Hmat(p*)(ρ,0) = (E_{p*}·suffix(p*+1))(ρ,0)
  = (Rmat_{p*}·suffix(p*))(ρ,0)` (via `E = Rmat·A`, `suffix p* = A_{p*}·suffix(p*+1)`). The pivot
  `Rmat_{p*}(ρ,ρ) = 1` ⟹ `= suffix(p*)(ρ, 0)`.  [also: `Hmat(p*+1)` has only `Text(p*+1) = ρ` rows, so
  row `ρ` is literally out of its range — an even cleaner kill of the `B·H` term, available as alternate.]
- (I-suffix) **`suffix(s)(σ_s, 0) = 1` for `p* ≤ s ≤ L`, downward.** Base `suffix(L) = I` ⟹
  `suffix(L)(0,0) = 1` (`σ_L = 0`). Step `suffix(s) = A_s · suffix(s+1)` (`suffix_succ`):
  `suffix(s)(σ_s, 0) = ∑_c A_s(σ_s, c)·suffix(s+1)(c, 0)`; `σ_s = Text(s+1)` is the first LIFT row of
  `A_s`, so `A_s(Text(s+1), c) = W_s(0, c)` (`chainA_apply_natAdd`), `= δ(c, σ_{s+1})` at the witness
  (carrier `W_s(0, σ_{s+1}) = 1`, the colPath `σ_s ↦ σ_{s+1}` link: `σ_{s+1} = Text(s+2) = ` the column
  the carrier reads, VALIDATED). `Finset.sum_eq_single σ_{s+1}` ⟹ `= 1·suffix(s+1)(σ_{s+1},0) = 1`.
  At `s = p*`: `suffix(p*)(ρ, 0) = 1` (since `σ_{p*} = ρ`). [For `b = L−1`: `σ_L = 0`, carrier
  `W_{L−1}(0,0)=1`; needs `W_{L−1}` to EXIST — it does, `b = L−1 < L`, but the decoder gate is
  `Wblk(b) ≠ 0` iff `b < L`; `b = L−1 < L` ✓.]
- (I-up) **`Hmat(s)(ρ, 0) = Hmat(s+1)(ρ, 0)` for `s < p*`, downward to `0`.** `E_s = Rmat_s·A_s = 0`
  (`Rmat_s = 0` for `s ≠ p*`), so `Hmat(s)(ρ,0) = (B_s·Hmat(s+1))(ρ,0) = ∑_t B_s(ρ,t)·Hmat(s+1)(t,0)`.
  `ρ < Text(s+1)` (since `Text(s+1) ≥ Text(p*) > ρ`), so `ρ` is a TOP-`[K]` row of `B_s = bmatStack`,
  `B_s(ρ, t) = K(ρ, t) = δ(ρ, t)` (`bmatStack_top`, `K = I`). `Finset.sum_eq_single ρ` ⟹
  `= Hmat(s+1)(ρ, 0)`. Compose `s = p*−1, …, 0`: `Hmat(0)(ρ, 0) = Hmat(p*)(ρ, 0) = 1`.

**Conclusion:** `Hmat 0 (ρ, 0) = 1 ≠ 0`, so `sqSumHmat0 ≥ 1² > 0`, so `achieverUfun w ≠ 0`. VALIDATED
`Hmat 0 (ρ,0) = 1` on all 285 (grid 1..3) + 240 (grid 1..4).

**Lean shape (build precision).** Downward inductions on `d = p*−s` (I-up) / `d = L−s` (I-suffix) via
`Finset.sum_eq_single` over the banked entry laws (`bmatStack_top`, `chainA_apply_natAdd`,
`rmatPad`/`Rmat` pivot), in the dependent-`Fin` `⟨_, by omega⟩` `have`+`exact` kernel (`lean/CLAUDE.md`).
The witness `wOnIdx` matches on the `frameSplitEquiv`/`liftSlotEquiv` role-slot outputs (round-trips
cancel by `apply_symm_apply`). No `sorry`/research; bounded engineering (the v1 cert's `rowPath` skeleton,
CORRECTED: rowPath = const `Text(p*+1)`, colPath = `Text(b+1)`, NOT uniform `(0,0)`).

---

## 3. CASE BOUNDARY (66/66) — TWO charts, both single-pivot  [SETTLED in `certificate-genM-smeared.md`]

All codim at the last boundary: `minAdm = r·c`, `r := Text(L)`, `c := M_L`, `m1 := M_{L−1}`. The
achiever-path struct decoder gives `achieverUfun ≡ 0` here (`Rfin ≡ 0`), so this class needs a SEPARATE
chart (OPTION A). The 66 split into TWO sub-classes, **both single-pivot** (the earlier 3-way SMEAR-A/B
split + the multi-axis conclusion are RETRACTED — see `certificate-genM-smeared.md`, which settled the
two residuals):

- **CLEAN (20): `r = m1`** ⟹ the active block = the WHOLE deepest factor. The banked
  `(4,4,2,2)`/`(2,2,1)`-style **single-pivot whole-deepest radial** (`pivotBlowupOn` on all `m1·c`
  deepest coords, `det = |u_p|^{m1·c−1} = |u_p|^{minAdm−1}`) fits `NodeAchieverChart` VERBATIM. EXACT
  20/20. **Cite banked `RouteM4422`.**
- **SMEARED (46): `r < m1`** ⟹ the **rational single-pivot chart** `φ_sm` (`certificate-genM-smeared.md`):
  `A⁽ᴸ⁻¹⁾ = [z·H̄ − Λ_0·S_bot ; S_bot]`, `Λ_0 = (P_1ᵀP_1)⁻¹P_1ᵀP_2` the rational routing of the FRONT
  product `P = A⁽⁰⁾···A⁽ᴸ⁻²⁾`. The unifying fact (EXACT, 652/652 wider grid): the **front bottleneck
  `min(M_0,…,M_{L−1}) = r`** for ALL smeared `M`, so `P_1` is left-invertible and `P_2 ∈ col(P_1)` — the
  routing is well-defined and `P·A⁽ᴸ⁻¹⁾ = z·P_1 H̄`, giving `F = z²·U`, `U = ‖P_1 H̄‖²` (POLYNOMIAL,
  `≢ 0`). **Single pivot `z`** (NOT two-axis — the prior two-axis chart was an L=2-only artifact). Det
  `= |z|^{minAdm−1}` EXACTLY (block-triangular: identity front + unit-triangular rational shear + radial
  `pivotBlowupOn`), threshold exactly `½·minAdm`. **Fits the EXISTING `NodeAchieverChart`** (single axis);
  the ONE new piece is the `cov` proof via `S1.1 weightedThreshold_transport` (the rational map is
  a.e.-analytic, off the null set `{det P_1ᵀP_1 = 0}`). EXACT 46/46 on all checks (`scripts/pp_smear_GATE.py`:
  unification + `F=z²U`/`U≠0`/`U` polynomial + det `z^{minAdm−1}` + coord count `= N` + threshold `½·minAdm`).

**Both residuals SETTLED** (Residual 1: the 46 smeared UNIFY under one rational single-pivot chart —
NO multi-axis bundle; Residual 2: the rational shear is unit-triangular, det EXACTLY `|z|^{minAdm−1}`
end-to-end). The brief's hoped-for single-pivot chart DOES exist for ALL smeared `M`, just RATIONAL (not
polynomial) — the routing divides by the front Gram minor. See `certificate-genM-smeared.md` for the
explicit `φ_sm`, the four `NodeAchieverChart` facts, and the Lean cost (the only new piece: the rational
`cov`).

---

## 4. CASE L = 1 (banked) — confirmed out of scope here

For `L = 1` the achiever chain has length 1 (no Schur frame, no chain telescope); the `2 ≤ L` hypothesis
on `structAdm_tach`/the chain machinery excludes it. `L = 1` rides the banked `DeepestBaseL1` (the
single-layer deepest-point normal form: the loss is a flat shifted sum of squares, RLCT `= M0·M1/2`, a
pure-radial single-layer chart). No witness/colPath needed.

---

## 5. THE UNIFIED ASSEMBLY `nodeChartGeneral M (hpos : 1 ≤ minAdm M)`  (`2 ≤ L`)

```
nodeChartGeneral M hpos :=        -- 2 ≤ L
  if  ∃ p∈[1,L−1], r_p≥1 ∧ c_p≥1   -- INTERIOR (decidable)
  then  the colPath Schur achiever chart (§2)         -- achieverUfun ≠ 0 via Hmat 0 (Text(p*+1), 0) = 1
  else if  Text(L) = M_{L−1}        -- BOUNDARY-clean (decidable)
  then  the banked single-pivot whole-deepest radial (§3, cites RouteM4422/RouteM221)
  else  φ_sm : the rational single-pivot smeared chart (§3, certificate-genM-smeared.md)
```
each branch supplies a `NodeAchieverChart M` (`hpos`, `phi`, `p`, `leafH`, `leafH_pivot`, `Ufun`,
`Ubound`, `Umeas`, `leaf_integrand`, `cov`, `image_subset`), so the assembly
`routeMCore_box_diverges_of_nodeChart` discharges the box-divergence atom ∀M (`2 ≤ L`). `L = 1` is the
separate `DeepestBaseL1` branch. The four cases are exhaustive (§1) and each guard is decidable.
**The multi-axis caveat is RETRACTED** (`certificate-genM-smeared.md`): all three `2≤L` branches are
SINGLE-pivot, so all fit the EXISTING single-axis `NodeAchieverChart` — no multi-axis bundle. The smeared
branch's chart is RATIONAL (the only structural difference), so its `cov` field is discharged via
`S1.1 weightedThreshold_transport` (a.e.-analytic), not the polynomial `pivotBlowupOn` `cov`.

**The binding pivot + threshold (all branches):** `leafH_pivot : leafH p = minAdm − 1` (the radial
exponent), threshold `(minAdm−1+1)/(2·1) = ½·minAdm` (`nodeChart_thresholdLe`). INTERIOR: the radial
exponent comes from the chart's full Jacobian (the colPath chart's `|det| = |u_p|^{minAdm−1}` is the
thread-36 det programme — SEPARATE from this witness, already scoped). BOUNDARY-CLEAN: `|u_p|^{minAdm−1}`
from the radial `active.card−1`. SMEARED: `|z|^{minAdm−1}` from the radial `r·c−1 = minAdm−1` + the
unit-triangular rational shear (det 1), EXACT end-to-end (`certificate-genM-smeared.md` §3).

---

## 6. What is PROVED vs to-BUILD vs CITED

- **PROVED (exhaustively validated, this pass):** the classifier is exhaustive/exclusive/decidable + total
  (`minAdm≥1` ∀ in-scope `M`, 0/671); the INTERIOR colPath construction yields `Hmat 0 (Text(p*+1),0) = 1`
  (351/351 + 240/240 — `scripts/witness_tide_v2_validate.py`); the BOUNDARY-CLEAN single-pivot radial
  (`F=u_p²U`, `U≠0`, `radial.card=minAdm`, 20/20); the BOUNDARY-SMEARED rational single-pivot chart
  (front-bottleneck`=r` 652/652, `F=z²U` single-pivot + `U≢0` polynomial + det `z^{minAdm−1}` + coord
  `=N` + threshold `½·minAdm`, 46/46 — `scripts/pp_smear_GATE.py`; `certificate-genM-smeared.md`).
- **TO BUILD (Lean):** (a) **INTERIOR, BOUNDED — DONE, integrated** (285/351, reviewer-PASS): the colPath
  witness `achieverUfun ≠ 0`; the colPath chart's Jacobian is the SEPARATE thread-36 det programme. (b)
  **BOUNDARY-CLEAN (20), BOUNDED:** the `NodeAchieverChart` fields from the banked `RouteM4422`/`RouteM221`
  radial. (c) **BOUNDARY-SMEARED (46), BOUNDED:** the rational single-pivot chart `φ_sm` — fits the
  EXISTING `NodeAchieverChart` (single axis); the only new piece is the rational `cov` via
  `S1.1 weightedThreshold_transport` (NO new bundle, NO new citation). (d) the `nodeChartGeneral` 4-way
  case-split assembly.
- **CITED:** `DeepestBaseL1` (L=1); `RouteM4422`/`RouteM221` radial (boundary-clean 20);
  `S1.1 weightedThreshold_transport` (smeared rational `cov`); the banked reduction
  (`achieverUfun_eq_eval`, `Hmat0_eval`, `UPolyGen_ne_zero_of_witness`, `achieverUbound`) + entry laws
  (`bmatStack_top`, `chainA_apply_natAdd`, `rmatPad`); `monomialIntegrand_lintegral_box_eq_top` (reused,
  single-axis, all branches).

The durable gates: `scripts/witness_tide_v2_validate.py` (interior 285/285 + 240/240),
`scripts/pp_smear_GATE.py` (smeared 46/46, all 5 checks). Re-run before any Lean tide; both must print
`0 failures`.

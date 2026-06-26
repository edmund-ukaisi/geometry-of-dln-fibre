# Build-ready repair spec — PIN2 (post-refutation) + PIN1 survival

**Verdict recap.** Option 2 (`Sreg ≍ ∑deepestEPivot²`) is UNSOUND (both directions; thread 31).
`loss_squeeze` is FALSE as typed. The repair is: the squeeze's **regular term must read the FULL
product's reg blocks**, which depend on the core slot — so `regStraighten`'s reg-OUTPUT must read the
core. **PIN1 survives verbatim** (the invertible reg-slice derivative `F` is unchanged — leaks are
degree-2). All algebra exact; decorrelated Codex (xhigh) on both the squeeze-soundness and the
PIN1-survival points; both in `codex/`.

---

## The non-negotiable fact that sets the architecture

The squeeze needs `∑(regStraighten q).1² ≍ dlnLoss − coreterm`. The only reg quantity comparable to the
loss's regular part is the **FULL product** reg energy `Sreg = (P00−1)²+P01²+P10²` (the leaf lemma).
`Sreg` DEPENDS on the core `T` (leak `P01 = (1+X0)Y1 + Y0·T1`). Therefore:

- A core-INDEPENDENT reg output (`E_pivot : (reg,spec)→reg`, the current `deepestEPivot`) CANNOT match
  `Sreg`. Confirmed dead three ways: `∑deepestEPivot²` over-counts on line A (`(T1Y0)²` vs `dln=0`);
  `∑deepestEPivot² + per-layer-Schur` fails (current); `∑deepestEPivot² + GLOBAL-Schur` ALSO fails
  (the over-count is in the *added* reg term, which no core term can subtract).
- So `E_pivot` must become `E_full : (reg, spec, core) → reg` — taking ALL THREE slots, returning the
  FULL product's three reg blocks (= `P00−1, P01, P10` from the leaf lemma's `hconj`).

## PIN1 survives — exact (the gating question, answered)

`E_full − E_zero = (0, Y0·T1, T0·Z1)` — **purely degree-2** (Codex re-derived independently, agrees).
- Reg-slice derivative at 0 (core+spec held 0): `D(E_full)(r0,0,0) = D(deepestEPivot)(r0,0) = F`
  (the block-triangular invertible `regBlockCLE`). IDENTICAL — the leaks vanish at core=0.
- Core-direction derivative at 0: `∂E_full/∂T0(0) = ∂E_full/∂T1(0) = 0` (leaks are degree-2).
- So `D(E_full)(0)` in block form (rows reg-out; cols reg-in, core-in, spec-in) is `[F | 0 | G]`
  (`G` = spectator block, possibly nonzero — coordinate-dependent).

**`deepestEPivot_regSlice_fderiv` (PIN1) is RE-USED verbatim** as the reg-slice fact, via a one-line
bridge `E_full(r0, 0, 0) = deepestEPivot(r0, 0)` (the core+spec-zero restriction kills the leaks —
`Matrix.ext`, each leak carries a zeroed factor). **NOT** a new invertibility argument, **NOT**
orphaned. `deepestEPivot` stays as the reg-slice witness; only the squeeze's reg OUTPUT changes object.

## The chart-derivative invertibility (the IFT-peel input) survives

Corrected `regStraighten q := (E_full(q.1, q.2.2, q.2.1), q.2.1, q.2.2)` — reg OUTPUT reads all slots,
core/spec OUTPUT slots fixed. Derivative at 0 (blocks reg/core/spec):

        [[ F   0   G ]
         [ 0   I   0 ]
         [ 0   0   I ]]

block-triangular, diagonal `(F, I, I)` ⇒ `det = det F ≠ 0` ⇒ **invertible**. The IFT/`#72` bounded-unit
local-diffeo peel (`rlctAtOn_boundedUnit_localHomeomorph`) consumes exactly an invertible derivative at
0 + `ContDiff` + a local inverse on an open `V` — all intact. (`D_core E_full(0)=0` is what makes the
reg-slice = `deepestEPivot` for the PIN1 bridge; invertibility itself only needs `F` invertible.)

## What changes in Lean (build-ready)

### (1) `DeepestRegAbsorbIFT.lean` — generalize the straightening object
`regStraightenOf`, `regStraightenTotalCLM`, `hasStrictFDerivAt_regStraightenOf_gen` currently take
`E_pivot : R × S → R`. Generalize to `E_pivot : R × (C × S) → R` (full split `(reg, core, spec)`):
- `regStraightenOf E_pivot q := (E_pivot q, q.2.1, q.2.2)` (reg-out reads all; core/spec-out fixed).
- `regStraightenTotalCLM D_E` for `D_E : (R×(C×S)) →L R`: `δ ↦ (D_E δ, δ.2.1, δ.2.2)` — invertible
  ⟺ the reg-block `D_E ∘ regIn` is a unit. Shear shape `[[F,0,G],[0,I,0],[0,0,I]]` block-tri, SAME
  unit criterion on `F`.
- `hasStrictFDerivAt_regStraightenOf_gen` re-proves with `proj := id` (no longer `(q.1,q.2.2)`).
- `regStraightenTotalCLM_equiv_of_regBlock_isUnit` (`DeepestRegSliceFderiv.lean:616`) generalizes —
  invertibility from the reg-block unit, now over the full domain.

### (2) `DeepestGaugeConstruction.lean`
- `framedParams_split_eq_frame_raw` (~1327): **DELETE `h00/h01/h10`** (the false exact equalities).
  Keep `hconj`, `hleak`, `hcore_le/hcore_ge`. (Optionally ADD `hregval_full : E_full(split w) =
  regResidualPack of (P00−1,P01,P10)` — an IDENTITY by `regResidualPack` bijectivity + `hconj`, no leak.)
- Define `E_full : DeepestSplit → (Fin nReg → ℝ)` = the regResidualPack of the FULL product
  `reindex(P0·(prod(paramsSymm w)−B)·QL)` reg blocks (= directly the `hconj` blocks `(P00−1,P01,P10)`).
- `deepestEPivot_deriv` (~1188): re-aim to produce `HasStrictFDerivAt E_full D_E 0` with `D_E`'s
  reg-block `= F`, via PIN1 + the bridge `E_full(·,0,0) = deepestEPivot(·,0)`. The core-block-zero fact
  (`∂E_full/∂core(0)=0`, the quadratic-leak lemma) is the new small atom.
- `deepest_loss_squeeze` (~1478): **DELETE `hSreg_eq`** (line 1541). Replace `hregval` with
  `hregval_full : (regStraighten q).1 = E_full q`. Then `∑(regStraighten (split w)).1² = Sreg` is the
  identity `‖E_full‖² = Sreg` (regResidualPack + hconj). The `c₁/c₂` arithmetic (lines 1566–1602) is
  UNCHANGED (it only ever needed `∑(regStraighten).1² = Sreg`, never `Sreg = Ereg`).

### (3) `DeepestGaugeChart.lean` — the structure
`regStraighten_core`/`regStraighten_spectator` (OUTPUT core/spec slots fixed) STAY TRUE — `E_full`
changes only the reg OUTPUT. `regAbsorb_rlct` (the peel) re-proves with the generalized
`regStraightenOf`/`regStraightenTotalCLM`; the `loss_squeeze` field is now TRUE.

### (4) `deepest_regAbsorb_exists` (~1697 wiring) + producer
Change `E_pivot : (reg,spec)→reg` to `E_full : (reg,core,spec)→reg`; `hEp_deriv` the full-domain
fderiv (reg-block `= F`); the defining identity `(regStraighten q).1 = E_full q`.

## Secondary fixes
- (i) last-layer pivot/threshold column: NOT an inconsistency; same `J` threaded (`hpivJ`). With
  `framedParamsRegPivot` only feeding PIN1's reg-slice witness now, the concern is contained.
- (ii) `endpoint_telescoping` needs `hinterface (s):Q_s=1∧P_{s+1}=1` for every interior `(s)+1<L`;
  `hQf0/hPfL` cover the boundary; for `L≥3` thread `deepestPoint_interior_frame_id` (`DeepestFrame.lean:108`).
  For `L=2` (current target) no strict-interior interface — `hQf0/hPfL` suffice.

## Sound banked atoms (stay)
`dlnLoss_two_sided_of_frame` (leaf, `Sreg+Score ≍ dlnLoss`), `core_comparability_squeeze` (#54),
`endpoint_telescoping` (+ interior frame id for L≥3), `exists_deepest_lastLayer_pivotFrame`,
`deepestPoint_frame_normal`, `regResidualPack` (bijection), `deepestEPivot_regSlice_fderiv` (PIN1 —
RE-USED as the reg-slice fact), `regBlockCLE`, `regStraightenTotalCLM_equiv_of_regBlock_isUnit`
(generalize the domain).

## Net effort
NOT a localized lemma fix; NOT a re-architecture of the invertibility either. The genuine new work:
(a) generalize `regStraightenOf`/`regStraightenTotalCLM` from `(reg,spec)→reg` to `(reg,core,spec)→reg`
(the existing proofs with `proj:=id`); (b) define `E_full` + the identity `‖E_full‖²=Sreg`; (c) the
bridge `E_full(·,0,0)=deepestEPivot(·,0)` + `∂E_full/∂core(0)=0` (degree-2) feeding PIN1's `F` into the
full-domain `D_E`. **PIN1's invertibility argument and the leaf squeeze are RE-USED, not re-proved.**

## DELETE from the squeeze path (the false load-bearers)
`framedParams_split_eq_frame_raw`'s `h00/h01/h10`; `deepest_loss_squeeze`'s `hSreg_eq`;
`deepestEPivot_sq_sum_eq_blocks` (the `∑deepestEPivot² = T=0 product reg energy` summing identity — was
only there to feed the false `hSreg_eq`).

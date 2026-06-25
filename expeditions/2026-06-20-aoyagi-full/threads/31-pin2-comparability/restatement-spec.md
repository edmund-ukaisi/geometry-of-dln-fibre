# Build-ready restatement spec — PIN2 (the post-refutation repair)

**Verdict:** option 2 (weaken `h00/h01/h10` to `Sreg ≍ ∑deepestEPivot²`) is **UNSOUND** — that
comparability is false in BOTH directions (line A / line B). Do NOT implement it. The repair below is
option-1-flavoured: drop the `deepestEPivot`/T=0 identification entirely and let the squeeze be the
leaf lemma's TRUE comparability `dlnLoss ≍ Sreg + Score` on the FULL product, with `regStraighten`
straightening the FULL reg blocks.

## What is SOUND and stays (the leaf core)

`dlnLoss_two_sided_of_frame` (`DeepestGaugeBlocks.lean:558`) is **correct**: given `hconj :
reindex(P0·N·QL) = fromBlocks (P00−1) P01 P10 P11` and `hleak`, it proves
`(Sreg + Score) ≍ dlnLoss` with `Sreg = (P00−1)²+P01²+P10²` and `Score = ‖P11 − P10⅟P00 P01‖²` — both
off the FULL product `N = ∏(paramsSymm w) − B`. Keep it verbatim. The `framedParams_split_eq_frame_raw`
`hconj` + `hleak` + the CORE comparability `hcore_le/hcore_ge` (lines 1365–1371) are all sound.

## What is FALSE and must be deleted

1. `framedParams_split_eq_frame_raw` (`DeepestGaugeConstruction.lean:1327`), the three conjuncts
   `h00/h01/h10` (lines 1356–1364): `P00 = (T=0 product)₁₁ ∧ P01 = (T=0 product)₁₂ ∧ P10 = (T=0
   product)₂₁`. These are EXACT equalities between FULL-product blocks (`P00,P01,P10` from `hconj`) and
   T=0-product (`framedParamsRegPivot`) blocks. FALSE: leak `(C0C1)₁₂ − (T=0)₁₂ = Y0·T1 ≠ 0`.
   → **Delete `h00/h01/h10` from the cert's conclusion.**
2. `deepest_loss_squeeze`'s `hSreg_eq` (`DeepestGaugeConstruction.lean:1541`): `Sreg = ∑deepestEPivot²`
   via `rw [h00, h01, h10]`. FALSE (depends on the deleted conjuncts). → **Delete `hSreg_eq`.**

## The repair (two coupled changes)

### (a) `regStraighten` must equal the straightened FULL reg blocks, not `deepestEPivot`

`DeepestGaugeChart`'s `regStraighten` (the structure field, `DeepestGaugeChart.lean:242`) is contracted
to be `dE(0)=id`, core/spectator-fixing. Its OUTPUT must be the FULL product's reg-block residual,
`E_full(w).1 = (the three reg blocks of reindex(P0·N·QL) packed via regResidualPack)` — i.e. exactly
`(P00−1, P01, P10)` from `hconj`. Then `∑(regStraighten (split w)).1² = Sreg` BY THE LEAF LEMMA's own
`hconj`, with NO `deepestEPivot` / `framedParamsRegPivot` appearing.

- Why `dE(0)=id` survives: the FULL reg blocks have unit transversal Jacobian at 0
  (`A−1 ~ X0+X1`, `B ~ Y1`, `C ~ Z0`; the leaks `Y0T1, T0Z1, Y0Z1` are pure-quadratic, no linear part),
  3 directions = `nReg`. So `E_full` is a genuine `dE(0)=id` local straightening — the SAME contract,
  now reading the right (full) product.
- `deepestEPivot` (and `framedParamsRegPivot`, `framedParamsReg`, `deepestEPivot_sq_sum_eq_blocks`) drop
  to UNUSED for the squeeze. Keep only if PIN1 still consumes them (it reads `deepestEPivot`'s fderiv —
  check PIN1 independently; the PIN1 fderiv `dE(0)=id` is the SAME at 0 whether T=0 or full, since the
  leak is quadratic, so PIN1's derivative fact is likely unaffected — but that is a SEPARATE adjudication).

### (b) `framedParams_split_eq_frame_raw`'s new conclusion

Drop `h00/h01/h10`. Keep: `hconj` (the FULL-product fromBlocks shape) + `hleak` + `hcore_le/hcore_ge`
(core comparability). The squeeze then reads:

    deepest_loss_squeeze:
      Sreg := (P00−1)²+P01²+P10²      -- FULL blocks, from hconj (UNCHANGED naming)
      Score := ‖P11 − P10⅟P00 P01‖²   -- FULL global Schur (UNCHANGED)
      ⟨hlo,hhi⟩ := dlnLoss_two_sided_of_frame … hconj hleak    -- gives (Sreg+Score) ≍ dlnLoss
      -- NEW:  ∑(regStraighten (split w)).1² = Sreg   BY  hregval' : regStraighten.1 = E_full
      --       where E_full(w) = the regResidualPack of (P00−1,P01,P10).  NO h00/h01/h10.
      -- coreΦ identification: deepestCoreF(coreAbsorb…) ≍ Score  via hcore_le/hcore_ge (UNCHANGED).

The squeeze's `c₁/c₂` arithmetic (lines 1566–1602) is UNCHANGED — it already folds `Score`'s
comparability `hcore_le/hcore_ge` into `c₁/c₂`; it never needed `Sreg = Ereg` exactly, only
`∑(regStraighten).1² = Sreg`, which is now an IDENTITY (both are the FULL reg blocks) rather than the
false `Sreg = ∑deepestEPivot²`.

### Decisive coupling to verify before building

`hregval` (`deepest_loss_squeeze` hypothesis, line 1490): currently `regStraighten.1 = deepestEPivot
(q.1, q.2.2)`. Must become `regStraighten.1 = E_full` (the full-product reg residual). The PRODUCER
`deepest_regAbsorb_exists` (`DeepestGaugeConstruction.lean:1697`) supplies `hra_regval`; its `regStraighten`
output must be re-pointed from `deepestEPivot` to `E_full`. **This is the real work** — `E_full` is the
nonlinear straightening of the FULL reg blocks; its `dE(0)=id`/continuity/core-fixing are the same
obligations `regStraighten` already carries, now off the full product. The matrix algebra that
`∑E_full² = Sreg` is then `rfl`/`regResidualPack` bijectivity (NOT a leak-bearing identity).

## Secondary fixes

- (i) last-layer column type: NOT an inconsistency. `framedParamsRegPivot`'s last layer and the bundle's
  `hcorner` are both threshold-row / pivot-column with the SAME `J` threaded (`hpivJ`). With
  `framedParamsRegPivot` no longer in the squeeze path, this concern largely evaporates; if PIN1 keeps
  `deepestEPivot`, the `pivotJSucc J = Jb` threading (`deepest_gauge_construction:1676`) is the reconcile.
- (ii) `endpoint_telescoping` interior interface: `hinterface (s) : Q_s=1 ∧ P_{s+1}=1` for every
  `(s:ℕ)+1 < L`. `hQf0/hPfL` cover only the boundary; for `L ≥ 3` thread `deepestPoint_interior_frame_id`
  (`DeepestFrame.lean:108`, `Q_s = P_s = 1` interior) into `hinterface`. For `L=2` (the current target)
  `hQf0/hPfL` already suffice (no strict-interior interface).

## Banked atoms that feed it (unchanged, sound)

`dlnLoss_two_sided_of_frame` (leaf), `core_comparability_squeeze` (#54, core), `endpoint_telescoping`
(+ interior frame id for L≥3), `exists_deepest_lastLayer_pivotFrame` (`reindex(P0·B·QL)=fromBlocks 1 0 0 0`),
`deepestPoint_frame_normal`, `reindex_fromBlocks_reads_eq_deviation`, `regResidualPack` (bijection).
**Drop from the squeeze path:** `deepestEPivot_sq_sum_eq_blocks`, the T=0 `framedParamsRegPivot` product
identification (was the load-bearer of the false `h00/h01/h10`).

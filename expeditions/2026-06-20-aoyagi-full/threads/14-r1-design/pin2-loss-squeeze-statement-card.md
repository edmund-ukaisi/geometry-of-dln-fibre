# Statement card — PIN2 #80 deepest_loss_squeeze (the L2 loss-squeeze chain)

- **Status:** chain `green-pending-cert`. `deepest_loss_squeeze` is **sorry-free GIVEN** the one
  geometric cert `framedParams_split_eq_frame_raw` (the single isolated `sorry`). Branch
  `origin/fm2/deepest-gauge-chart-sub34` @bec9d794 (frame-wiring migration done). File
  `lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean`. Build GREEN (2719 jobs);
  downstream `DeepestGaugeChart` also green. Sorries in this module: 2 = the cert (mine) +
  `deepestEPivot_regSlice_fderiv_id` (deriv-fm's #91). Only axiom = `monomial_rlct` (S2).

## FRAME-WIRING UPDATE (2026-06-23, the escalation RESOLVED in shape)

The earlier escalation (cert false-as-stated: `framedParams` was an ADDITIVE chart `raw + corM`, not
a frame conjugation) is **resolved by migrating the shared `framedLayer`** (controller call,
Codex-confirmed). NEW:

    framedLayer P Q X Y Z T = reindex(fromBlocks 1 0 0 0) + P · reindex(fromBlocks X Y Z T) · Q

(was `reindex(fromBlocks (1+X) Y Z T)`). The frame is wired into the READING; `split` stays
frameless/MP. `framedParams`/`framedParamsReg`/`deepestEPivot` + the 5 deps thread an **explicit frame
family** `(Pf Qf)`; `deepestPoint_frame` is instantiated only at the cert + `deepest_gauge_construction`.
At the deepest slot the deviation vanishes ⟹ `framedLayer = corM` (frame-independent base), so the
idempotent fold + base/contdiff proofs survive. Migration is GREEN; chain still sorry-free given the cert.

**Two consequences (handoff to deriv-fm, who resumes #82/#91 on this branch):**
- `deepestEPivot`'s reg-slice fderiv at 0 is **no longer `id`** — it is the constant **invertible
  frame-factor** CLM (`Pf_0` left / `Qf_{L-1}` right r-corner action ∘ the shared `regPivotFinEquiv`
  cancel; interior frames id). The `deepestEPivot_regSlice_fderiv_id` `id` statement is the pre-frame
  target, now likely false for a nontrivial frame — restate to the frame factor; in-file ⚠ note added.
- `regStraightenTotalCLM_equiv_of_regBlock_id` (DeepestRegAbsorbIFT) relaxes its hypothesis from
  reg-block = id to reg-block = `IsUnit`/invertible (invertible block + shear is still an invertible
  CLE; consumer needs invertibility only — within crux2's #150 shear-CLE calibration).

## CERT CLOSURE PATH (what remains, precise)

`framedParams_split_eq_frame_raw` is now correctly SHAPED (frame-conjugated, consistent across
cert/chain/assembly). Its remaining content (the genuine geometric core):
1. **round-trip** `framedParams(split w) s = P_s · (paramsSymm w)_s · Q_s` — needs `readX/Y/Z (split w)`
   = the raw-deviation block of `(paramsSymm w − deepestPoint)_s`, i.e. the
   `regGaugeSlotEquiv ∘ regGaugeIdxSplit ∘ roleSplitIdx ∘ paramsEquivFlat` cancellation through
   `subRight deepestFlat` + `deepestPoint_frame_normal` (`P·deepestPoint·Q = corM`). **ENABLER DONE
   (@79e824c6):** `deepestRoleIndexEquiv`'s `eReg` was an OPAQUE `Fintype.equivFin` split, DIFFERENT
   from the `regGaugeIdxSplit` that `regGaugeSlotEquiv`/`readX/Y/Z` use — so the round-trip could not
   cancel. Refactored `eReg := regGaugeIdxSplit` (the two now SHARE the reg-gauge split by
   construction). **Remaining:** the actual `Equiv.symm_apply_apply` cascade through the 4-equiv chain
   — overlaps deriv-fm's banked alignment-cancel bedrock (`regGaugeIdxSplit_symm_*`, fm/deriv-spec
   @cdcb4143, lands on this branch with #82/#91); best closed with that, not re-derived.
2. `endpoint_telescoping` (interior interfaces vanish) ⟹ `prod(framedParams(split w)) =
   P0·prod(paramsSymm w)·QL`. **PROVEN + ready** (DeepestTelescoping). ⚠ Requires the frame family to
   be **id-on-interior + boundary-only** (`Pf_s=1` for `s≥1`, `Qf_s=1` for `s≤L-2`; boundary frames
   only) — the raw `deepestPoint_frame` (Classical.choose) does NOT give id-interior. Consistent
   (interior `deepestPoint_s = corM` ⟹ `1·corM·1 = corM`). **This is the part-(1)/part-(2) COUPLING:
   deriv-fm's round-trip must target this id-interior family** (interior then trivialises:
   `framedParams(split w) s = (paramsSymm w)_s`; only the 2 boundary layers carry a real frame).
3. `reindex(P0·B·QL) = fromBlocks 1 0 0 0`. **REDUCES to part (2) at the deepest point**: `prod(deepestPoint)
   = B` (`deepestPoint_isDeep.1 ⊆ optimalSet`), so `P0·B·QL = prod(framedParams 0) = corM` (my proven
   `prodAux_framedParamsReg_zero`). Clean — no separate B `block_elimination` needed.
4. `core_comparability_squeeze` (#54) — **PROVEN + ready** (gives `∑E²+‖R‖² ≍ ∑E²+‖P11‖²`). **GAP (the
   substantive open piece of my parts):** the link `∑‖R‖² ≍ deepestCoreF (coreAbsorb (split w)).2.1` is
   NOT banked. `R = P11 − P10·⅟P00·P01` is the FULL-product Schur core; `deepestCoreF (coreAbsorb…)` is
   the absorbed per-layer reduced-core loss (`(coreAbsorb q).2.1 = q.2.1 + schurCutoffShift`). They
   agree only mod regular leakage (g156: `R − ∏S_s ∈ ideal(E)`) — a genuine TWO-SIDED comparability
   (the cert's γ₁/γ₂), to be proved. **This is the real remaining content of cert parts (2)-(4).**

## Audit (2026-06-23, build-independent, my parts (2)-(4) readiness)
- Part (2) endpoint_telescoping: PROVEN. Blocked only on the frame-family decision (id-interior).
- Part (3): reduces to part (2) + `prod(deepestPoint)=B`. Trivial once (2) lands.
- Part (4): `#54` squeeze PROVEN; the `‖R‖²↔deepestCoreF` g156-leakage comparability is OPEN (the
  hardest of my parts). Needs the Schur-core ↔ absorbed-reduced-core relation.
- Assembly: mechanical once parts (1)-(4) + the frame family are in place (chain is sorry-free-given-cert).

The ORIGINAL escalation text below is kept as the dead-route record (the bare-split additive chart).

## The delivered theorem (green, modulo the cert)

```text
deepest_loss_squeeze (H) (r) (B) (hB : B.rank = r) (hr) (hL)
    (split  : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (coreAbsorb : DeepestSplit ≃ₜ DeepestSplit) (regStraighten : DeepestSplit → DeepestSplit)
    (hsplit_base : split (paramsEquivFlat H (deepestPoint …)) = 0)
    (hregval : ∀ q, (regStraighten q).1 = deepestEPivot H r hr hL (q.1, q.2.2))
    (hcoreabs : coreAbsorb = deepestCoreAbsorb H r hr hL) :
    ∃ c₁ c₂, 0 < c₁ ∧ 0 < c₂ ∧ ∃ U ∈ 𝓝 (paramsEquivFlat H (deepestPoint …)), ∀ w ∈ U,
      0 ≤ Φ w ∧ c₁·Φ w ≤ dlnLoss H B (paramsEquivFlat.symm w) ∧ dlnLoss H B (…) ≤ c₂·Φ w
  where  Φ w = (∑ i, (regStraighten (split w)).1 i ²) + deepestCoreF H r (coreAbsorb (split w)).2.1
```

`c₁ = ((1+γ₁)·Klo)⁻¹`, `c₂ = Kup·(1+γ₂)`, `Klo = 2(1+t²)·KP`, `Kup = Ki·(2+2t²)`,
`KP = (∑P0²)(∑QL²)`, `Ki = (∑Pi²)(∑Qi²)` — the endpoint-frame energies (positivity supplied by the
cert). The squeeze is **two-sided** (`c₁ < c₂`): the RLCT value `½·minAdm` stays EXACT; the
loss↔Φ relation is a comparability, correctly named (no headline change).

## The cert (the ONE isolated sorry)

```text
framedParams_split_eq_frame_raw (H) (r) (B) (hB) (hr) (hL) (split) :
    ∃ (P0 QL Pi Qi : frame matrices) (t γ₁ γ₂ : ℝ),
      Pi·P0 = 1 ∧ QL·Qi = 1 ∧ 0 < γ₁ ∧ 0 < γ₂ ∧
      0 < (∑P0²)(∑QL²) ∧ 0 < (∑Pi²)(∑Qi²) ∧
      ∃ U ∈ 𝓝 (deepest), ∀ w ∈ U, ∃ P00 P01 P10 P11 [Invertible P00],
        reindex(P0·(prod(paramsSymm w) − B)·QL) = fromBlocks (P00−1) P01 P10 P11
        ∧ P00 = Preg.toBlocks₁₁ ∧ P01 = Preg.toBlocks₁₂ ∧ P10 = Preg.toBlocks₂₁
        ∧ ∑(P10·⅟P00·P01)² ≤ t²·∑E²
        ∧ ∑(P11 − P10·⅟P00·P01)² ≤ γ₂·deepestCoreF (coreAbsorb (split w)).2.1
        ∧ deepestCoreF (coreAbsorb (split w)).2.1 ≤ γ₁·∑(P11 − P10·⅟P00·P01)²
  where  Preg = reindex(prod(framedParamsReg ((split w).1, (split w).2.2)))
```

## The chain (sorry-free given the cert)

1. `dlnLoss_two_sided_of_frame` (banked leaf, sorry-free) on `N = prod(paramsSymm w) − B`, endpoint
   frames `P0/QL/Pi/Qi`, blocks `P00/P01/P10/P11`, leak `t` → `cleanE ≤ Klo·∑N²` and
   `∑N² ≤ Kup·cleanE`, with `cleanE = (∑(P00−1)²+∑P01²+∑P10²) + ∑Rcore²`.
2. `deepestEPivot_sq_sum_eq_blocks` (banked leaf, sorry-free, #120-stable summing bijection) +
   `hregval (split w)` + the block identifications `h00/h01/h10` → the three reg blocks fold to
   `∑ i, (regStraighten (split w)).1 i ²` (the `Sreg = ∑(regStraighten).1²` identity, closed by `ring`
   on the `+`-assoc).
3. The two-sided core comparability (`hcore_le`, `hcore_ge`) folds `∑Rcore²` against
   `deepestCoreF (coreAbsorb (split w)).2.1`; `dlnLoss = ∑N²` by `rfl`.
4. Arithmetic: lower `Φ ≤ (1+γ₁)·Klo·∑N²` ⟹ `c₁·Φ ≤ ∑N²`; upper `∑N² ≤ Kup·(1+γ₂)·Φ`. All folds
   are nonneg-linear (`linarith` with explicit `ring`/`positivity` hints), no `nlinarith` blowup.

## Honest scope / the ESCALATION (what is NOT closed, and why)

**The cert is NOT provable as-stated with the bare `split`.** The architecture's own contract
(`DeepestGaugeConstruction.lean:88`) is

> `gaugeDecode = gaugeSlotRead ∘ frame ∘ (split.symm − deepestFlat)`

i.e. the per-layer frame `deepestPoint_frame` (the `Classical.choose` rank-normal-forms) sits BETWEEN
`split.symm` and the gauge read. BUT:
- `deepest_gauge_construction` (`:775`) supplies `split = deepestSplit_exists` — a **bare** MP
  reindex + translation, **NO frame**.
- `framedParamsReg ((split w).1, (split w).2.2)` reads `readX/Y/Z` **raw** off the split coords
  (`framedLayer = reindex(fromBlocks (1+X) Y Z 0)`, no per-layer frame).

So `prod(paramsSymm w)` endpoint-frame-conjugated by `deepestPoint_frame` telescopes the FRAMED
product (`endpoint_telescoping` + interior-interface vanishing), but the `framedParamsReg` product
blocks `P00/P01/P10` carry **NO frame**. They match the frame-telescoped blocks only if the frame is
composed into the decode (`split`) — which the bare split does not do. This is the #82-class
false-as-stated risk: the math is sound, but the cert references the **wrong (frameless) `split`**.

**FIX NEEDED (controller/crux2-level, not cobuild-local):** wire `deepestPoint_frame` into the decode
— either compose the constant per-layer frame into `split` (so `split.symm` produces the framed
layers), or have `framedParams`/`framedParamsReg` apply the frame inside `framedLayer`. The
`regBoundaryEmbed` structured-equiv technique (deriv-fm) handles the reg-half index alignment, but it
does NOT supply the frame — that is the missing piece. Once the frame is in the decode, the cert's
`reindex(P0·N·QL) = fromBlocks …` closes via `endpoint_telescoping` on `deepestPoint_frame` + the
`framedParams = framed-decode-of-paramsSymm` round-trip, and the core comparability via
`core_comparability_squeeze` (#54, banked).

## Build-env note

Built via a per-worktree writable mathlib mirror (`/home/ubuntu/dgc-sub34-store`, mathlib build
real-copied + `chmod u+w`, rest symlinked) — the shared store was left read-only/untouched (lake
"Replaying" cannot re-stamp the read-only `.olean.hash`, error 13, a box-rotation artifact affecting
all lanes). `lb` re-symlinks to the shared store, so it breaks until the operator's shared-store
chmod restores it for everyone.

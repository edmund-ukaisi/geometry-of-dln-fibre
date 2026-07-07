# Statement card — Step Θ piece 1 (CONJ reg-absorb general-`L`), `hRegAbsorbConj` DROPPED

Thread `genm-hstep2close2`, off `origin/genm-hstep2twostep` (@121e2750). Closing the #120 `hstep2` via
the two-step bridge `Step Θ ∘ Step Ψ_conj`. This card covers **piece 1** — the general-`L` conjugate
reg-absorb — which makes the banked Step Θ (`link2_at_wstar_gaugeReg_gen`) **unconditional**.

Branch `origin/genm-hstep2close2` @ `497f6334`.
Lean modules:
- `lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbConjGen.lean` (new, ~330 LoC, sorry-free)
- `lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeGenTheta.lean` (edited — drops `hRegAbsorbConj`)

## What piece 1 delivers

> **Claim (Step Θ, unconditional).** For `2 ≤ L`, the naive and conjugate absorbed-core energies have
> the same local RLCT at the chart basepoint `wstar`, with NO conjugate-reg-absorb hypothesis:
> `rlctAtOn (∑ (regStraighten (split x))² + coreF(deepestCoreAbsorbConj (split x))) wstar
>  = rlctAtOn (∑ (regStraighten (split x))² + coreF(deepestCoreAbsorb (split x))) wstar`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.link2_at_wstar_gaugeReg_gen` (`DeepestDiffeoBridgeGenTheta` @ `497f6334`)
>   — `hRegAbsorbConj` DROPPED; the new hypotheses `hJfront : J = frontEmbed`, `hPtri`/`hQtri` (per-layer
>   block-triangularity of the frames) are all wire-dischargeable (strict-interior frames are the
>   identity, `deepestPoint_frame_pivot_triangular_exists`'s `hInterior`; boundary layers from the bundle).
> - **Forced `#print axioms`.** `link2_at_wstar_gaugeReg_gen`, `regAbsorb_conj_gen`,
>   `deepestEFull_coreConstant_gen` all `[propext, Classical.choice, Quot.sound]` (clean-three, no `sorryAx`).

### The conj reg-absorb chain (`DeepestRegAbsorbConjGen`, all general `L`, sorry-free)

- **`prod_framedParamsPivot_zeroReg_eq_corner_gen`** — the crux. The reindexed framed product at the
  reg=spec=0 slice is the core-INDEPENDENT block corner `fromBlocks 1 0 0 (junk)`. Proved by a `prodAux`
  prefix corner-telescoping (`prodAux_framedParamsPivot_zeroReg_corner`): each framed layer reindexes to
  `fromBlocks 1 0 0 (T_s)` (`reindex_framedLayer_zeroReads_eq_corner`, banked), and corner blocks fold
  `∏ fromBlocks 1 0 0 T_s = fromBlocks 1 0 0 (∏ T_s)` (`fromBlocks_one_corner_mul` along `reindex_mul_split`).
  This replaces the `Fin 3` two-layer unfold `prodDecode_eq_two_of_L2`.
- **`deepestEFull_coreConstant_gen`** — the value-fold atom `deepestEFull(0,c,0) = deepestEFull(0,0,0)`
  (both corners have `{11,12,21}` blocks `(1,0,0)`; `deepestEFull_eq_of_framedProd_regBlocks_eq`).
- **`deepestEFull_coreInBlock_zero_gen`** — `D(deepestEFull)(0) ∘ coreInCLM = 0` (constant ⟹ zero fderiv).
- **`deepestEFull_conj_hTilde_exists_gen`** — the conj π̃ is a local diffeo at `0` (the conj shift's
  nonzero `Dδ` moves only the core slot, annihilated by `D_E`; the reg-block stays the PIN-1 frame `F`).
- **`regAbsorbPeel_conj_gen`, `regAbsorb_conj_gen`** — the gauge-reg conj reg-absorb (mirror of
  `DeepestL2ConjSub4`'s `regAbsorbPeel_conj`/`regAbsorb_conj`, via `rlctAtOn_comp_localDiffeo` /
  `rlctAtOn_regAbsorb_reduce2`). `regAbsorb_conj_gen` IS the `hRegAbsorbConj` discharge.

- **Verdict on the general lift** (front-loaded in the Θ card, confirmed): **labor, not a wall.** The
  deepest-point corner structure is general; the only genuinely-new lemma is the prefix corner-telescoping,
  the rest is a near-verbatim `Fin 3 → Fin (L+1)` copy of the banked conj-side machinery (all support
  lemmas — `contDiff_schurCutoffShiftConj`, `deepestEPivot_regSlice_fderiv`,
  `regStraightenTotalCLM2_equiv_of_regBlock_isUnit` — were already general).

## Build status

- Isolated green: `scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbConjGen` ✓,
  `…DeepestDiffeoBridgeGenTheta` ✓. `rg`: no name clashes with siblings; no downstream consumer of the
  changed `link2_*` signatures (Theta is a leaf). Full `scripts/lb DLNFibre` tail-stalled under contention
  (sjclose live) — isolated green + rg suffice per the workflow note.

## Remaining to close `hstep2` at general `L` (precise — pieces 2 + 3, NOT done)

The two-step assembled bridge (L2 template `deepest_diffeo_bridge_L2_assembled`) is `LINK1 (Ψ_conj) ∘
LINK2 (Θ)`. Piece 1 makes **LINK2 (Θ) = `link2_at_wstar_gaugeReg_gen`** unconditional. Remaining:

2. **Step Ψ_conj (LINK-1), the coupled bulk — NOT started.** Build the general
   `deepest_diffeo_bridge_gen_conj_impl` (analog of `deepest_diffeo_bridge_L2_conj_impl`):
   `rlctAtOn Φscore = rlctAtOn (∑ (regStraighten (split x))² + coreF(deepestCoreAbsorbConj (ψ (split x))))`
   where `ψ` is the general CONJUGATE core-shear. **This is a large separate construction**: the entire
   existing Ψ_conj machinery is L=2-scoped — `psiSplitRawL2CoreConj` (`DeepestDiffeoBridgeL2Conj`),
   `l2g'Conj`/`l2T1pConj`, `hsub3reg_conj_germ` (takes `hL2eq : L = 2`), `hsub4core_conj_germ` (`Fin 3`) all
   only couple the LAST layer. The general version must couple ALL layers via the honest chain
   `Ĉ_s = reindex(decode s)` (pivot `deepBlkA_s + gaugeReadX_s`) with `blockSchur (partProd Ĉ L) = ScoreSchur`
   (`schur_product_ldu_rec` + `reindex_mul_split`, numerically certified by `genm-hstep2chain`). Banked
   general input: `deepestCoreF_coreAbsorbConj_eq_prodSchur` (reduces the conj absorbed core to
   `frobSqMat(prod(core + schurCorrectionConj))`) — the honest-chain gap is linking that to `ScoreSchur`.
   Size estimate: comparable to `DeepestDiffeoBridgeL2Conj.lean` (168 KB) + the L2 Conj germ files — a full
   separate tide.

3. **Compose Θ ∘ Ψ_conj → `deepest_diffeo_bridge_gen_assembled`** (analog of
   `deepest_diffeo_bridge_L2_assembled`): `rw [LINK1]; exact link2_at_wstar_gaugeReg_gen …`. Then `rw` into
   the `hstep2` sorry at `DeepestL2Wiring:1060` (L≥3 arm; the RHS is the naive `deepestCoreAbsorb` target
   that Θ bridges to). **Blocked on piece 2.** The `hstep2` sorry is left UNTOUCHED (not laundered).

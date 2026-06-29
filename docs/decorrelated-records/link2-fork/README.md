# LINK2 fork — decorrelated pen-and-paper record (2026-06-29)

Decorrelated adjudication of the L=2 conj-side diffeo-bridge fork (`witness` seat, with an
obstruction fallback). Records the exact-algebra verification + the independent Codex read that
overturned the original "ρ fixes the core ⟹ conj-smooth stack avoided" framing.

## Verdict

WITNESS direction is real, but the requested ρ (reg-block-only, conj-smooth-stack-free, ContDiff)
does **not** exist. The actual Lean construction (`psiL2Conj` in
`DeepestDiffeoBridgeL2Conj.lean`) closes the conj `deepestEFull` reg term via the ContDiff
`rlctAtOn_comp_localDiffeo`, whose smoothness IS the conj-smooth stack — necessary (deepestEFull
reads the core bilinearly) AND already paid (the `contDiff_l2*Conj_entry` tower, bottoming out in
`hDA = IsUnit(deepBlkA)`). The Θ-peel (`rlctAtOn_comp_homeomorph`, MP only) handles only the
core-energy `∑q.1²` summand, where the reg term is the core-INDEPENDENT split slot.

## Load-bearing exact-algebra facts (the scripts)

- `link2_model.py` — `bareAbsorb ∘ Θ = conjAbsorb` and `Θ0 = 0`, symbolic, arbitrary continuous
  shifts (CHECK 1); the Θ-peel structure (CHECK 2).
- `link2_fork.py` — the core→reg leak in `deepestEFull` (the matrix-product reg residual reads the
  core bilinearly); block-triangular frames do NOT zero it (CHECK 3/4); the leak is a
  (smooth reg coord)·(core shift) cross term that a core+spec-fixing smooth ρ cannot cancel as an
  exact germ (CHECK 5).
- `link2_order.py` — leak order (O(|q|^3) inside E); the RLCT-sensitivity distinction
  (smooth ρ vs a separate domination argument).
- `link2_Muniform.py` — M-uniformity of the leak/no-leak structure at (2,2,2), (2,3,2), (3,3,3),
  (3,3,3) r=2; AND the compensating smooth joint move `dy = −t·y0/(1+x0)` (rational-smooth under
  pivot invertibility = `hDA`) — the reason ρ exists and is ContDiff under `hDA`.
- `codex_link2_prompt.md` / `codex_link2_answer.md` — the decorrelated Codex consult (xhigh,
  hypothesis withheld). Codex independently produced the germ-smoothness-class-invariance
  obstruction certificate AND the "RLCT could still be equal by domination, not by smooth ρ" caveat.

## Kill-condition

`hDA = IsUnit(deepBlkA)` failing at the relevant point collapses the conjugated inverses'
`ContDiffAt`, hence the whole conj-smooth stack. It is the single foundation seam.

## hDA seam — dischargeable with scope (the kill-condition resolved)

`hDA_check.py` adjudicates whether `hDA = IsUnit(deepBlkA s)` (= the leading `r×r` block
`(reindex(deepestPoint s)).toBlocks₁₁` invertible) is forced by the deep-layers structure.

- **Not forced by the bare `IsDeepLayers`** (rank-`r` layers + boundary tail-zero): exact
  obstruction WITNESS — a rank-`r` boundary layer `w0 = [[1,0,0],[0,0,0],[0,1,0]]` (cols ≥ r zero,
  rank 2) whose top-left `2×2` is singular. The rank can sit in the bottom rows.
- **Dischargeable under a front-pivot ROW WLOG** (`htop : (B's top-r-rows).rank = r`). A rank-`r`
  factor always has `r` independent rows, so a row-permutation (absorbed into the boundary gauge,
  preserving optimalSet / loss / rank) brings the pivot rows to the top ⟹ leading block invertible.
  This is the row-analogue of the front-pivot COLUMN WLOG (`hJfront`) already in
  `deepest_gauge_construction`.
- **Already proven in source**: `deepestPoint_leadingBlock_isUnit` in
  `DeepestLeadingBlock.lean` (origin/genm-l2fin, sorry-free) concludes `IsUnit(deepBlkA 0)` from
  exactly `htop`, via front-peel + the layer-0 tail-columns-vanish conjunct.

So hDA is **not an obstruction**; it is a scoped WLOG (the front-pivot row condition), discharged.
The remaining honest work is threading `htop` / the row-WLOG seam (and the `hDA1` last-layer
analogue) through the producer, alongside the already-present column WLOG.

Reproduce: `python3 <script>.py` (sympy 1.14).

## LINK2 route decision — the two sharp questions (2026-06-29, second dispatch)

The controller sharpened to two exact-algebra questions deciding the LINK2 route. Both answered.

### (1) Is `coreF(bareAbsorb(ψq)) = coreF(conjAbsorb(q))` near wstar? — **FALSE** (definitive)

`ψ = psiSplitRawL2CoreConj` (the conj joint move, core ↦ T1'c). This is the single-bridge
(option-b) core identity. EXACT-RATIONAL WITNESS (`q1_witness.py`, (2,2,2) r=1, the fairest
setting — forced `schurConj = schur` to isolate the moved-vs-original difference):

- `coreF(bareAbsorb(ψq)) = 6053384292071/400000000000000000`
- `coreF(conjAbsorb(q))  = 14641/914457600`
- differ (diff ≈ −8.77e-7).

The two energies AGREE exactly at wstar (reads=0, diff=0) but DIVERGE at second order off it
(`diff = −eps²/88200 + eps⁴/47040`). M-uniform (the reduced core at r=1 is scalar for all H).
Structurally: `(1)` would need `bareAbsorb(ψq)=Score` (the FALSE W-a hLDUtie) AND `Score=conjAbsorb(q)`
(also false — Score is the joint-MOVED Schur complement, `conjAbsorb(q)` is the un-moved one); two
false links, and the witness confirms no cancellation. ⟹ **The Θ-peel route is NECESSARY**, not
scaffolding. Deliverable is (2).

### (2) Does `link2_rho_residual` close, and by what mechanism? — [SUPERSEDED by the third-dispatch CORRECTION below: the model here OMITTED the spec slot; comparability is FALSE]

`link2_rho_residual : rlctAtOn(∑R'(q)² + C) 0 = rlctAtOn(∑R'(Θq)² + C) 0`, `C = coreF∘conjAbsorb`
FIXED both sides, `Θ = thetaConj`, `R' = regStraighten.1 = deepestEFull`.

Answer: it holds, by Watanabe two-sided comparability `(1−ε)F ≤ F_moved ≤ (1+ε)F`, ε→0 at 0
(`link2_rho.py`, `link2_honest.py`; Codex-confirmed `codex_rho_answer.md` — both germs comparable to
a controlled quadratic). **First-order core-blindness alone does NOT suffice** at the RLCT level
(higher-order perturbations can move the RLCT — Codex's `x²+y¹⁰` example). The load-bearing triple:
1. atom `deepestEFull_coreConstant` (on-slice value-constancy) ⟹ `ΔR = R'(Θq)−R'(q)` carries a REG
   factor (vanishes when reg=0);
2. `Θ0=0` ⟹ the core shift `delta` carries its own →0 factor;
3. PIN-1 `dE(0)` invertibility ⟹ `∑R'²` dominates the reg directions.
Then `F_moved − F = ∑(2R'ΔR + ΔR²)` (C cancels — same both sides), each term ≤ ε·∑R'² ≤ ε·F.
**C's core-degeneracy (the singular DLN multiplication map) NEVER enters the denominator** — only
`F ≥ ∑R'² ≥ 0` is used. So `link2_rho_residual` closes via comparability, NOT a reg-side diffeo.

The honest residual for the formaliser: this is an `rlctAtOn`-comparability lemma (a
`c1·H ≤ H' ≤ c2·H ⟹ equal rlctAtOn` interface + the explicit ε-bound from the three inputs above),
NOT a `rlctAtOn_comp_localDiffeo`/`_homeomorph` application. If that comparability interface is not
yet banked, it is the new piece (Watanabe-standard; integrability-threshold sandwich).

## CORRECTION (third dispatch) — the comparability route for `link2_rho_residual` is DEAD

The dispatch-2 (2) analysis above had a hole: it modeled `ΔR` with only reg coordinates and OMITTED
the spec slot. The red-team (`codex_epsbound_answer.txt`) flagged it; adjudicated by exact algebra
against the REAL index routing (`DeepestSplitReindex.regBoundaryToRegGauge`): the reg slot routes onto
only `{X_first, Y_last, Z_first}`; everything else (incl. `Y_first`, `Z_last`) is SPEC. The core leak
rides `Y_first` (=Y0) and `Z_last` (=Z1) — both SPEC. So:

- **FIX 1 (atom on full {reg=0}) — FALSE** (`fix1_verify.py`): `deepestEFull(0,c,s)` depends on `c`
  for `s≠0` (`P12 ⊃ T1·p`, `P21 ⊃ T0·q`, `p,q` spec).
- **FIX 2 (Θ-shift carries reg factor) — FALSE** (`fix2_real.py`): `delta_0=−Zbar0·p/(1+u)`,
  `delta_1=−Ybar_last·q/(1+x)`; at reg=0 these ride spec `p,q` ≠ 0.
- **FIX 3 (R' dominates spec) — FALSE** (`fix23_check.py`): spec is a gauge/spectator direction;
  `∑R'²` is spec-degenerate (`R'_11 ⊃ p·q`).
- **The comparability statement itself — FALSE on every small ball** (`codex_fix_witnesses.py`,
  Codex-found + here-verified exact; `A=deepBlkY_last`, `B=deepBlkZ_0`):
  - W1 `u=−t²,x=0,p=q=t,v=w=0,T0=Bt/(1−t²),T1=At`: `F=0`, `Φ>0` ⟹ no `c₁>0`.
  - W2 `…,w=−Bt²,T0=Bt,T1=0`: `Φ=0`, `F>0` ⟹ no finite `c₂`.
  - W3 `u=−t²+t³,…`: `F/Φ ~ (A²+B²)t⁻² → ∞`.

`F` and `Φ` have DIFFERENT zero sets, so `rlctAtOn_squeeze` does NOT apply. The team's `c₁=1/2,c₂=3/2`
are not just wrong constants — no fixed constants exist. (The dispatch-2 random sample `F/Φ∈[0.69,1.26]`
was a mirage: integer rays miss the fine-tuned cancellation locus. MC never certifies comparability.)

**Critical-path impact: NONE.** `link2_rho_residual` is TRUE (equivalent to LINK2) but unprovable by
integrand comparability. It was an ALTERNATIVE decomposition (Θ-peel + reg-swap) to avoid the
conj-smooth stack; that decomposition's reg-swap leg is the dead route. The LIVE route,
`deepest_diffeo_bridge_L2_conj_impl` (the `psiL2Conj` full ContDiff bridge), is **sorry-free** and does
NOT consume `link2_rho_residual` (consumed only in `ScratchL2Link2.lean`). It moves reg+core JOINTLY —
exactly the necessity dispatch-1 established. Recommendation: drop the Θ-peel/reg-swap decomposition;
LINK2 already closes via `psiL2Conj` (cost = the conj-smooth stack, already paid via `hDA`).

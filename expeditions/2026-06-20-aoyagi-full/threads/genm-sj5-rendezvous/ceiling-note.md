# genm-sj5-rendezvous — ceiling note (formaliser `asmbase`, 2026-07-14)

Branch `genm-sj5-rendezvous` off canonical `expedition/aoyagi-full`. After deep mapping (all 7
authoritative files + the crux/connector/assembly chain + Codex architecture pass), the Lean tree was
RESET to clean canonical (no laundered sorries, aggregator unbroken). This note is the honest handoff:
what is verified, the ceiling reached, and the ordered remaining bricks. Codex artefacts:
`codex/rehome-{prompt,answer}.md`.

## 1. Verified topology (from `import` lines) — the re-home is forced

`DeeperFlagCore → HeadSplitDom → PivotDom → PivotFin` (arrows = imported-by). The proved crux
(`pivotPeel_domination`, `forward_LHS_finiteness`) is the MOST DOWNSTREAM file (PivotFin). The entire
head-split assembly (`deeperFlag_shell_le`/`deeperFlag_spineToCore`; the `headSplit_domination`,
`headSplit_pivotDom`, `pivotDom_*` stubs) is UPSTREAM of the crux ⟹ the recon's "T1: one-line `exact`
stub→impl" is a CYCLE and not literally possible. Resolution (Codex-endorsed, no cycle): re-home the
whole head-split chain (`deeperFlag_spineToCore` + `deeperFlag_shell_le` + a clean `headSplit_domination`)
into a NEW sink file R downstream of PivotFin + GoodConnector + WaistConnector; delete the dead upstream
stubs. R is a valid sink (no cycle). Connectors are already parameterized (GoodConnector takes
hstrict/hsat/hsector; WaistConnector takes hred) — they don't import PivotFin, R supplies their hyps.

## 2. Confirmed-safe / de-risked findings (bankable)

- ~~**`hjr : j < r` is VESTIGIAL**~~ **← CORRECTED (rvprep, 2026-07-15): this "confirmed-safe" bank is FALSE — `hjr` is LOAD-BEARING.** Empirically: dropping `hjr` and rebuilding → `RouteMSJShellContain.lean:182:4: omega could not prove the goal`. The `omega` in `hj_eq` derives `weakEigCount ε Zf = ↑j` from `min(weakEigCount ε Zf, r) = ↑j`, which NEEDS `↑j < r` (at `↑j = r`, min gives only `w ≥ r`). `omega` SILENTLY consumes `hjr`, so a name-grep misreads it as "unused" — **the omega trap** (this is why the original "grep-verified unused" was wrong). **Do NOT relax `hjr`.** The j=r saturated shell is GENUINE content, already handled the RIGHT way by rescopefin's **j-agnostic** `RouteMSJShellSubset.shellSpineIntegrand_le_layerBox` (shell integrand ≤ full-box integral, bypassing the shell restriction + the crux entirely). USE THAT at rendezvous for j=r, not a hyp-drop.
- **T3 frame-strip is OPTIONAL for the load-bearing build** (cosmetic/bedrock only). Codex + direct read
  confirm `{m,hcvg,hmM,ε',hε',U_sf,hUs,hrank,hfloor}` are unused in `pivotPeel_domination`'s body. R can
  either strip them or supply them from Brick F (`exists_headSplitFrame`) in the moved `spineToCore`.
  (Deferred; flag as deviation if unreached.)
- **Degenerate `hnd`**: in R's good branch, `by_cases (∀ i, 1 ≤ M i)`; the `¬` case gives `∃ i, M i = 0`
  ⟹ `minAdm M = 0` (via `minAdm_le_head_mul_tailInf`: i=0 kills the head factor, i≥1 kills the tail inf)
  ⟹ `carrierThreshold = 0` ⟹ `DecoratedBoxThresholdFinite` vacuous. Sound (Codex-confirmed).
- **Waist/(d) knot** (Codex-endorsed): WaistConnector's `deeperFlagWaist_finite_impl` bakes a call to the
  DecoratedStep (d) STUB `deeperFlagGood_finite` (sorry) on `rev M`. Fill is impossible in place (needs
  crux downstream). Fix = refactor WaistConnector to take the (d)-callback as a hypothesis `hgoodconn`
  (dependency inversion; same L, same hIH on `M∘Fin.rev`); R supplies the clean (d). No cycle.
- **`hcvg` is NOT droppable** (checked per controller steer): `deeperFlag_shell_core_le` genuinely
  consumes `hconv` in its body (`deeperFlagUnifConst_lt_top ... hconv`, line 396). `hconv` comes from
  `hcvg`. So the covervalid hcvg Nat-lemma (~30-50 LoC, off-sector) IS required — not the "drop the hyp"
  path.
- **O1 extraction** (`decoratedBoxThresholdFinite_of_routeMBoxThresholdFinite`) is clean: the
  `suffices hbox` block in `deeperFlagGood_finite_impl` (GoodConnector @374-490) does NOT use
  hnd/hstrict/hsat/hsector/hgoodpiv; it reduces `DecoratedBoxThresholdFinite D` (per c') to
  `routeMLayerBoxIntegral M c' 1 < ⊤`. `carrierThreshold M = minAdm M/2` = `RouteMBoxThresholdFinite`'s
  threshold, so the extraction boundary is exactly the `suffices`. Extract as a standalone lemma; R uses
  it as `hred` for WaistConnector.

## 3. THE CEILING — the first blocker: T2 `shellSpine_le_hsQ_box` (shell-restricted) is UNRESOLVED

This gates the entire re-home (`deeperFlag_shell_le`'s proof goes `spineToCore → headSplit_domination →
shellSpine_le_hsQ_box + pivotPeel_domination`). It is NOT "bounded measure-reorg wiring". The soundness
of its shell-restricted target is unclear:

- `shellSpineIntegrand` (DeeperFlagCore) integrates the outer `A'` over
  `paramsBoxM ∩ {A' | prod (tailChain M) A' ∈ singularShell ε r jf}`.
- `singularShell ε r j := {Z | min(weakEigCount ε Z, r) = j}` (`RouteMSJShellCover`) ⟹ for **j ≥ 1** the
  shell has ≥ 1 singular value < ε, i.e. `σ_min(prod) < ε`.
- Step2's `shellSpine_le_hsQ_box` (my worktree @210) RHS restricts `A_cor` to
  `matBox ∩ pivotShell M u ε Zf z`, and `pivotShell = {A_cor | (hsQ·hsQᵀ − ε²·1).PosSemidef}`, i.e.
  `σ_min(hsQ) ≥ ε`.
- `hsSplit_good_of_shell` puts shell points ON the good set, so `Zf z = Z_deep z` (the ACTUAL product, no
  floor). Then `hsQ = fromRows(pivot)(A_cor · Z_deep)` — for j ≥ 1 this inherits `σ_min < ε`, so the
  transported `A_cor ∉ pivotShell`. Hence the shell-j (j≥1) points are EXCLUDED from step2's RHS, making
  `shellSpineIntegrand(shell j≥1) ≤ ∫_{pivotShell} …` look FALSE unless the integrand vanishes there.
- Step2's signature OMITS the floor (`hfloor`/`U_sf`), which is the only apparatus (piecewise floored
  frame + Ky-Fan, D-C style) that could establish the pivotShell restriction. The recon's own suggested
  method ("drop the shell indicator, use ≥0") yields the NON-shell bound (`≤ ∫_{matBox}`), which does
  NOT match the shell-restricted target the crux consumes (the crux `pivotPeel_domination` bounds the
  SHELL-restricted `pivotDomLHS`; the row-Gram floor `frobSq(T·Q) ≥ ε²·frobSq(T)` NEEDS `pivotShell`).

`shellSpine_le_hsQ_box` was NEVER proven (a `sorry` on step2; only `pivotPeel_domination`/
`forward_LHS_finiteness` were fidelity-passed — NOT shellSpine). **Resolving T2 needs the crux authors'
design intent** (cruxfin/rhsfin — `rhsfin` is active in this session): was the shell-restriction meant to
carry the floor (making T2 a genuine D-C/Ky-Fan proof with `hfloor`/`U_sf` added to its signature), or
should `pivotDomLHS`/the shell-restriction be reconciled? This is a knowing decision for the controller,
not a mechanical fill.

## 4. Remaining bricks, ordered (all downstream of T2)

1. **T2** `shellSpine_le_hsQ_box` shell→pivotShell (see §3). GENUINE, design-gated. Critical path.
2. **hcvg Nat-lemma** (covervalid `threads/genm-covervalid/`, ~30-50 LoC): off-sector `1 ≤ j < r` ⟹
   `hcvg`. Real dependency (§2). Needed for hstrict/hsat.
3. **hstrict / hsat** = `deeperFlag_shell_le` (moved to R, clean) + `hIH` on the reduced comparator +
   threshold bookkeeping (`minAdm_le_peelCharge_add_redChain`: `c' < minAdm M/2 ⟹ c'−peelCharge/2 <
   minAdm(redChain)/2`) + a c'≤peelCharge/2 "small-c'" regime bound. Medium.
4. **hsector (j=0)** (covervalid cert): (i) `a+b ≤ M2 → #120 sjSector`/`uniformWenn_le` (banked, no
   crux); (ii) `a+b = M2+1` borderline → the crux. Theorem `a★+b★ ≤ M2+1` always. Genuine assembly to
   `shellSpineIntegrand(j=0) < ⊤`; NOT banked as such.
5. **Re-home mechanics** (bounded, all downstream of 1-4): move `deeperFlag_spineToCore` +
   `deeperFlag_shell_le` to R (nothing else uses them — only docstrings + AxCheck audit reference them;
   grep-verified); build clean `headSplit_domination_R` (= old `headSplit_domination_impl` body, calling
   `pivotPeel_domination` with `hu` from `ht1`, supplying the frame from Brick F); O1 extraction;
   WaistConnector `hgoodconn` refactor; delete dead stubs (PivotDom 4, HeadSplitDom 2, DeeperFlagCore
   stub, DecoratedStep a/b/c/dispatch — keep (e) + `deepTailMin` + bricks); assemble
   `decoratedStepHyp_dispatch_R` (3-way) + `decoratedDescent_holds : DecoratedDescent`; HeadlineL1Mint
   imports R, replaces the sorry; wire aggregator + AxCheck; TRUE-mint cleanup (delete `_legacy`, drop
   `MintRehearsal108`).

## 5. Recommendation

The crux (u≥1) + O2 + (e) + the connectors are done. But the crux→connector BRIDGE (T2 + hstrict/hsat +
hsector) is genuinely unbuilt analytic assembly, and T2's shell-restricted soundness is a design question
for the crux authors. Suggested decomposition: (a) resolve T2 with `rhsfin`/cruxfin (design intent +
signature: does shellSpine carry `hfloor`? is the D-C/Ky-Fan the intended proof?) — this is the pivotal
brick; (b) a focused tide for hcvg-lemma + hstrict/hsat + hsector (consuming the covervalid cert); (c) the
mechanical re-home + mint (§4.5) once (a)/(b) land. The mechanical re-home is straightforward once the
bridge exists.

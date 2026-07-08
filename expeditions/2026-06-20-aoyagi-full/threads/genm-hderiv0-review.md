# Fidelity review — `hderiv0` (`hasStrictFDerivAt_psiSplitDeltaGen_zero`)

Reviewer thread, wall D1 #120, Producer-1 diffeo-triple leaf #2/3.
Target canonical `@b177b361`, file
`lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiHderiv0Gen.lean:1682`.
Audited in isolated worktree `/home/ubuntu/workspace/revhderiv0-wt`.

**Verdict: survived — clean PASS on all four dimensions.** One non-blocking caveat (the
end-to-end compose is deferred; the hyp bundle is nonetheless provably the standard bundle).

## 1. FIDELITY — PASS

Conclusion (verbatim):
```
HasStrictFDerivAt (fun q => psiSplitRawGen H r hr hL J Pf Qf q - q)
  (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0
```
- Deviation `q ↦ psiSplitRawGen q − q` (not the map itself), derivative arg is the **zero CLM**,
  base point is `0`. `HasStrictFDerivAt` (stronger than `HasFDerivAt`). This is the correct encoding
  of "D(deviation)(0)=0", i.e. `D(psiSplitRawGen)(0)=id`.
- `psiSplitRawGen` is the **real joint move** (`DeepestPsiSplitRawGen.lean`): per-layer forced-decode
  reads (`forcedDecodeLeft/Right`) of the moved chain `movedC C Z0e − corM`, packed back through
  `regGaugeSlotEquiv.symm` / `paramsEquivFlat`. Not a trivialised `id` stand-in.
- Consumer shape match: `hasStrictFDerivAt_deepestPsiCutRaw_zero` / `hasStrictFDerivAt_deepestPsiFlatCut`
  (`DeepestPsiFlatCutGen.lean:78,131`) take `hderiv0 : HasStrictFDerivAt (fun q => psiSplitRaw q − q) 0 0`
  for an abstract `psiSplitRaw`. The target's conclusion is **exactly** this with
  `psiSplitRaw := psiSplitRawGen H r hr hL J Pf Qf`.

## 2. HYP-MATCH + NON-VACUITY — PASS (load-bearing)

Bundle: `hL, hL2, hJfront, hQf0, hPfL, hPunit, hQunit, hPtri, hP22, hQtri, hQ22, hInterior`.

- **Byte-identical to `psiSplitRawGen_deepestChain_hmove`'s bundle** (`DeepestHmoveGen.lean:82`) —
  confirmed by textual diff of the four `reindex … toBlocks` block hypotheses (IDENTICAL) and by
  matching hypothesis-name sets. The target genuinely routes through `hmove` (line 1190). No
  hypothesis is added beyond hmove's.
- **Same bundle the germ producer already carries.** `hsub3reg_gen_germ`
  (`DeepestChainUnitGerm.lean:655`), which proves the reg-energy germ the downstream assembly
  consumes for the concrete `psiSplitRawGen`, takes the same `hQf0,hPfL,hPunit,hQunit,hPtri,hP22,
  hQtri,hQ22,hInterior` bundle and threads it into `hmove` (line 727). So hderiv0 requires exactly
  what the established germ path already requires — no divergence, no mis-scope.
- **Non-vacuous.** `Pf = Qf = 1` (identity on every layer) satisfies the whole bundle: `reindex e e 1
  = 1`, `toBlocks₁₂ 1 = 0`, `toBlocks₂₂ 1 = 1`, `toBlocks₂₁ 1 = 0`, and interior/boundary identity.
  No hidden inconsistency among `hPtri/hP22/hInterior/hQf0/hPfL`.
- **Dischargeability.** The abstract assembly `deepest_diffeo_bridge_gen_assembled`
  (`DeepestDiffeoBridgeGenConj.lean:110`) does not itself list `hP22/hQ22/hInterior` — it takes the
  germs as hyps and consumes `hderiv : D(psi)=id` abstractly. But the **deferred concrete full-compose**
  that instantiates `psiSplitRaw := psiSplitRawGen` must produce the germ via `hsub3reg_gen_germ`,
  which **already forces** `hP22/hQ22/hInterior` into that compose. The same concrete normal-form
  frames therefore discharge hderiv0's identical bundle. No gap where assembly-only frames (∀-s
  `hPtri/hQtri`) could satisfy the assembly while violating hderiv0's extra hyps, because the germ
  production — required by the same compose — pins `hP22/hQ22/hInterior` regardless.

## 3. LAUNDERING — PASS

The frame hyps constrain only `Pf/Qf` (boundary block-triangularity + interior identity), not the
variable `q` and not the derivative witness. They do not assert `psiSplitRawGen = id` or `D = 0` by
fiat. `psiSplitRawGen` is a nontrivial forced-decode map (§1), and the same bundle drives the
nontrivial `hmove`/germ path — the theorem is not hollow. Conclusion is not smuggled through a
hypothesis.

## 4. BUILD — PASS

- Force-recompiled in worktree (`touch` + `./scripts/lb …DeepestPsiHderiv0Gen`): exit 0,
  `Build completed successfully (2757 jobs)`. Only `linter.style` warnings (show/longLine), no errors.
- `#print axioms hasStrictFDerivAt_psiSplitDeltaGen_zero` (scratch import) →
  `[propext, Classical.choice, Quot.sound]` — **clean-three**, no `sorryAx`.
- No `sorry/admit/native_decide/axiom` in the target file. Two direct imports carry sorries in
  *other* theorems (`DeepestPsiSplitRawGenMove` ×1, `DeepestDiffeoBridgeL2` ×2); the axiom trace
  confirms these are **off the target's dependency path**.

## Caveat (non-blocking)

The end-to-end wiring — instantiate `psiSplitRaw := psiSplitRawGen` into `deepestPsiFlatCut` and pass
`hderiv0 := hasStrictFDerivAt_psiSplitDeltaGen_zero` to `hasStrictFDerivAt_deepestPsiFlatCut` — is
**deferred** (Producer-1 "triple + compose" per `DLNFibre.lean:826,839`). So hderiv0's discharge is
not yet exercised in Lean end-to-end. This is expected for a leaf and is a future review target; it
does not weaken hderiv0, whose hyp bundle is provably the standard Producer-1 bundle.

## Decorrelated Codex

`codex/{fidelity-prompt,fidelity-answer}.md` (xhigh, read-only): SOUND on all four, with correct
INFERENCE flags on the "identical bundle" claim (D) and psiSplitRawGen non-triviality (C) — both of
which I verified against source (byte-diff §2; definition §1).

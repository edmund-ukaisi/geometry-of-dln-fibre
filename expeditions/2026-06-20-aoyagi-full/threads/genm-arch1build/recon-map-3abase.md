# recon-map-3abase — the arity≥4 (3a) base-assembly map

**Seat:** self-recon (read-only cross-branch inventory), aoyagi-full Stage 2, `genm-arch1build`.
**Date:** 2026-07-16. **NO build, NO merge** (per controller; the (3a) formaliser build is a separate task
gated on `deephier`'s hierarchical-case verdict). De-risks the base so the build starts immediately.

**(3a) TARGET.** `RouteMBoxThresholdFinite M` (`M : Fin (n+1) → ℕ`, `n ≥ 3`, i.e. arity ≥ 4) via:
box → shell cover → per-shell finiteness [front gate `clsCodim_gate_genL` × deep-stratum gate
`deepGate_branch`(+CR (I)) + deep atlas `deepRankLE_lintegral_lt_top` + `shellSpine_le_frontCharge`
(hZrank/hEtopae) + per-stratum radial `single_block_stratum_lt_top`] → sum → (□). The mint consumes (□)
DIRECTLY (`RouteMSJMint`, not the L≥1-unsound `cornerComparator` descent — confirmed by reassembly/diagbfix).

**★ HEADLINE.** The base is in far better shape than "~2 sorries" implied: **every named component is
sorry-free and located**; the deep-atlas modules are sorry-free (the "1 sorry" greps were the `sorry-free`
docstring). The two genuine (3a) Lean gaps are **UNBUILT ASSEMBLY theorems** (not sorries in existing
modules): (G1) per-shell joint finiteness, (G2) the ∀-arity box→shell→sum→(□). The merge is CLEAN (three
cherry-picks onto `genm-arch1build`, all deps present, no name clashes, CR-infra byte-identical).

---

## (a) Component inventory — branch + commit + sorry-free

`genm-deepatlas` tip = `323f40776`. `genm-arch1build` = `6e0ee0f31` (= deepatlas + my 3, GREEN base).

| component | module | branch @commit | sorry-free? |
|---|---|---|---|
| `routeMBoxThresholdFinite_mnp` (arity-3 (□) base) | RouteMSchurRectCapB:453 | deepatlas 323f40776 (+all descendants) | ✔ (clean-three) |
| `shellSpine_le_frontCharge` (step1+2, needs hGae/hEtopae) | RouteMSJIncidenceAssembly:610 | deepatlas 323f40776 | ✔ |
| `clsCodim_gate_genL` (front gate, general-L) | RouteMSJIncidenceAssembly:723 | deepatlas 323f40776 | ✔ |
| `deepRankLE_lintegral_lt_top` (deep coverage glue, needs hfin) | RouteMSJDeepCoverage:175 | deepatlas 323f40776 | ✔ |
| deep-atlas charts (Atlas/Cover/Pivot/Index/Codim/ChainPeel/Factor) | RouteMSJDeep*.lean | deepatlas 323f40776 | ✔ (ALL sorry-free — docstring-only "sorry-free" mentions) |
| **hZrank** `deepFactor_hZrank_of_le` / `deepFactor_rank_ge_deepTailMin_ae` | RouteMSJDeepRankGen | arch1build 6e0ee0f31 | ✔ |
| **hEtopae** `deepFactor_hEtopae` / `frobSq_stack_pos_ae` | RouteMSJPivotEnergyPos | arch1build 6e0ee0f31 | ✔ |
| **per-stratum radial** `single_block_stratum_lt_top` | RouteMSJStratumRadial | arch1build 6e0ee0f31 | ✔ |
| **deep-stratum gate** `deepGate_branch` / `deepGate_uρ_branch` | RouteMSJDeepGate | **genm-sj5-stepbuild** 83703cbbf | ✔ (0 sorry/decide/admit) |
| **CR (I) input** `minAdm_le_compositeRank_add` (`hI`) + `CRrec` | RouteMSJCompositeRank | **genm-crstrat** 66a54b428 | ✔ |
| `shellSpineIntegrand_le_layerBox` (shell ⊆ box, trivial-finiteness) | RouteMSJShellSubset | **genm-sj5-rescopefin** c7cb8a591 | ✔ |
| `RouteMSJShellCover` / `singularShell` (shell cover) | RouteMSJShellCover | deepatlas 323f40776 | ✔ |
| arity-3 anchor (`cornerComparator_integral_eq`×2) | RouteMSJArity3Anchor | genm-arch1asm (UNCOMMITTED) | ✔ but LIMITED use (comparator route, L≥1-unsound); OFF live path |

"canonical" (arch1asm's phrasing) = the integration line carrying `routeMBoxThresholdFinite_mnp`
(genm-deepatlas + descendants); NOT `dev` (`routeMBoxThresholdFinite_mnp` is not on `dev`).

---

## (b) MERGE PLAN — three cherry-picks onto arch1build (CLEAN)

**Base = `genm-arch1build` @6e0ee0f31** (deepatlas + my 3; GREEN, 8406-job build per arch1asm). It already
carries: incidence assembly, front gate, deep-atlas (sorry-free), deepRankLE, routeMBoxThresholdFinite_mnp,
RouteMSJShellCover, hZrank/hEtopae/single_block.

**Cherry-pick 3 modules (all deps already on the base — verified):**
1. `RouteMSJDeepGate.lean` (from `genm-sj5-stepbuild`) — imports ONLY `RouteMSJDecoratedCharge` (present); uses `RouteMLayerSplit`/`RouteMSJIncidenceExponent` (present).
2. `RouteMSJCompositeRank.lean` (from `genm-crstrat`) — imports `MinAdmPermInvariance` (present) + `Mathlib.Logic.Equiv.Fin.Rotate`. Supplies `deepGate_branch`'s `hI`.
3. `RouteMSJShellSubset.lean` (from `genm-sj5-rescopefin`) — imports `RouteMSJHeadSplitDom` + `RouteMSchurRectCapB` (both present).

**Conflict analysis:**
- NO name clashes among the picked pieces (rg: `deepGate_branch` only on stepbuild; `shellSpineIntegrand_le_layerBox` only on rescopefin; my 3 unique; `minAdm_le_compositeRank_add`/`CRrec` unique).
- CR-infra deps `Core/ResidualRank.lean` + `D1ResidualRankIdentity.lean` are **byte-identical** deepatlas↔stepbuild (no divergence). RouteMSJCompositeRank's only Core-ish dep (`MinAdmPermInvariance`) is on the base.
- stepbuild/crstrat/rescopefin are SIBLING lineages (merge-bases `12a7ae38a`/`12a7ae38a`/`80932d884`, all older than deepatlas tip) — so **cherry-pick the individual .lean files, do NOT `git merge` the branches** (a full merge would drag their divergent copies of shared modules). File-level cherry-pick is safe because each picked module's deps are already present at ≥ their versions.
- **Aggregator gate (lean/CLAUDE.md):** after the 3 picks, add the imports to `DLNFibre.lean` and green-gate the FULL `lake build DLNFibre` (not just per-module `scripts/lb`) — this is the only way to catch a sibling name-clash the isolated build misses. `rg` the new top-level names once more against the full aggregator's modules before wiring.

Alternative (if cherry-pick friction): `git checkout genm-arch1build; git checkout genm-sj5-stepbuild -- lean/…/RouteMSJDeepGate.lean` etc. (path-checkout, same effect, no history merge).

---

## (c) The remaining (3a) Lean gaps — TWO UNBUILT ASSEMBLY theorems (not sorries)

The deep-atlas + gate + CR (I) + front pieces are ALL sorry-free. `deepGate_branch` has **NO consumers on any
branch** ⟹ the assembly is genuinely unbuilt. The gaps:

- **G1 — per-shell joint finiteness (the joint stratified atlas assembly).** UNBUILT. Statement (to build):
  for a good binding shell cut, the per-shell integrand is finite — wiring `shellSpine_le_frontCharge`
  (discharge hGae via `deepFactor_hZrank_of_le`+`hGae_from_deepRank`, hEtopae via `deepFactor_hEtopae`) →
  `frontCharge_factor`/`frontLoss_pivotPoly_eq` → the joint (front `clsCodim_gate_genL` × deep
  `deepGate_branch`(hI:=`minAdm_le_compositeRank_add`)) stratified atlas → per-stratum radial
  (`single_block_stratum_lt_top` + the ℓ=0 twoBlock, §4) → `deepRankLE_lintegral_lt_top` (discharge `hfin`
  from the per-cell gate+radial) → per-shell `< ⊤`. This is the ARITY≥4 analogue of the arity-3 §3.1
  mechanism, with the deep factor NON-trivial (deep gate active). `hfin` for `deepRankLE` is discharged HERE
  (per-cell = per-deep-stratum radial-finite via `deepGate_branch`'s `C_k ≥ 2T1_q`).
- **G2 — the ∀-arity box→shell→sum→(□) assembly.** UNBUILT. `RouteMBoxThresholdFinite M` (arity≥4) via:
  box → `singularShell`/`RouteMSJShellCover` finite shell cover → per-shell finiteness (G1) →
  `lintegral_lt_top_of_finite_cover`/sum → (□). The base case (arity 3) is `routeMBoxThresholdFinite_mnp`
  (banked); `shellSpineIntegrand_le_layerBox` gives the off-shell / shell⊆box a-fortiori legs.

Sub-obligations inside G1/G2 (all banked machinery, wiring only): the ℓ=0 twoBlock radial (§4, `d_v=M₀`
leading-slice — needs the SVD intrinsic bound `‖YW‖²≥(‖W‖²/min(u,d))‖Ye₁‖²`, the one spectral piece);
the (ℓ,s)-index completeness; the binding-cut scope threading (`hbind`/`hpiv` from `bindingCut`).

---

## (d) ★ BEDROCK GATE audit — `deepGate_branch` is a GENUINE ∀-PROOF (not a bounded decide)

`RouteMSJDeepGate.lean`: **0 sorry, 0 `decide`/`native_decide`, 0 `admit`** (verified via git-show grep).

- `deepGate_branch (M0 M1 u s κ mM) (hu : u ≤ min M0 M1) (hI : mM ≤ κ + minAdm ![M0,M1,s]) : mM + chargeExp (M0-u)(M1-u) s ≤ (M0-u)(M1-u) + u·s + κ` — proof: `have hII := minAdm3_add_chargeExp_le M0 M1 u s hu; omega`. **Genuine ∀-proof** over general `ℕ` variables (omega + one lemma), NO enumeration.
- Its supporting lemma `minAdm3_add_chargeExp_le` (the `chargeExp ≤ (ab+us) − minAdm₃` bound) is proved by `Finset.sup'_le` + a per-element `hper` closed by `omega`/`nlinarith [mul_nonneg …]` + `induction`/`by_cases` — again a genuine ∀-proof, NOT a `decide` sweep over widths.
- **Its load-bearing INPUT `hI`** = crstrat's `minAdm_le_compositeRank_add (M : Fin (L+1+1+1+1)→ℕ) (s) : minAdm M ≤ CRrec (deepTail M) s + minAdm ![M 0,M 1,s]` is **ALSO a genuine ∀-proof, sorry-free** (arity≥4, via the `CRrec` recursion + `gCrux`/perm-invariance). So the deep-stratum gate's BASE is genuine bedrock end-to-end (`deepGate_branch ∘ minAdm_le_compositeRank_add`), no bounded `decide`/enumeration anywhere on the gate path.

**VERDICT: the gate is sound bedrock (∀-proof).** The only residual risk is not the gate but the UNBUILT
assembly (G1/G2) that consumes it.

---

## (e) Dependency-ordered build plan (on the merged base)

0. **[merge]** cherry-pick DeepGate + CompositeRank + ShellSubset onto arch1build; wire imports; full-aggregator green-gate + `#print axioms` clean-three. (this task's output enables it)
1. **ℓ=0 twoBlock radial** (§4) — the one spectral piece (SVD intrinsic bound + `twoBlock_radial_le` + outer W-radial). Self-contained, pairs with `single_block_stratum_lt_top`. [the hardest sub-brick]
2. **deep-stratum per-cell radial** — instantiate `deepGate_branch` (hI := `minAdm_le_compositeRank_add`) to get `C_k ≥ 2T1_q`, feed `corner_block_cube_lintegral_lt_top` (same engine as `single_block`) ⟹ per-deep-cell finiteness = `hfin` for `deepRankLE_lintegral_lt_top`.
3. **G1 per-shell joint finiteness** — assemble: `shellSpine_le_frontCharge` (hGae/hEtopae discharged) + front gate + step 2 (deep) + steps 1 (ℓ=0) + `deepRankLE` glue ⟹ per-shell `< ⊤`.
4. **G2 ∀-arity box→shell→sum→(□)** — shell cover + G1 + finite-cover sum + arity-3 base (`routeMBoxThresholdFinite_mnp`) ⟹ `RouteMBoxThresholdFinite M` (arity≥4), by induction on arity.
5. **wire to mint** — `RouteMSJMint` consumes (□) directly; done.

**Gating:** steps 1–4 are the (3a) formaliser build, gated on `deephier`'s hierarchical-case verdict (the
recursion's arity-induction structure) per the controller. This map + the clean merge unblock an immediate
start once deephier lands.

---

## Summary (≤180-char cards)

- INVENTORY: all 12 named components sorry-free + located; deep-atlas sorry-free (docstring false-positive); only the two ASSEMBLY theorems (G1,G2) unbuilt.
- MERGE: base arch1build + cherry-pick DeepGate(stepbuild)+CompositeRank(crstrat)+ShellSubset(rescopefin); deps all present; no name clashes; CR-infra byte-identical; full-aggregator gate at end.
- GAPS: G1 per-shell joint finiteness (front×deep gate + atlas + radial + shellSpine); G2 ∀-arity box→shell→sum→(□). Plus ℓ=0 twoBlock radial (1 spectral sub-brick).
- BEDROCK: deepGate_branch = genuine ∀-proof (omega/nlinarith, NO bounded decide); input hI (minAdm_le_compositeRank_add) also genuine ∀-proof sorry-free. Gate base = sound bedrock.
- BUILD: merge → ℓ=0 radial → deep per-cell radial → G1 → G2 → mint. Gated on deephier.

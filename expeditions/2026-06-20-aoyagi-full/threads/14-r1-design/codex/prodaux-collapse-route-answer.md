   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading additional input from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/deriv-spec
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019ef5ae-a927-71f0-8505-0333e9e40c20
--------
user
Lean4/Mathlib v4.29. Follow-up on a chain-product strict-derivative collapse. I have PROVEN (green) all of:
- alignment cancel: at gauge-zero slice, readX(r0,0) s = 0 unless s=firstLayer (then = r0 at X-pivot coord); readZ similarly s=firstLayer; readY s=lastLayer. So the framed layer C_s(r0) = reindex(fromBlocks (1+X_s) Y_s Z_s 0) is CONSTANT (= corner = reindex(fromBlocks 1 0 0 0)) for every INTERIOR layer s ∉ {firstLayer,lastLayer}; only C_first and C_last vary with r0.
- prodAux_framedParamsReg_zero_aux: at r0=0, prodAux k = corner (reindexed) for 1≤k≤L.
- corner_reindex_mul: corner*corner=corner.
- A banked EXISTENCE strict-deriv per entry (opaque D).

TARGET: HasStrictFDerivAt (fun r0 => (P.toBlocks11 - 1) a b) (proj idx_X) 0 where P = reindex(prod(framedParamsReg(r0,0))), idx_X = regPivotFinEquiv.symm (inl(a,b)); plus the toBlocks12→Y_last and toBlocks21→Z_first analogues.

I'm choosing between:
(I) Define explicit `prodAuxEntryDeriv` (recursive Leibniz value) mirroring the existence proof, prove its strict-deriv, THEN prove by induction `prodAuxEntryDeriv (framedParamsReg·) 0 = the corner-sandwich Σ_s prefix·δC_s·suffix`, then read blocks. Concern: the corner-collapse induction is itself heavy + dependent-Fin casts.
(II) EXPLOIT interiors-constant: rewrite prod = (prefix corners)·C_first·(mid corners)·C_last·(suffix corners) so only ≤2 factors vary, differentiate THAT. Concern: the rewrite of prodAux into this factored form has its own cast pain, and firstLayer/lastLayer positions (0 and L-1) interact with the prodAux fold direction.
(III) Per-ENTRY directly: the coordinate function r0 ↦ (P11-1) a b. Since interiors constant and the corner kills cross terms, claim this entry function equals EXACTLY a single affine coordinate r0 ↦ r0 idx_X (NO higher-order terms, because the surviving sandwich corner·δ·corner is degree-1 and the higher-order product terms vanish on the corner blocks). If TRUE, the entry function is literally LINEAR (= r0 idx_X + const), and HasStrictFDerivAt is trivial via HasStrictFDerivAt of a coordinate projection + congr. IS the entry EXACTLY affine in r0 (not just to first order)? Consider L=2: P = C_0(r0)·C_1(r0), both vary (first=0,last=1). (P11) = (1+X_0)(1+X_1)_block... = block11 of product. X_0 routes the X-pivot, Y_1 the Y-pivot, etc. Is (C_0·C_1).toBlocks11 - 1 EXACTLY linear in r0? Compute: C_0=[[1+X0,Y0],[Z0,0]] but Y0=0 (Y only at last=1), Z0=routed. C_1=[[1+X1,Y1],[Z1,0]] but X1: X routes to first=0 only, so X1=0; Z1: Z to first only, so Z1=0; Y1=routed. So C_0=[[1+X0,0],[Z0,0]], C_1=[[1,Y1],[0,0]]. Product block11 = (1+X0)*1 + 0*0 = 1+X0. So P11-1 = X0 = r0 at X-pivot. EXACTLY linear! block12 = (1+X0)Y1 = Y1 + X0Y1 — NOT linear (X0Y1 cross term)! 

So (III) FAILS for block12 (the cross term X0·Y1 is degree 2). So I DO need the derivative (first-order), where X0Y1 contributes 0 at r0=0. Given block12 = Y1 + X0·Y1, its strict deriv at 0 is δY1 (the X0·Y1 term is o(r0)). 

So the real task per block: entry = (linear in r0) + (genuinely higher order vanishing at 0). The linear part is the surviving corner-sandwich. QUESTION: given this explicit small structure (each entry = explicit polynomial: block11=X0(+products that vanish), block12=Y_last+cross, block21=Z_first+cross), what's the LEANEST Lean route? Is there a way to write each entry function as `coordinate + remainder` and use HasStrictFDerivAt.add where remainder has deriv 0 (via it being a product of two functions each 0 at 0, hasStrictFDerivAt of f*g at 0 with f0=0,g0=0 gives deriv 0)? Specifically for general L: the product of L corner-or-varying factors — the entry is multilinear-ish. Recommend the cleanest GENERAL-L route and give the key lemma statements + Mathlib v4.29 deriv API (HasStrictFDerivAt.mul, .add, mul_zero deriv tricks). Keep dependent-Fin casts minimal.
codex
I’ll inspect the local Lean code and pinned Mathlib API so the recommendation lines up with the actual definitions and v4.29 names, rather than guessing from memory.
exec
/bin/bash -lc "rg --files -g 'CLAUDE.md' -g 'lake-manifest.json' -g 'lakefile.lean' -g '*.lean'" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc ls in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc 'rg -n "prodAux|framedParamsReg|readX|readY|readZ|corner_reindex_mul|prodAuxEntryDeriv|HasStrictFDerivAt" -S .' in /home/ubuntu/workspace/deriv-spec
 succeeded in 107ms:
AGENTS.md
CLAUDE.md
README.md
ROADMAP.md
TEMPLATE.md
docs
expeditions
lean
paper-sources
theory
threads

 succeeded in 122ms:
lean/DLNFibre.lean
lean/lake-manifest.json
lean/DLNFibre/Core/BaseChange.lean
lean/DLNFibre/Core/CThetaDropM.lean
lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean
lean/DLNFibre/Core/IntervalModule.lean
lean/DLNFibre/Core/PolynomialDimension.lean
lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean
lean/DLNFibre/Core/OrbitKostant.lean
lean/DLNFibre/Core/OrbitClosure.lean
lean/DLNFibre/Core/VoigtDischarge.lean
lean/DLNFibre/Core/MeasureTheory/PolynomialZeroSet.lean
lean/DLNFibre/Core/Setup.lean
lean/DLNFibre/Core/OrbitDifferential.lean
lean/DLNFibre/Core/NoetherMonicPositioning.lean
lean/DLNFibre/Core/OrbitTangentCotangent.lean
lean/DLNFibre/Core/OrbitSmooth.lean
lean/DLNFibre/Core/OrbitDifferentialRank.lean
lean/DLNFibre/Core/CThetaGeometric.lean
lean/DLNFibre/Core/DeformationExt.lean
lean/DLNFibre/Core/AffineNoetherRank.lean
lean/DLNFibre/Core/OrbitLinearCodim.lean
lean/DLNFibre/Core/CThetaExplicit.lean
lean/DLNFibre/Core/Submult.lean
lean/DLNFibre/Core/JacobianTrdeg.lean
lean/DLNFibre/Core/BoxMoveDegeneration.lean
lean/DLNFibre/Core/Basic.lean
lean/DLNFibre/Core/BoxMoveGeneration.lean
lean/DLNFibre/Core/CThetaValue.lean
lean/DLNFibre/Core/PolynomialCurveLimit.lean
lean/DLNFibre/Core/CThetaThetaBridge.lean
lean/DLNFibre/Core/SmoothPointRegular.lean
lean/DLNFibre/Core/OrbitImageDim.lean
lean/DLNFibre/Core/BoxMoveGeneral.lean
lean/DLNFibre/Core/Barcode.lean
lean/DLNFibre/Core/CThetaQIP.lean
lean/DLNFibre/Core/MatrixKaehler.lean
lean/DLNFibre/Core/IntegralDimension.lean
lean/DLNFibre/Core/Gabriel.lean
lean/DLNFibre/Core/OrbitVariety.lean
lean/DLNFibre/Core/NullstellensatzCodim.lean
lean/DLNFibre/Core/RankLocusClosed.lean
lean/DLNFibre/Core/CTheta.lean
lean/DLNFibre/Core/AffineDomainDimension.lean
lean/DLNFibre/Core/CThetaQIPConverse.lean
lean/DLNFibre/Core/OrbitCodim.lean
lean/DLNFibre/Core/Matrix/RankNormalForm.lean
lean/DLNFibre/Core/RankPattern.lean
lean/DLNFibre/Core/CotangentJacobian.lean
lean/DLNFibre/Core/OrbitPullbackDim.lean
lean/DLNFibre/Core/Orbit.lean
lean/DLNFibre/DLN/Basic.lean
lean/DLNFibre/DLN/RLCT/BGEngine.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Spectator.lean
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1G5.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1SmoothBlock.lean
lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean
lean/DLNFibre/DLN/RLCT/Foundations/Lambda.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean
lean/DLNFibre/DLN/RLCT/Foundations/DeepestSplitHaar.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Transport.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1G5Charts.lean
lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean
lean/DLNFibre/DLN/RLCT/Foundations/CoreShearMP.lean
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean
lean/DLNFibre/DLN/RLCT/Validate/ScratchAlign.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Block.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Value.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean
lean/DLNFibre/DLN/RLCT/Validate/Case111Bridge.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean
lean/DLNFibre/DLN/RLCT/AxCheck.lean
lean/DLNFibre/DLN/RLCT/Skeleton.lean
lean/CLAUDE.md
CLAUDE.md
expeditions/2026-06-18-voigt-discharge/threads/33-A1-kahler-trdeg-api/probes/KahlerTrdegProbe.lean
expeditions/2026-06-18-voigt-discharge/threads/33-A1-kahler-trdeg-api/probes/RingKrullTrdegProbe.lean

 succeeded in 186ms:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:11:      HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL (r0, 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:16:`hasStrictFDerivAt_prod_entry` returns `∃ D, HasStrictFDerivAt (prod entry) D x` — D is an OPAQUE
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:23:    -- goal: HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:31:Output coord = `(P.toBlocks₁₁ − 1) a b` where `P = reindex (prod (framedParamsReg (r0,0)))`. By the #91
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:35:`(framedParamsReg (r0,0)) reads readX_first (r0) a b = regGaugeSlotEquiv (r0,0) ⟨0, inl(inl(a,b))⟩`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:46:    -- d(prod (framedParamsReg (r0,0)))|_0 = Σ_s (corner prefix) · δC_s · (corner suffix), and the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:49:      HasFDerivAt (fun r0 => (reindex (prod (framedParamsReg (r0,0)))) i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:54:1. `prod_framedParamsReg_zero` (banked): at r0=0, `prod (framedParamsReg 0) = reindex (fromBlocks 1 0 0 0)`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:56:2. The product derivative at 0 (Leibniz, cobuild's `hasStrictFDerivAt_prodAux_entry` VALUE, or a direct
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:57:   `prodAux` induction): `dP|_0 = Σ_s prodAux_prefix(0) · δC_s · prodAux_suffix(0)`. The prefix/suffix
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:58:   AT r0=0 are the idempotent corner (by `prodAux_framedParamsReg_zero_aux` — the partial products at 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:62:   only for the FIRST. The `fromBlocks_multiply` / `corner_reindex_mul` kernels (banked in
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:64:4. `δC_s = framedLayer` derivative = `fromBlocks (δreadX) (δreadY) (δreadZ) 0` (T=0), and readX/Y/Z are
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:65:   LINEAR in r0 (regGaugeSlotEquiv is a CLE — `regGaugeSlotCLE`), so `δreadX_s = readX_s` etc. (a linear
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:66:   map's derivative is itself). So `Σ_s δX_s = Σ_s readX_s(r0)`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:84:- `prod_framedParamsReg_zero`, `prodAux_framedParamsReg_zero_aux`, `corner_reindex_mul`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:86:- `regGaugeSlotCLE` (DeepestFramedProduct) — readX/Y/Z linearity (δread = read).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:87:- `hasStrictFDerivAt_prodAux_entry` (cobuild @2bf7065) — IF a Leibniz value is wanted; else direct induction.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:96:- The Σ_s collapse to δX_first needs `readX_s (r0,0) = 0` for s ≠ 0 (interior X in the GAUGE slot, held
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:98:  entries are in the gauge half (the complement), and gauge = 0. STATE this as `readX_interior_zero`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:99:- If the per-coordinate derivative-of-(P11−1) doesn't directly give `Σ_s readX_s`, fall back to the
./lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean:33:def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
./lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean:39:      refine (prodAux H A k hk') * ?_
./lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean:50:  prodAux H A L (Nat.lt_succ_self L)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean:63:step-fact of the deepest-product idempotent fold (the `_base` value-fold's `prodAux` induction — the
./lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:76:  -- `simp` reduces the layer product `prodAux` (clearing its recursive casts) to `1 * A 0 * A 1`;
./lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:79:  simp [prodAux]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:16:gauge-sliced tuple `C : Params H` — no new fold; `prod`/`prodAux` are reused.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:38:function (defeq), giving `ContDiff` of `regGaugeSlotEquiv` (hence of the `readX/Y/Z` entries) via
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:62:/-- Each `readX` entry is `ContDiff ⊤` (a coordinate of the `ContDiff` gauge read). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:63:theorem contDiff_readX_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:65:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readX H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:66:  simp only [readX, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:69:/-- Each `readY` entry is `ContDiff ⊤`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:70:theorem contDiff_readY_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:73:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readY H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:74:  simp only [readY, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:77:/-- Each `readZ` entry is `ContDiff ⊤`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:78:theorem contDiff_readZ_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:81:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readZ H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:82:  simp only [readZ, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:102:`readX/readY/readZ`) and the reduced core `T_s` (read off the core slot via `paramsEquivFlat (deepestM)`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:111:      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:112:      (readZ H r hr hL (q.1, q.2.2) s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:120:`Fin nReg` pack convention (the open obstruction), only on the gauge read `readX/Y/Z`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:121:noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:126:      (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:129:/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:132:theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:134:    framedParamsReg H r hr hL 0 s
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:138:  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:139:    readZ_zero H r hr hL s, add_zero]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:141:/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:142:`fromBlocks (1+X) Y Z 0` block entry (reindexed), i.e. `1+readX` / `readY` / `readZ` / `0`, each
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:144:theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:147:    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:149:  have hentry : (fun p => framedParamsReg H r hr hL p s i j)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:150:      = fun p => Matrix.fromBlocks (1 + readX H r hr hL p s) (readY H r hr hL p s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:151:          (readZ H r hr hL p s) (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:155:    simp only [framedParamsReg, framedLayer, Matrix.reindex_apply, Matrix.submatrix_apply,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:162:  · -- (1 + X) entry: `(if a = b then 1 else 0) + readX … a b` — the `if` is a constant in `p`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:163:    exact contDiff_const.add (contDiff_readX_entry H r hr hL s a b)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:164:  · exact contDiff_readY_entry H r hr hL s a b
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:165:  · exact contDiff_readZ_entry H r hr hL s a b
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:184:typechecks). The PROOF is the cast-heavy `prodAux` induction: invariant `prodAux H C k = P0 *
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:185:prodAux H A k * (frame at k)`, interior interfaces cancelling by the `Q s * P s' = 1` conditions. The
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:191:`deepestEPivot` is `pack ∘ residual ∘ reindex ∘ prod ∘ framedParamsReg`; its `ContDiff ⊤` reduces to
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:192:`ContDiff ⊤ (fun x => prod H (g x))` for `g = framedParamsReg` (each layer affine in the slots, so
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:193:`ContDiff`). The product is the dependent-Fin `prodAux` fold — `ContDiff` ENTRY-WISE (matrix = nested
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:194:`Pi`; `contDiff_pi'` twice), mirroring the green `continuous_prodAux`: base `prodAux 0 = 1` const, step
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:195:`(prodAux k * layer) i j = ∑ m, prodAux k i m · layer m j` (`ContDiff.sum` of `ContDiff.mul`). No
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:201:plain ℝ-valued). Induction on `k`, mirroring `continuous_prodAux`: the matrix-mul step is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:202:`(prodAux k * layer) i j = ∑ m, prodAux k i m · layer m j` (`ContDiff.sum` of `ContDiff.mul`). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:203:theorem contDiff_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:209:      ContDiff ℝ (⊤ : ℕ∞) (fun x => prodAux H (g x) k hk i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:214:      -- `prodAux 0 = 1`; each entry is `0` or `1`, constant.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:215:      have : (fun x => prodAux H (g x) 0 hk i j)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:226:      -- `prodAux (k+1) i j = ∑ m, prodAux k i m · (cast layer k) m j`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:227:      have hentry : (fun x => prodAux H (g x) (k + 1) hk i j)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:228:          = fun x => ∑ m, prodAux H (g x) k hk' i m
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:241:/-- **`ContDiff` of the full layer-product entries** (`contDiff_prodAux_entry` at `k = L`). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:248:  contDiff_prodAux_entry H g hg L (Nat.lt_succ_self L) i j
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:250:/-- **`HasStrictFDerivAt` of the partial-product ENTRIES** (the `_deriv` infrastructure, entry-wise to
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:251:dodge the matrix-norm instance, mirroring `contDiff_prodAux_entry`). If each layer ENTRY has a strict
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:252:derivative `g' s i j` at `x`, then each `prodAux` entry has the LEIBNIZ strict derivative
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:253:`∑ m, (prodAux k i m) · (layer deriv) + (prodAux k deriv) · (layer i m)` — built by `HasStrictFDerivAt.sum`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:254:of `HasStrictFDerivAt.mul`. The derivative VALUE is the sum-of-products `prodAux'`; the deepest-point
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:256:theorem hasStrictFDerivAt_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:260:      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:263:      ∃ D : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j) D x := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:268:      -- `prodAux 0 = 1`; each entry is constant, derivative `0`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:270:      have : (fun y => prodAux H (g y) 0 hk i j)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:281:      -- `prodAux (k+1) i j = ∑ m, prodAux k i m · (cast layer k) m j`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:282:      have hentry : (fun y => prodAux H (g y) (k + 1) hk i j)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:283:          = fun y => ∑ m, prodAux H (g y) k hk' i m
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:288:      -- Each summand `prodAux k i m * (cast layer) m j` has a strict derivative (product rule).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:289:      -- `HasStrictFDerivAt.sum` over `m`; each summand via `HasStrictFDerivAt.mul` of (ih) and (the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:292:          HasStrictFDerivAt (fun y => prodAux H (g y) k hk' i m
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:297:        have hlayer : HasStrictFDerivAt
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:306:      exact ⟨∑ m, D m, HasStrictFDerivAt.fun_sum (fun m _ => hD m)⟩
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:308:/-- **`HasStrictFDerivAt` of the full layer-product entries** (`hasStrictFDerivAt_prodAux_entry` at
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:315:      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:317:    ∃ D : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => prod H (g y) i j) D x :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:318:  hasStrictFDerivAt_prodAux_entry H g x g' hg L (Nat.lt_succ_self L) i j
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:171:by the concrete `regStraighten`'s implicit-function-theorem data (`HasStrictFDerivAt.toOpenPartialHomeomorph`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:210:(`HasStrictFDerivAt.toOpenPartialHomeomorph`) packages the local inverse; the bounded-unit Jacobian
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:217:(`ContDiff ℝ ⊤` is a CONVENIENCE above the germ minimum — `ContDiffAt`/`HasStrictFDerivAt` at `wstar`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:225:    (hf : HasStrictFDerivAt f (e : M →L[ℝ] M) wstar)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:325:with `HasStrictFDerivAt E_pivot (fst) 0` — the "`dE(0) = id`" of the ruling, typed precisely: the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:370:Given `HasStrictFDerivAt E_pivot (fst : R × S →L R) 0` (the precise `dE(0) = id`), the total map's
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:371:strict derivative at `0` is `ContinuousLinearMap.id`. Assembled by `HasStrictFDerivAt.prodMk` of the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:375:    (hE : HasStrictFDerivAt E_pivot (ContinuousLinearMap.fst ℝ R S) 0) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:376:    HasStrictFDerivAt (regStraightenOf (C := C) E_pivot)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:382:  have hproj_sd : HasStrictFDerivAt (fun q : R × (C × S) => (q.1, q.2.2)) proj 0 :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:385:  have hreg_sd : HasStrictFDerivAt (fun q : R × (C × S) => E_pivot (q.1, q.2.2))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:390:  have hcore_sd : HasStrictFDerivAt (fun q : R × (C × S) => q.2.1)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:393:  have hspec_sd : HasStrictFDerivAt (fun q : R × (C × S) => q.2.2)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:396:  have hcs_sd : HasStrictFDerivAt (fun q : R × (C × S) => (q.2.1, q.2.2))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:415:    (hE : HasStrictFDerivAt E_pivot (ContinuousLinearMap.fst ℝ R S) 0) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:416:    HasStrictFDerivAt (regStraightenOf (C := C) E_pivot)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:437:`HasStrictFDerivAt E_pivot D_E 0` for any `D_E`, the total map's strict derivative at `0` is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:441:    (hE : HasStrictFDerivAt E_pivot D_E 0) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:442:    HasStrictFDerivAt (regStraightenOf (C := C) E_pivot) (regStraightenTotalCLM (C := C) D_E) 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:446:  have hproj_sd : HasStrictFDerivAt (fun q : R × (C × S) => (q.1, q.2.2)) proj 0 :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:448:  have hreg_sd : HasStrictFDerivAt (fun q : R × (C × S) => E_pivot (q.1, q.2.2))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:452:  have hcore_sd : HasStrictFDerivAt (fun q : R × (C × S) => q.2.1)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean:455:  have hspec_sd : HasStrictFDerivAt (fun q : R × (C × S) => q.2.2)
./lean/DLNFibre/DLN/RLCT/Validate/ScratchAlign.lean:81:-- readX at firstLayer reads back r0 at the X-pivot coord.
./lean/DLNFibre/DLN/RLCT/Validate/ScratchAlign.lean:84:    readX H r hr hL (r0, 0) (firstLayer hL) a b
./lean/DLNFibre/DLN/RLCT/Validate/ScratchAlign.lean:86:  simp only [readX, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:7:The cast-heavy `prodAux` induction behind PIN2's frame bridge:
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:18:- (`prodAux_succ` SHAPE, typechecks) the `k+1` fold IS the running product times the layer transported
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:37:/-- **`prodAux` recursion, reindex-explicit** (statement TYPECHECKS; proof is the deferred entry-chase).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:40:theorem prodAux_succ (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:45:    prodAux H A (k + 1) hk
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:46:      = (prodAux H A k (Nat.lt_of_succ_lt hk)) *
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:53:block `Matrix.reindex eC.symm eS.symm M` at the running widths, then the `prodAux` succ-step is the clean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:54:product `prodAux k * reindex eC.symm eS.symm M` — the def's `Eq.mpr` cast is collapsed by the index-level
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:55:`cases e1; cases e2` idiom (the `contDiff_prodAux_entry` precedent). All three folds (value / deriv /
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:58:theorem prodAux_succ_layer (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:70:    prodAux H A (k + 1) hk
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:71:      = prodAux H A k (Nat.lt_of_succ_lt hk) * Matrix.reindex eC.symm eS.symm M := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:78:  show prodAux H A k hk' *
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:81:  refine congrArg (prodAux H A k hk' * ·) ?_
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:89:theorem corner_reindex_mul {a b c r : ℕ}
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:130:/-- **The idempotent fold at `0`** (`prodAux` form, `1 ≤ k`). At the deepest gauge slot, every layer is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:131:the block-normal corner `reindex (fromBlocks 1 0 0 0)` (`framedParamsReg_zero`), and the corner is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:133:(at width `H 0 × H ⟨k⟩`). Proven by `prodAux_succ` + `framedParamsReg_zero` + `fromBlocks_multiply`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:135:theorem prodAux_framedParamsReg_zero_aux (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:138:      prodAux H (framedParamsReg H r hr hL 0) k hk
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:149:      -- INDEX-level equalities (the `prodAux` def's own, `Fin.ext`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:154:      -- `prodAux (k+1)` unfolds (def at Loss.lean) to `prodAux k * (Eq.mpr-cast layer)`, and that layer
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:155:      -- IS the corner at the running widths (`framedParamsReg_zero` then `cases e1; cases e2` collapses the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:157:      -- the Eq.mpr-cast layer = the corner at the running widths (PROBE-proven: `framedParamsReg_zero`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:159:      have hlayer : ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:164:        rw [framedParamsReg_zero H r hr hL ⟨k, hkL⟩]; cases e1; cases e2; rfl
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:165:      have hstep : prodAux H (framedParamsReg H r hr hL 0) (k + 1) hk
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:166:          = prodAux H (framedParamsReg H r hr hL 0) k hk' *
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:170:        show prodAux H (framedParamsReg H r hr hL 0) k hk' *
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:171:            ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:173:        exact congrArg (prodAux H (framedParamsReg H r hr hL 0) k hk' * ·) hlayer
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:177:        -- accumulator is `prodAux 0 = 1`; `1 * corner = corner` (`prodAux 0` reduces, then `one_mul`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:180:        exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:185:gauge-sliced product at the deepest gauge slot is the block-normal corner: `prod (framedParamsReg 0) =
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:186:reindex (fromBlocks 1 0 0 0)` (at width `H 0 × H (last)`). `prod = prodAux L`; specialize the `aux`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:188:theorem prodAux_framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:190:    prod H (framedParamsReg H r hr hL 0)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:194:  have h := prodAux_framedParamsReg_zero_aux H r hr hL L (Nat.lt_succ_self L) hL
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:238:  -- HMul `P0 * prodAux A k` typechecks at `Fin (H 0)`, NO per-step boundary cast).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:243:  -- INVARIANT `prodAux C k = (h0cs ▸ P ⟨0⟩) * prodAux A k` (1 ≤ k ≤ Lm), P ⟨0⟩ cast to `Fin (H 0)`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:245:      prodAux H C k hk = (h0cs ▸ P ⟨0, by omega⟩) * prodAux H A k hk := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:255:        rw [prodAux_succ H C k hsucc e1 e2, prodAux_succ H A k hsucc e1 e2]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:259:          -- k+1 = 1: `prodAux _ 0 = 1` (def); the layer is `reindex (C ⟨0⟩)` vs `reindex (A ⟨0⟩)`, and
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:264:          simp only [show prodAux H C 0 (Nat.lt_of_succ_lt hsucc)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:266:            show prodAux H A 0 (Nat.lt_of_succ_lt hsucc)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:289:  -- FINAL: `prod C = prodAux C (Lm+1) = prodAux C Lm * (cast C_Lm)`; `C_Lm = A_Lm·Q_Lm` (P_Lm = 1, hPid);
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:290:  -- hinv ⟹ `= (cast P⟨0⟩)·prodAux A Lm·(cast A_Lm·Q_Lm) = P0 · prod A · QL`. ∃-intro the cast P⟨0⟩, Q⟨Lm⟩.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:292:  -- `prod C = prodAux C (Lm+1)`; `prodAux_succ` (k=Lm) unfolds the last layer.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:303:  rw [prodAux_succ H C Lm hLm1 e1L e2L, prodAux_succ H A Lm hLm1 e1L e2L]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:305:  · -- `Lm = 0` (L = 1): single layer is BOTH endpoints. `prodAux _ 0 = 1`; `C 0 = P0 · A 0 · Q0`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:310:  · -- `Lm ≥ 1`: `hinv Lm` gives `prodAux C Lm = P0 · prodAux A Lm`; `C Lm = A Lm · Q Lm` (`P Lm = 1`);
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:323:    -- REMAINING (handed to crux2): the LAST step, pure 4-matrix associativity `P0·prodAux·(rA·QL) =
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:324:    -- P0·(prodAux·rA)·QL` (both `P0·prodAux·rA·QL`). The dependent-dim `Matrix.mul_assoc` resists EVERY
./lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:680:  simp only [prodAux, eq_mpr_eq_cast]
./lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:47:index `⟨0,_⟩ : Fin 1`). `prodAux` for `L = 2` telescopes `(1·C⁽¹⁾)·C⁽²⁾`. Closer: `mul_apply` +
./lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:48:`eq_mpr_eq_cast` exposes the base factor's `prodAux` `Fin`-cast as an explicit `cast`; a `simp only`
./lean/DLNFibre/DLN/RLCT/Validate/Case212.lean:57:  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:195:`ContDiff ℝ ⊤` with `dE(0) = id` (typed as `HasStrictFDerivAt E_pivot (fst) 0`) — its concrete
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:208:    (hEp_deriv : HasStrictFDerivAt E_pivot D_E 0)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:251:  · -- `HasStrictFDerivAt (regStraightenOf E_pivot) (e) 0`: the assembled total CLM IS `e` (via `he`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:345:reading the reg + spectator slots, with `dE(0) = id` (typed `HasStrictFDerivAt deepestEPivot (fst) 0`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:349:`HasStrictFDerivAt (fst) 0`, `0 ↦ 0`) are the residual gauge-geometry obligation: the product-residual
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:365:`Fin nReg → ℝ` via `regResidualPack`. `P = ∏ (framedParamsReg p)` reindexed to `r ⊕ M` block shape;
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:372:      (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL p))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:381:  -- Each layer entry of `framedParamsReg` is `ContDiff` (`contDiff_framedParamsReg_entry`), so each
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:382:  -- entry of `prod H (framedParamsReg ·)` is `ContDiff` (`contDiff_prod_entry`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:384:      ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s a b) :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:385:    contDiff_framedParamsReg_entry H r hr hL
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:387:      ContDiff ℝ (⊤ : ℕ∞) (fun p => prod H (framedParamsReg H r hr hL p) a b) :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:388:    fun a b => contDiff_prod_entry H (framedParamsReg H r hr hL) hlayer a b
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:397:          (prod H (framedParamsReg H r hr hL p))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:423:    HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:434:  -- Per-coordinate: `HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0`. The #91
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:435:  -- idempotent-sandwich: `d(prod(framedParamsReg (r0,0)))|_0 = Σ_s corner·δC_s·corner` keeps the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:439:  -- atom is the patient analytic fill (the Leibniz sandwich VALUE through `prodAux` + the cancel).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:446:on `DeepestSplit`, det 1, invertible). Bundled: `∃ D_E (e : ≃L), HasStrictFDerivAt deepestEPivot D_E 0
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:455:      HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 ∧
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:461:  have hsd : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:465:  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => ((r0, 0) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:472:  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:474:    have hsd0 : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:490:  -- At the origin slot, `∏(framedParamsReg 0)` is the reindexed corner `fromBlocks 1 0 0 0`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:491:  -- (`prod_framedParamsReg_zero`); the outer `reindex` in `P` cancels it, so `P = fromBlocks 1 0 0 0`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:495:        (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL 0)))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:497:    rw [prodAux_framedParamsReg_zero H r hr hL, ← Matrix.reindex_symm,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:48:noncomputable def readX (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:55:noncomputable def readY (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:62:noncomputable def readZ (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:70:theorem continuous_readX (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:72:    Continuous (fun p => readX H r hr hL p s) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:74:  simp only [readX, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:77:theorem continuous_readY (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:79:    Continuous (fun p => readY H r hr hL p s) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:81:  simp only [readY, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:84:theorem continuous_readZ (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:86:    Continuous (fun p => readZ H r hr hL p s) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:88:  simp only [readZ, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:105:theorem readX_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:107:    readX H r hr hL 0 s = 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:109:  simp only [readX, Matrix.of_apply, Matrix.zero_apply, regGaugeSlotEquiv_zero H r hr hL,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:112:theorem readY_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:114:    readY H r hr hL 0 s = 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:116:  simp only [readY, Matrix.of_apply, Matrix.zero_apply, regGaugeSlotEquiv_zero H r hr hL,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:119:theorem readZ_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:121:    readZ H r hr hL 0 s = 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:123:  simp only [readZ, Matrix.of_apply, Matrix.zero_apply, regGaugeSlotEquiv_zero H r hr hL,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:139:  fun s => -(readZ H r hr hL p s) * (1 + readX H r hr hL p s)⁻¹ * (readY H r hr hL p s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:166:/-- The matrix inverse `(1 + readX p s)⁻¹` is `ContinuousAt p` when `det(1 + readX p s) ≠ 0`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:167:theorem continuousAt_inv_one_add_readX (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:170:    (hdet : (1 + readX H r hr hL p s).det ≠ 0) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:171:    ContinuousAt (fun q => (1 + readX H r hr hL q s)⁻¹) p := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:172:  have hadd : ContinuousAt (fun q => (1 : Matrix (Fin r) (Fin r) ℝ) + readX H r hr hL q s) p :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:173:    (continuous_const.add (continuous_readX H r hr hL s)).continuousAt
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:180:/-- The per-layer Schur correction is `ContinuousAt p` when `det(1 + readX p s) ≠ 0`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:184:    (hdet : (1 + readX H r hr hL p s).det ≠ 0) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:188:    (continuousAt_matrix_mul ((continuous_readZ H r hr hL s).continuousAt.neg)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:189:      (continuousAt_inv_one_add_readX H r hr hL s p hdet))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:190:    (continuous_readY H r hr hL s).continuousAt
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:197:  simp only [schurCorrection, readZ_zero H r hr hL s, neg_zero, Matrix.zero_mul]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:221:  {p | ∀ s : Fin L, (1 + readX H r hr hL p s).det ≠ 0}
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:227:      = ⋂ s : Fin L, {p | (1 + readX H r hr hL p s).det ≠ 0} := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:231:  have hcont : Continuous (fun p => (1 + readX H r hr hL p s).det) :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:232:    (continuous_const.add (continuous_readX H r hr hL s)).matrix_det
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean:239:  rw [readX_zero H r hr hL s, add_zero, Matrix.det_one]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:20:  (the gauge half is held at `0`). Hence `readX/readY/readZ (r0,0) s` are nonzero ONLY at the routed
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:135:/-! ## The `readX/readY/readZ` slice values -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:137:/-- `readX (r0,0) (firstLayer) a b` reads back `r0` at the X-pivot coordinate. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:138:theorem readX_regSlice_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:140:    readX H r hr hL (r0, 0) (firstLayer hL) a b
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:142:  simp only [readX, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:147:/-- `readX (r0,0) s = 0` for `s ≠ firstLayer` (the X-routing hits only `firstLayer`). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:148:theorem readX_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:150:    readX H r hr hL (r0, 0) s = 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:152:  simp only [readX, Matrix.of_apply, Matrix.zero_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:156:/-- `readZ (r0,0) (firstLayer) a b` reads back `r0` at the Z-pivot coordinate. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:157:theorem readZ_regSlice_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:160:    readZ H r hr hL (r0, 0) (firstLayer hL) a b
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:162:  simp only [readZ, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:167:/-- `readZ (r0,0) s = 0` for `s ≠ firstLayer`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:168:theorem readZ_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:170:    readZ H r hr hL (r0, 0) s = 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:172:  simp only [readZ, Matrix.of_apply, Matrix.zero_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:176:/-- `readY (r0,0) s = 0` for `s ≠ lastLayer`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:177:theorem readY_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:179:    readY H r hr hL (r0, 0) s = 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:181:  simp only [readY, Matrix.of_apply, Matrix.zero_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:189:theorem framedParamsReg_regSlice_interior (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:192:    framedParamsReg H r hr hL (r0, 0) s
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:196:  simp only [framedParamsReg, framedLayer, readX_regSlice_zero_of_ne H r hr hL r0 s hsf,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:197:    readY_regSlice_zero_of_ne H r hr hL r0 s hsl, readZ_regSlice_zero_of_ne H r hr hL r0 s hsf,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:58:(both `0 ↦ 0`). Used to evaluate `prodAux`'s cast-transported layer at `(0,0)`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:67:theorem prodAux_e00Witness_zero (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 1 ≤ M s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:69:    prodAux M (e00Witness M) k hk ⟨0, hpos 0⟩ ⟨0, hpos ⟨k, hk⟩⟩ = 1 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:71:  | zero => simp [prodAux, Matrix.one_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:79:      -- the cast-transported layer `Lyr` is the `e₀₀` matrix at the `prodAux`-needed type. Its entries:
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:90:      -- `prodAux (k+1) = prodAux k * Lyr`; evaluate at `(0,0)` via `mul_apply` + the single 0-term.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:91:      show (prodAux M (e00Witness M) k hk' * Lyr) ⟨0, hpos 0⟩ ⟨0, hpos ⟨k + 1, hk⟩⟩ = 1
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:105:    have := prodAux_e00Witness_zero M hpos L (Nat.lt_succ_self L)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:106:    -- `prod = prodAux L`, and `⟨0, hpos ⟨L, _⟩⟩ = ⟨0, hpos (Fin.last L)⟩` (same `Fin.last`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:128:as `eval z P` for one `P`. `prod`/`prodAux` are ℝ-specific, so we mirror `prodAux` over a generic
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:134:/-- The generic-`CommRing` mirror of `prodAux` (same recursion + cast structure). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:149:/-- `prodPolyAux` maps to `prodAux` under any ring hom applied per layer: if `(A s).map f = B s` for
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:150:every layer, then `(prodPolyAux M A k).map f = prodAux M B k`. The eval-commutes engine. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:184:/-- `prodPolyAux` over ℝ IS `prodAux` (same recursion + cast structure) — the bridge from the generic
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:185:mirror back to the loss's `prodAux`. By induction (both: base `1`, step `prev * cast layer`). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:186:theorem prodPolyAux_eq_prodAux (M : Fin (L + 1) → ℕ) (A : Params M) (k : ℕ) (hk : k < L + 1) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:187:    prodPolyAux M A k hk = prodAux M A k hk := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:193:      conv_rhs => rw [prodAux]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:219:`prodAux M (flatSymm z) = prod M (flatSymm z)`, and `dlnLoss = ∑ entries²`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:230:    -- `prodPolyAux M (flatSymm z) L = prodAux M (flatSymm z) L = prod M (flatSymm z)`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean:231:    rw [prodPolyAux_eq_prodAux M ((paramsEquivFlat M).symm z) L (Nat.lt_succ_self L)] at h1
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:121:base `prodAux 0 = 1` constant; step `prodAux (k+1) = prodAux k * (layer k)`, the cast-transported
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:123:then `Continuous.matrix_mul`). Local helper — `fun_prop` deep-recurses on `prodAux`; lift to a shared
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:125:private theorem continuous_prodAux (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:126:    Continuous (fun A : Params H => prodAux H A k hk) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:131:      simpa [prodAux] using
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:150:      have hMul : Continuous (fun A : Params H => prodAux H A k hk' * layer A) :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:154:/-- The multiplication map is continuous (`continuous_prodAux` at `k = L`). Local helper. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:156:  continuous_prodAux H L (Nat.lt_succ_self L)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean:159:`prod H A − B`. The integrand measurability `fun_prop` cannot get (deep-recurses on `prodAux`).
./lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:14:inner dim collapsing by `Finset.sum_singleton`) is the **`Fin 2` inner sum** + the `prodAux`
./lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:15:dependent-`Fin`-cast: `prodAux`'s `rw [e1, e2]` produces `cast`s on the `Matrix` type between
./lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean:33:  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:590:private theorem prodAux_zero (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k + 1 < L + 1) :
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:591:    prodAux H (fun _ => 0) (k + 1) hk = 0 := by
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:592:  rw [prodAux]; convert Matrix.mul_zero _
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:598:  exact prodAux_zero H k (Nat.lt_succ_self _)
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:778:/-- The `prodAux` recursion-step, with the dependent-`Fin` cast discharged by HEq: if `A ⟨k,_⟩` is
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:779:HEq to `Mstep` (typed at the `prodAux` dims), then `prodAux (k+1) = prodAux k * Mstep`. -/
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:780:private theorem prodAux_step (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:783:    prodAux H A (k + 1) hk = prodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:784:  rw [prodAux]; congr 1; rw [eq_comm]; apply eq_of_heq
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:832:/-- The partial product up to (but excluding) the last layer: `prodAux m = U · [I_r|0]_{r→H⟨m⟩}`. -/
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:833:private theorem prodAux_closed (hrH : ∀ s : Fin (L + 1), r ≤ H s)
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:835:    prodAux H (wLayers H r U V) m hmlt = U * projM r (H ⟨m, hmlt⟩) := by
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:841:      rw [prodAux_step H (wLayers H r U V) 0 hmlt (U * projM r (H ⟨0 + 1, hmlt⟩))
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:847:      rw [prodAux_step H (wLayers H r U V) n hmlt
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:860:  rw [prodAux_step H (wLayers H r U V) n (Nat.lt_succ_self (n + 1))
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:863:  rw [prodAux_closed H r U V hrH n (by omega) (by omega)
./lean/DLNFibre/DLN/RLCT/Skeleton.lean:887:  rw [prodAux_step H (wSingle H B) 0 (Nat.lt_succ_self 1) B (by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/l2-architecture-card.md:172:   deep-recurses on `prodAux`; needs a hand `continuous_prodAux` (induction; the `prodAux` definitional
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/l2-architecture-card.md:179:Cert-gap #2 (`Measurable (dlnLoss M 0)`) is **CLOSED**: `continuous_prodAux`/`continuous_prod`/
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/l2-architecture-card.md:181:The `prodAux` `Fin.cast` that stalled 3 solo attempts — Codex (g151, xhigh) gave the idiom: define
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/l2-architecture-card.md:203:- Foundations bedrock: `rlctAtOn_spectator_peel`, `continuous_prodAux/_prod/_dlnLoss`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:7:      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0, 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:98:      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0,0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:103:`d(P)|₀ = Σ_s corner·δC_s·corner`; (b) the idempotent-sandwich collapse (`prodAux_framedParamsReg_zero` +
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:132:  is which X/Y/Z) → ripples to `readX/Y/Z` VALUES → `framedParamsReg`/`deepestEPivot` VALUES.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:8:The #123 dependent-Fin `prodAux` cast wall (the named single L2 gate in the handback) is BROKEN.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:12:`prodAux_succ_layer` kernel (`cases e1; cases e2`). FOLD1 (value) DONE both:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:13:- `prodAux_framedParamsReg_zero_aux` + `prodAux_framedParamsReg_zero` (crux2's file, axiom-clean).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:20:  named sorry. BANKED clean-three: `hasStrictFDerivAt_prodAux_entry`/`_prod_entry` (the L-fold product
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:26:  HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0)) id 0` — the #91 idempotent-sandwich (gauge-zero
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:53:    detbound card's "next layer"): `ContDiff ⊤ f` + `HasStrictFDerivAt f (e:≃L) wstar` + `f wstar=wstar`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:95:- `deepestEPivot` CONCRETE def + `regResidualPack` @20ad514; `framedParamsReg` (T=0) + `_zero` @2f3508e;
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:96:  `contDiff_prodAux_entry`/`contDiff_prod_entry` @9aaead1; `regGaugeSlotCLE` + `contDiff_readX/Y/Z_entry`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:97:  + `contDiff_framedParamsReg_entry` @ecd8d6f.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:115:- **`_base`** (`deepestEPivot 0 = 0`): **DONE** (clean-three) via `prodAux_framedParamsReg_zero` (the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:118:- **`_deriv`** (the bundled shear): the concrete shear `D_E` + `HasStrictFDerivAt deepestEPivot D_E 0`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:140:- **crux2's #111 `prodAux_succ` cast** (`obtain rfl + rfl`, COMPLETED) → closes `_base` (the idempotent
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:141:  fold) AND PIN 2-B's boundary `prodAux` telescoping.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:1:# Statement card — #123 FOLD1: the idempotent `prodAux`-at-0 fold + `deepestEPivot_base`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:3:> **Claim.** At the origin gauge slot, the framed (T=0) layer product `∏(framedParamsReg 0)` is the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:5:> `deepestEPivot 0 = 0`. This is FOLD1 (value) of the #123 `prodAux` fold family — the cast-wall break
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:9:>   - `DLNFibre.DLN.RLCT.prodAux_framedParamsReg_zero_aux` and
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:10:>     `DLNFibre.DLN.RLCT.prodAux_framedParamsReg_zero` (crux2's single-writer
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:15:> - **Gloss.** Every layer of `framedParamsReg H r hr hL 0` is, at the origin, the block-normal corner
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:17:>   (`framedParamsReg_zero`). The corner is idempotent under the chain product, so the running product
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:18:>   through `k ≥ 1` layers is again the corner at width `H 0 × H ⟨k⟩` (`prodAux_framedParamsReg_zero_aux`),
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:19:>   and at `k = L` this is `∏ = reindex(corner)` (`prodAux_framedParamsReg_zero`). The pivot residual
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:24:> - **The cast break (the named #123 gate).** The `prodAux` succ-step carries a dependent-`Fin` cast:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:27:>   matrix-VALUE rewrite of `framedParamsReg_zero` under the fold. TWO independent cracks:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:28:>   - **cobuild:** after `rw [prodAux_succ … e1 e2]` the layer is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:32:>     (the `prodAux 0 = 1` head), `k ≥ 1` → `rw [ih]` + `corner_reindex_mul` (the idempotent
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:34:>   - **crux2:** `prodAux_succ_layer` — the SHARED step-cast kernel; the index-level `cases e1; cases e2`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:35:>     collapses the def's `Eq.mpr`/cast (the `contDiff_prodAux_entry` precedent). The reusable family piece.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:38:>   `prodAux_framedParamsReg_zero_aux`, `prodAux_framedParamsReg_zero`, `deepestEPivot_base` — all
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:41:> - **Building blocks (crux2, axiom-clean):** `prodAux_succ` (explicit `e1/e2` + `Subsingleton.elim`),
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:42:>   `prodAux_succ_layer` (the kernel), `corner_reindex_mul` (`submatrix_mul_equiv` + `fromBlocks_multiply`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:45:>   - `deepestEPivot_deriv` (#82): the `HasStrictFDerivAt` Leibniz derivative + shear — analytic, OPEN.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:7:   Biggest risk: dependent `prodAux` casts plus named Leibniz derivative will spread through every entry.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:22:have hE : HasStrictFDerivAt E D_E 0 :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:29:- `HasStrictFDerivAt.comp`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:31:- `HasStrictFDerivAt.hasFDerivAt`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:45:  HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:50:Prove this coordinatewise by `hasStrictFDerivAt_pi''`. For each packed coordinate, unfold `deepestEPivot`, `framedParamsReg`, `framedLayer`, then use the gauge-zero slice facts for reads:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:53:readX H r hr hL (r0, 0) s = if s = first then X_from_reg r0 else 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:54:readY H r hr hL (r0, 0) s = if s = last  then Y_from_reg r0 else 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:55:readZ H r hr hL (r0, 0) s = if s = first then Z_from_reg r0 else 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:82:  HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:84:      -- packed residual of prod H (framedParamsReg (r0,0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:113:The wall is `deepestEPivot_regSlice_hasStrictFDerivAt_id`, specifically making `regResidualPack` and `regGaugeIdxSplit` expose that the regular coordinates are exactly `(X_first, Y_last, Z_first)`. Fallback: do A only for the reg-slice, not full `(reg,gauge)`: name a restricted Leibniz derivative for `fun r => prod H (framedParamsReg (r,0))`; collapse it to `id`; still keep `D_E := fderiv` for the full map.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-cast-prompt.md:3:explicit cast-free `∑`/polynomial form) but `prod`/`prodAux`'s dependent recursion introduces `cast`s
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-cast-prompt.md:11:def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-cast-prompt.md:17:      refine (prodAux H A k hk') * ?_
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-cast-prompt.md:23:  prodAux H A L (Nat.lt_succ_self L)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-cast-prompt.md:35:- `show prodAux H222 A 2 _ = A 0 * A 1; rfl` → fails (the e1/e2 `rw`-casts aren't rfl-collapsible; also
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-cast-prompt.md:37:- `rw [prodAux]; simp [Matrix.mul_apply, prodAux, eq_mpr_eq_cast, cast_eq, one_apply, Fin.sum_univ_two]`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-cast-prompt.md:55:   e.g. `prodAux_succ : prodAux H A (k+1) hk = prodAux H A k _ * (cast-free A-term)` stated to AVOID the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-answer.md:2:Rewrite the continuity goal for the transported layer with `e1` and `e2` before transporting the proof. In other words, prove `Continuous layer` by normalizing the whole goal with `simpa only [e1, e2, eq_mpr_eq_cast, cast_eq] using continuous_apply ...`; after that the casted layer is just the coordinate projection `fun A => A ⟨k, hkL⟩`. Then multiply by the induction hypothesis and use `Continuous.congr` with the definitional recursive equation for `prodAux`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-answer.md:5:theorem continuous_prodAux (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-answer.md:6:    Continuous (fun A : Params H => prodAux H A k hk) := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-answer.md:11:      simpa [prodAux] using
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-answer.md:41:          prodAux H A k hk' * layer A) :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g152-sub34-finding.md:327:Controller named `HasStrictFDerivAt.toPartialHomeomorph`; the ACTUAL v4.29 name is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g152-sub34-finding.md:330:- `HasStrictFDerivAt.toOpenPartialHomeomorph (hf : HasStrictFDerivAt f (f' : E →L F) a)` [f' an ≃L via
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g152-sub34-finding.md:336:- C¹ upgrade HasFDerivAt→HasStrictFDerivAt: `ContDiffAt.hasStrictFDerivAt (hf : ContDiffAt 𝕂 n f x) (hn : n ≠ 0)`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:7:    HasStrictFDerivAt deepestEPivot D_E 0 ∧ (e : DeepestSplit →L DeepestSplit) = regStraightenTotalCLM D_E
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:16:  where P = reindex eIn eOut (prod H (framedParamsReg p))  [reindex/eIn/eOut are FIXED Equivs,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:17:  constant in p]. So deepestEPivot is: pack ∘ (block-projections − const) ∘ reindex ∘ (prod ∘ framedParamsReg).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:18:  The ONLY p-dependence is in prod H (framedParamsReg p). reindex, toBlocks, −1, pack are all CONSTANT-LINEAR.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:19:- framedParamsReg p : each layer s = reindex (fromBlocks (1+X_s) Y_s Z_s 0), where (X_s,Y_s,Z_s) =
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:20:  readX/readY/readZ p s are LINEAR coordinate reads of p (they coerce from a ContinuousLinearEquiv
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:28:- hasStrictFDerivAt_prodAux_entry : ∀ entry, ∃ D, HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j) D x
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:30:  HasStrictFDerivAt.fun_sum of .mul, cast-layer normalised by simp [eq_mpr_eq_cast, cast_eq]).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:31:- prodAux_framedParamsReg_zero : prod H (framedParamsReg 0) = reindex (corner = fromBlocks 1 0 0 0)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:33:- fromBlocks_blockdiag_idem (corner·corner = corner), corner_reindex_mul.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:34:- deepestEPivot_contdiff : ContDiff ⊤ deepestEPivot (so HasStrictFDerivAt deepestEPivot (fderiv ℝ … 0) 0 is FREE).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:42:THE GAP: my hasStrictFDerivAt_prodAux_entry gives ∃ D (opaque). I need the EXPLICIT D_E (or at least
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:46:(A) Refactor prodAux_entry to NAME the derivative recursively (Leibniz sum value), then specialize at
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:52:    an explicitly-constructed N), prove HasStrictFDerivAt deepestEPivot (the reg-component of e) 0 by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:20:- `prodAux H A : (k:ℕ) → (hk : k < L+1) → Matrix (Fin (H 0)) (Fin (H ⟨k,hk⟩)) ℝ`, with
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:21:  `prodAux 0 = 1`, `prodAux (k+1) = prodAux k * (cast layer ⟨k,hkL⟩)` (dependent Fin casts e1/e2).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:22:- `prod H A := prodAux H A L (Nat.lt_succ_self L)`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:23:- `framedParamsReg H r hr hL p : Params H`, each layer = `reindex e.symm e'.symm (fromBlocks (1+X_s) Y_s Z_s 0)` where X_s=readX p s etc (linear in p, =0 at p=0).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:24:- At p=0 (gauge slot 0): `prodAux_framedParamsReg_zero_aux`: for 1≤k≤L, `prodAux (framedParamsReg 0) k = reindex e0.symm ek.symm (fromBlocks 1 0 0 0)` (the corner).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:25:- Banked: `hasStrictFDerivAt_prodAux_entry` proves EXISTENCE of a strict derivative D for each entry `fun y => prodAux (g y) k i j` (opaque D, built by Leibniz HasStrictFDerivAt.sum/.mul induction), but NOT the explicit value.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:26:- `corner_reindex_mul`: corner * corner = corner (idempotent under the chain, reindexed).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:28:GOAL: the reg-slice `r0 ↦ deepestEPivot (r0,0)` (each output coord is a block entry (P11-1)/P12/P21 of `P=reindex(prod(framedParamsReg(r0,0)))`) has strict derivative `id` at 0. The math: dP|_0 = Σ_s corner·δC_s·corner. corner·δC_s·corner keeps only: (0,0)-block X_s for all s, (0,1)-block Y_s for the LAST layer, (1,0)-block Z_s for the FIRST layer. With gauge=0 the reg-coords route X to first layer, Y to last, Z to first (via regBoundaryToRegGauge∘regPivotFinEquiv shared with regResidualPack=regPivotFinEquiv), so each coord's derivative = the matching r0 projection.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:31:(A) Prove a NEW explicit-value Leibniz lemma `prodAux_corner_fderiv`: by induction, the strict derivative of `prodAux(framedParamsReg(r0,0)) k i j` at 0 is `Σ_{s<k} (corner_{0..s})·(δlayer_s)·(corner_{s+1..k})` — but this needs naming the running-corner-prefixes and is heavy.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:32:(B) Bypass the explicit Σ: prove directly that the COORDINATE function `r0 ↦ (block entry of reindex prod) i` has derivative `proj i`, by showing the function equals `r0 ↦ r0 i + (higher order)` — i.e. find a clean `HasStrictFDerivAt` via the structure without naming the full Σ.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:35:Which is least Lean-painful at v4.29? Give the concrete lemma statement(s) + tactic skeleton for the recommended route. Be concrete about avoiding the dependent-Fin cast blowup in the prodAux induction. Mathlib v4.29 names only.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:39:/bin/bash -lc 'rg -n "hasStrictFDerivAt_iff_isLittleO|HasStrictFDerivAt|congr_fderiv|unique.*fderiv|isLittleO" $(pwd)/.lake/packages/mathlib/Mathlib $(pwd)/.lake/packages/mathlib/Mathlib.lean' in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:42:2026-06-23T17:57:08.569602Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc 'rg -n "hasStrictFDerivAt_iff_isLittleO|HasStrictFDerivAt|congr_fderiv|unique.*fderiv|isLittleO" $(pwd)/.lake/packages/mathlib/Mathlib $(pwd)/.lake/packages/mathlib/Mathlib.lean'`: CreateProcess { message: "Rejected(\"rejected by user\")" }
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:153:/bin/bash -lc 'rg -n "hasStrictFDerivAt_prodAux_entry|prodAux_framedParamsReg_zero_aux|corner_reindex_mul|deepestEPivot|framedParamsReg|regBoundaryToRegGauge|regResidualPack|regPivotFinEquiv" -S .' in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:175:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:121:noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:176:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:129:/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:178:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:132:theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:179:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:134:    framedParamsReg H r hr hL 0 s
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:180:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:138:  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:181:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:141:/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:182:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:144:theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:183:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:147:    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s i j) := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:184:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:149:  have hentry : (fun p => framedParamsReg H r hr hL p s i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:185:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:155:    simp only [framedParamsReg, framedLayer, Matrix.reindex_apply, Matrix.submatrix_apply,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:187:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:191:`deepestEPivot` is `pack ∘ residual ∘ reindex ∘ prod ∘ framedParamsReg`; its `ContDiff ⊤` reduces to
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:188:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:192:`ContDiff ⊤ (fun x => prod H (g x))` for `g = framedParamsReg` (each layer affine in the slots, so
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:189:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:256:theorem hasStrictFDerivAt_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:190:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:308:/-- **`HasStrictFDerivAt` of the full layer-product entries** (`hasStrictFDerivAt_prodAux_entry` at
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:192:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:318:  hasStrictFDerivAt_prodAux_entry H g x g' hg L (Nat.lt_succ_self L) i j
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:196:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:12:>   `HasStrictFDerivAt deepestEPivot D_E 0 ∧ (e : →L) = regStraightenTotalCLM D_E`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:197:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:17:>   - `D_E := fderiv ℝ deepestEPivot 0`, `hsd : HasStrictFDerivAt deepestEPivot D_E 0` via
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:200:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:26:>   - `hasStrictFDerivAt_prodAux_entry` / `hasStrictFDerivAt_prod_entry`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:202:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:36:>   `HasStrictFDerivAt (fun r0 : Reg => deepestEPivot H r hr hL (r0, 0)) (ContinuousLinearMap.id ℝ Reg) 0`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:203:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:38:>   `dP|_0 = Σ_s corner·δC_s·corner` (corners idempotent, `prodAux_framedParamsReg_zero` banked) keeps,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:215:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:11:      HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL (r0, 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:216:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:23:    -- goal: HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:219:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:31:Output coord = `(P.toBlocks₁₁ − 1) a b` where `P = reindex (prod (framedParamsReg (r0,0)))`. By the #91
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:222:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:35:`(framedParamsReg (r0,0)) reads readX_first (r0) a b = regGaugeSlotEquiv (r0,0) ⟨0, inl(inl(a,b))⟩`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:225:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:46:    -- d(prod (framedParamsReg (r0,0)))|_0 = Σ_s (corner prefix) · δC_s · (corner suffix), and the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:226:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:49:      HasFDerivAt (fun r0 => (reindex (prod (framedParamsReg (r0,0)))) i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:227:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:54:1. `prod_framedParamsReg_zero` (banked): at r0=0, `prod (framedParamsReg 0) = reindex (fromBlocks 1 0 0 0)`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:228:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:56:2. The product derivative at 0 (Leibniz, cobuild's `hasStrictFDerivAt_prodAux_entry` VALUE, or a direct
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:229:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:58:   AT r0=0 are the idempotent corner (by `prodAux_framedParamsReg_zero_aux` — the partial products at 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:230:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:62:   only for the FIRST. The `fromBlocks_multiply` / `corner_reindex_mul` kernels (banked in
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:235:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:84:- `prod_framedParamsReg_zero`, `prodAux_framedParamsReg_zero_aux`, `corner_reindex_mul`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:236:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:87:- `hasStrictFDerivAt_prodAux_entry` (cobuild @2bf7065) — IF a Leibniz value is wanted; else direct induction.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:239:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:89:theorem corner_reindex_mul {a b c r : ℕ}
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:240:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:131:the block-normal corner `reindex (fromBlocks 1 0 0 0)` (`framedParamsReg_zero`), and the corner is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:241:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:133:(at width `H 0 × H ⟨k⟩`). Proven by `prodAux_succ` + `framedParamsReg_zero` + `fromBlocks_multiply`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:242:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:135:theorem prodAux_framedParamsReg_zero_aux (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:243:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:138:      prodAux H (framedParamsReg H r hr hL 0) k hk
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:244:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:155:      -- IS the corner at the running widths (`framedParamsReg_zero` then `cases e1; cases e2` collapses the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:245:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:157:      -- the Eq.mpr-cast layer = the corner at the running widths (PROBE-proven: `framedParamsReg_zero`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:246:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:159:      have hlayer : ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:247:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:164:        rw [framedParamsReg_zero H r hr hL ⟨k, hkL⟩]; cases e1; cases e2; rfl
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:248:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:165:      have hstep : prodAux H (framedParamsReg H r hr hL 0) (k + 1) hk
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:249:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:166:          = prodAux H (framedParamsReg H r hr hL 0) k hk' *
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:250:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:170:        show prodAux H (framedParamsReg H r hr hL 0) k hk' *
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:251:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:171:            ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:252:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:173:        exact congrArg (prodAux H (framedParamsReg H r hr hL 0) k hk' * ·) hlayer
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:253:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:180:        exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:255:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:185:gauge-sliced product at the deepest gauge slot is the block-normal corner: `prod (framedParamsReg 0) =
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:256:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:188:theorem prodAux_framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:257:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:190:    prod H (framedParamsReg H r hr hL 0)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:258:./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:194:  have h := prodAux_framedParamsReg_zero_aux H r hr hL L (Nat.lt_succ_self L) hL
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:262:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:7:      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0, 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:281:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:98:      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0,0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:282:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:103:`d(P)|₀ = Σ_s corner·δC_s·corner`; (b) the idempotent-sandwich collapse (`prodAux_framedParamsReg_zero` +
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:295:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:132:  is which X/Y/Z) → ripples to `readX/Y/Z` VALUES → `framedParamsReg`/`deepestEPivot` VALUES.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:310:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:345:reading the reg + spectator slots, with `dE(0) = id` (typed `HasStrictFDerivAt deepestEPivot (fst) 0`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:316:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:365:`Fin nReg → ℝ` via `regResidualPack`. `P = ∏ (framedParamsReg p)` reindexed to `r ⊕ M` block shape;
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:318:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:372:      (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL p))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:322:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:381:  -- Each layer entry of `framedParamsReg` is `ContDiff` (`contDiff_framedParamsReg_entry`), so each
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:323:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:382:  -- entry of `prod H (framedParamsReg ·)` is `ContDiff` (`contDiff_prod_entry`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:324:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:384:      ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s a b) :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:325:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:385:    contDiff_framedParamsReg_entry H r hr hL
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:326:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:387:      ContDiff ℝ (⊤ : ℕ∞) (fun p => prod H (framedParamsReg H r hr hL p) a b) :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:327:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:388:    fun a b => contDiff_prod_entry H (framedParamsReg H r hr hL) hlayer a b
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:330:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:397:          (prod H (framedParamsReg H r hr hL p))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:341:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:434:  -- Per-coordinate: `HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0`. The #91
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:342:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:435:  -- idempotent-sandwich: `d(prod(framedParamsReg (r0,0)))|_0 = Σ_s corner·δC_s·corner` keeps the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:345:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:446:on `DeepestSplit`, det 1, invertible). Bundled: `∃ D_E (e : ≃L), HasStrictFDerivAt deepestEPivot D_E 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:348:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:455:      HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 ∧
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:351:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:461:  have hsd : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:355:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:474:    have hsd0 : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:359:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:490:  -- At the origin slot, `∏(framedParamsReg 0)` is the reindexed corner `fromBlocks 1 0 0 0`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:360:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:491:  -- (`prod_framedParamsReg_zero`); the outer `reindex` in `P` cancels it, so `P = fromBlocks 1 0 0 0`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:361:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:495:        (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL 0)))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:362:./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:497:    rw [prodAux_framedParamsReg_zero H r hr hL, ← Matrix.reindex_symm,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:373:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:7:    HasStrictFDerivAt deepestEPivot D_E 0 ∧ (e : DeepestSplit →L DeepestSplit) = regStraightenTotalCLM D_E
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:376:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:16:  where P = reindex eIn eOut (prod H (framedParamsReg p))  [reindex/eIn/eOut are FIXED Equivs,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:377:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:17:  constant in p]. So deepestEPivot is: pack ∘ (block-projections − const) ∘ reindex ∘ (prod ∘ framedParamsReg).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:378:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:18:  The ONLY p-dependence is in prod H (framedParamsReg p). reindex, toBlocks, −1, pack are all CONSTANT-LINEAR.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:379:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:19:- framedParamsReg p : each layer s = reindex (fromBlocks (1+X_s) Y_s Z_s 0), where (X_s,Y_s,Z_s) =
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:380:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:28:- hasStrictFDerivAt_prodAux_entry : ∀ entry, ∃ D, HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j) D x
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:381:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:31:- prodAux_framedParamsReg_zero : prod H (framedParamsReg 0) = reindex (corner = fromBlocks 1 0 0 0)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:382:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:33:- fromBlocks_blockdiag_idem (corner·corner = corner), corner_reindex_mul.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:383:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:34:- deepestEPivot_contdiff : ContDiff ⊤ deepestEPivot (so HasStrictFDerivAt deepestEPivot (fderiv ℝ … 0) 0 is FREE).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:384:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:42:THE GAP: my hasStrictFDerivAt_prodAux_entry gives ∃ D (opaque). I need the EXPLICIT D_E (or at least
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:387:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:52:    an explicitly-constructed N), prove HasStrictFDerivAt deepestEPivot (the reg-component of e) 0 by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:389:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:23:- `framedParamsReg H r hr hL p : Params H`, each layer = `reindex e.symm e'.symm (fromBlocks (1+X_s) Y_s Z_s 0)` where X_s=readX p s etc (linear in p, =0 at p=0).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:390:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:24:- At p=0 (gauge slot 0): `prodAux_framedParamsReg_zero_aux`: for 1≤k≤L, `prodAux (framedParamsReg 0) k = reindex e0.symm ek.symm (fromBlocks 1 0 0 0)` (the corner).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:391:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:25:- Banked: `hasStrictFDerivAt_prodAux_entry` proves EXISTENCE of a strict derivative D for each entry `fun y => prodAux (g y) k i j` (opaque D, built by Leibniz HasStrictFDerivAt.sum/.mul induction), but NOT the explicit value.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:392:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:26:- `corner_reindex_mul`: corner * corner = corner (idempotent under the chain, reindexed).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:393:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:28:GOAL: the reg-slice `r0 ↦ deepestEPivot (r0,0)` (each output coord is a block entry (P11-1)/P12/P21 of `P=reindex(prod(framedParamsReg(r0,0)))`) has strict derivative `id` at 0. The math: dP|_0 = Σ_s corner·δC_s·corner. corner·δC_s·corner keeps only: (0,0)-block X_s for all s, (0,1)-block Y_s for the LAST layer, (1,0)-block Z_s for the FIRST layer. With gauge=0 the reg-coords route X to first layer, Y to last, Z to first (via regBoundaryToRegGauge∘regPivotFinEquiv shared with regResidualPack=regPivotFinEquiv), so each coord's derivative = the matching r0 projection.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:394:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:31:(A) Prove a NEW explicit-value Leibniz lemma `prodAux_corner_fderiv`: by induction, the strict derivative of `prodAux(framedParamsReg(r0,0)) k i j` at 0 is `Σ_{s<k} (corner_{0..s})·(δlayer_s)·(corner_{s+1..k})` — but this needs naming the running-corner-prefixes and is heavy.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:401:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:50:Prove this coordinatewise by `hasStrictFDerivAt_pi''`. For each packed coordinate, unfold `deepestEPivot`, `framedParamsReg`, `framedLayer`, then use the gauge-zero slice facts for reads:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:402:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:84:      -- packed residual of prod H (framedParamsReg (r0,0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:405:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:113:The wall is `deepestEPivot_regSlice_hasStrictFDerivAt_id`, specifically making `regResidualPack` and `regGaugeIdxSplit` expose that the regular coordinates are exactly `(X_first, Y_last, Z_first)`. Fallback: do A only for the reg-slice, not full `(reg,gauge)`: name a restricted Leibniz derivative for `fun r => prod H (framedParamsReg (r,0))`; collapse it to `id`; still keep `D_E := fderiv` for the full map.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:406:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:1:# Statement card — #123 FOLD1: the idempotent `prodAux`-at-0 fold + `deepestEPivot_base`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:407:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:3:> **Claim.** At the origin gauge slot, the framed (T=0) layer product `∏(framedParamsReg 0)` is the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:408:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:5:> `deepestEPivot 0 = 0`. This is FOLD1 (value) of the #123 `prodAux` fold family — the cast-wall break
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:410:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:9:>   - `DLNFibre.DLN.RLCT.prodAux_framedParamsReg_zero_aux` and
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:411:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:10:>     `DLNFibre.DLN.RLCT.prodAux_framedParamsReg_zero` (crux2's single-writer
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:413:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:15:> - **Gloss.** Every layer of `framedParamsReg H r hr hL 0` is, at the origin, the block-normal corner
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:414:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:17:>   (`framedParamsReg_zero`). The corner is idempotent under the chain product, so the running product
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:415:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:18:>   through `k ≥ 1` layers is again the corner at width `H 0 × H ⟨k⟩` (`prodAux_framedParamsReg_zero_aux`),
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:416:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:19:>   and at `k = L` this is `∏ = reindex(corner)` (`prodAux_framedParamsReg_zero`). The pivot residual
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:418:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:27:>   matrix-VALUE rewrite of `framedParamsReg_zero` under the fold. TWO independent cracks:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:419:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:32:>     (the `prodAux 0 = 1` head), `k ≥ 1` → `rw [ih]` + `corner_reindex_mul` (the idempotent
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:420:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:38:>   `prodAux_framedParamsReg_zero_aux`, `prodAux_framedParamsReg_zero`, `deepestEPivot_base` — all
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:421:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:42:>   `prodAux_succ_layer` (the kernel), `corner_reindex_mul` (`submatrix_mul_equiv` + `fromBlocks_multiply`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:422:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:45:>   - `deepestEPivot_deriv` (#82): the `HasStrictFDerivAt` Leibniz derivative + shear — analytic, OPEN.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:423:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:13:- `prodAux_framedParamsReg_zero_aux` + `prodAux_framedParamsReg_zero` (crux2's file, axiom-clean).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:427:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:20:  named sorry. BANKED clean-three: `hasStrictFDerivAt_prodAux_entry`/`_prod_entry` (the L-fold product
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:430:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:26:  HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0)) id 0` — the #91 idempotent-sandwich (gauge-zero
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:439:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:95:- `deepestEPivot` CONCRETE def + `regResidualPack` @20ad514; `framedParamsReg` (T=0) + `_zero` @2f3508e;
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:440:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:97:  + `contDiff_framedParamsReg_entry` @ecd8d6f.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:444:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:115:- **`_base`** (`deepestEPivot 0 = 0`): **DONE** (clean-three) via `prodAux_framedParamsReg_zero` (the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:445:./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:118:- **`_deriv`** (the bundled shear): the concrete shear `D_E` + `HasStrictFDerivAt deepestEPivot D_E 0`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:609:The cast-heavy `prodAux` induction behind PIN2's frame bridge:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:620:- (`prodAux_succ` SHAPE, typechecks) the `k+1` fold IS the running product times the layer transported
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:639:/-- **`prodAux` recursion, reindex-explicit** (statement TYPECHECKS; proof is the deferred entry-chase).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:642:theorem prodAux_succ (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:647:    prodAux H A (k + 1) hk
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:648:      = (prodAux H A k (Nat.lt_of_succ_lt hk)) *
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:655:block `Matrix.reindex eC.symm eS.symm M` at the running widths, then the `prodAux` succ-step is the clean
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:656:product `prodAux k * reindex eC.symm eS.symm M` — the def's `Eq.mpr` cast is collapsed by the index-level
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:657:`cases e1; cases e2` idiom (the `contDiff_prodAux_entry` precedent). All three folds (value / deriv /
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:660:theorem prodAux_succ_layer (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:672:    prodAux H A (k + 1) hk
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:673:      = prodAux H A k (Nat.lt_of_succ_lt hk) * Matrix.reindex eC.symm eS.symm M := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:680:  show prodAux H A k hk' *
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:683:  refine congrArg (prodAux H A k hk' * ·) ?_
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:691:theorem corner_reindex_mul {a b c r : ℕ}
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:732:/-- **The idempotent fold at `0`** (`prodAux` form, `1 ≤ k`). At the deepest gauge slot, every layer is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:733:the block-normal corner `reindex (fromBlocks 1 0 0 0)` (`framedParamsReg_zero`), and the corner is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:735:(at width `H 0 × H ⟨k⟩`). Proven by `prodAux_succ` + `framedParamsReg_zero` + `fromBlocks_multiply`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:737:theorem prodAux_framedParamsReg_zero_aux (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:740:      prodAux H (framedParamsReg H r hr hL 0) k hk
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:751:      -- INDEX-level equalities (the `prodAux` def's own, `Fin.ext`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:756:      -- `prodAux (k+1)` unfolds (def at Loss.lean) to `prodAux k * (Eq.mpr-cast layer)`, and that layer
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:757:      -- IS the corner at the running widths (`framedParamsReg_zero` then `cases e1; cases e2` collapses the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:759:      -- the Eq.mpr-cast layer = the corner at the running widths (PROBE-proven: `framedParamsReg_zero`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:761:      have hlayer : ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:766:        rw [framedParamsReg_zero H r hr hL ⟨k, hkL⟩]; cases e1; cases e2; rfl
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:767:      have hstep : prodAux H (framedParamsReg H r hr hL 0) (k + 1) hk
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:768:          = prodAux H (framedParamsReg H r hr hL 0) k hk' *
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:772:        show prodAux H (framedParamsReg H r hr hL 0) k hk' *
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:773:            ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:775:        exact congrArg (prodAux H (framedParamsReg H r hr hL 0) k hk' * ·) hlayer
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:779:        -- accumulator is `prodAux 0 = 1`; `1 * corner = corner` (`prodAux 0` reduces, then `one_mul`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:782:        exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:787:gauge-sliced product at the deepest gauge slot is the block-normal corner: `prod (framedParamsReg 0) =
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:788:reindex (fromBlocks 1 0 0 0)` (at width `H 0 × H (last)`). `prod = prodAux L`; specialize the `aux`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:790:theorem prodAux_framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:792:    prod H (framedParamsReg H r hr hL 0)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:796:  have h := prodAux_framedParamsReg_zero_aux H r hr hL L (Nat.lt_succ_self L) hL
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:872:reading the reg + spectator slots, with `dE(0) = id` (typed `HasStrictFDerivAt deepestEPivot (fst) 0`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:876:`HasStrictFDerivAt (fst) 0`, `0 ↦ 0`) are the residual gauge-geometry obligation: the product-residual
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:892:`Fin nReg → ℝ` via `regResidualPack`. `P = ∏ (framedParamsReg p)` reindexed to `r ⊕ M` block shape;
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:899:      (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL p))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:908:  -- Each layer entry of `framedParamsReg` is `ContDiff` (`contDiff_framedParamsReg_entry`), so each
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:909:  -- entry of `prod H (framedParamsReg ·)` is `ContDiff` (`contDiff_prod_entry`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:911:      ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s a b) :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:912:    contDiff_framedParamsReg_entry H r hr hL
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:914:      ContDiff ℝ (⊤ : ℕ∞) (fun p => prod H (framedParamsReg H r hr hL p) a b) :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:915:    fun a b => contDiff_prod_entry H (framedParamsReg H r hr hL) hlayer a b
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:924:          (prod H (framedParamsReg H r hr hL p))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:950:    HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:961:  -- Per-coordinate: `HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0`. The #91
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:962:  -- idempotent-sandwich: `d(prod(framedParamsReg (r0,0)))|_0 = Σ_s corner·δC_s·corner` keeps the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:966:  -- atom is the patient analytic fill (the Leibniz sandwich VALUE through `prodAux` + the cancel).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:973:on `DeepestSplit`, det 1, invertible). Bundled: `∃ D_E (e : ≃L), HasStrictFDerivAt deepestEPivot D_E 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:982:      HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 ∧
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:988:  have hsd : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:992:  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => ((r0, 0) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:999:  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1001:    have hsd0 : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1017:  -- At the origin slot, `∏(framedParamsReg 0)` is the reindexed corner `fromBlocks 1 0 0 0`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1033:/-- **`ContDiff` of the full layer-product entries** (`contDiff_prodAux_entry` at `k = L`). -/
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1040:  contDiff_prodAux_entry H g hg L (Nat.lt_succ_self L) i j
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1042:/-- **`HasStrictFDerivAt` of the partial-product ENTRIES** (the `_deriv` infrastructure, entry-wise to
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1043:dodge the matrix-norm instance, mirroring `contDiff_prodAux_entry`). If each layer ENTRY has a strict
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1044:derivative `g' s i j` at `x`, then each `prodAux` entry has the LEIBNIZ strict derivative
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1045:`∑ m, (prodAux k i m) · (layer deriv) + (prodAux k deriv) · (layer i m)` — built by `HasStrictFDerivAt.sum`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1046:of `HasStrictFDerivAt.mul`. The derivative VALUE is the sum-of-products `prodAux'`; the deepest-point
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1048:theorem hasStrictFDerivAt_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1052:      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1055:      ∃ D : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j) D x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1060:      -- `prodAux 0 = 1`; each entry is constant, derivative `0`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1062:      have : (fun y => prodAux H (g y) 0 hk i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1073:      -- `prodAux (k+1) i j = ∑ m, prodAux k i m · (cast layer k) m j`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1074:      have hentry : (fun y => prodAux H (g y) (k + 1) hk i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1075:          = fun y => ∑ m, prodAux H (g y) k hk' i m
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1080:      -- Each summand `prodAux k i m * (cast layer) m j` has a strict derivative (product rule).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1081:      -- `HasStrictFDerivAt.sum` over `m`; each summand via `HasStrictFDerivAt.mul` of (ih) and (the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1084:          HasStrictFDerivAt (fun y => prodAux H (g y) k hk' i m
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1089:        have hlayer : HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1098:      exact ⟨∑ m, D m, HasStrictFDerivAt.fun_sum (fun m _ => hD m)⟩
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1100:/-- **`HasStrictFDerivAt` of the full layer-product entries** (`hasStrictFDerivAt_prodAux_entry` at
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1107:      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1109:    ∃ D : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => prod H (g y) i j) D x :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1110:  hasStrictFDerivAt_prodAux_entry H g x g' hg L (Nat.lt_succ_self L) i j
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1394:gauge-sliced tuple `C : Params H` — no new fold; `prod`/`prodAux` are reused.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1416:function (defeq), giving `ContDiff` of `regGaugeSlotEquiv` (hence of the `readX/Y/Z` entries) via
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1440:/-- Each `readX` entry is `ContDiff ⊤` (a coordinate of the `ContDiff` gauge read). -/
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1441:theorem contDiff_readX_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1443:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readX H r hr hL p s i j) := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1444:  simp only [readX, Matrix.of_apply]
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1447:/-- Each `readY` entry is `ContDiff ⊤`. -/
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1448:theorem contDiff_readY_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1451:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readY H r hr hL p s i j) := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1452:  simp only [readY, Matrix.of_apply]
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1455:/-- Each `readZ` entry is `ContDiff ⊤`. -/
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1456:theorem contDiff_readZ_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1459:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readZ H r hr hL p s i j) := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1460:  simp only [readZ, Matrix.of_apply]
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1480:`readX/readY/readZ`) and the reduced core `T_s` (read off the core slot via `paramsEquivFlat (deepestM)`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1489:      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1490:      (readZ H r hr hL (q.1, q.2.2) s)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1498:`Fin nReg` pack convention (the open obstruction), only on the gauge read `readX/Y/Z`. -/
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1499:noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1504:      (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1507:/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1510:theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1512:    framedParamsReg H r hr hL 0 s
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1516:  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1517:    readZ_zero H r hr hL s, add_zero]
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1519:/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1520:`fromBlocks (1+X) Y Z 0` block entry (reindexed), i.e. `1+readX` / `readY` / `readZ` / `0`, each
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1522:theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1525:    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s i j) := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1527:  have hentry : (fun p => framedParamsReg H r hr hL p s i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1528:      = fun p => Matrix.fromBlocks (1 + readX H r hr hL p s) (readY H r hr hL p s)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1529:          (readZ H r hr hL p s) (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1533:    simp only [framedParamsReg, framedLayer, Matrix.reindex_apply, Matrix.submatrix_apply,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1540:  · -- (1 + X) entry: `(if a = b then 1 else 0) + readX … a b` — the `if` is a constant in `p`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1541:    exact contDiff_const.add (contDiff_readX_entry H r hr hL s a b)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1542:  · exact contDiff_readY_entry H r hr hL s a b
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1543:  · exact contDiff_readZ_entry H r hr hL s a b
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1562:typechecks). The PROOF is the cast-heavy `prodAux` induction: invariant `prodAux H C k = P0 *
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1563:prodAux H A k * (frame at k)`, interior interfaces cancelling by the `Q s * P s' = 1` conditions. The
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1605:def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1611:      refine (prodAux H A k hk') * ?_
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1622:  prodAux H A L (Nat.lt_succ_self L)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1694:- `prodAux H A : (k:ℕ) → (hk : k < L+1) → Matrix (Fin (H 0)) (Fin (H ⟨k,hk⟩)) ℝ`, with
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1695:  `prodAux 0 = 1`, `prodAux (k+1) = prodAux k * (cast layer ⟨k,hkL⟩)` (dependent Fin casts e1/e2).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1696:- `prod H A := prodAux H A L (Nat.lt_succ_self L)`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1697:- `framedParamsReg H r hr hL p : Params H`, each layer = `reindex e.symm e'.symm (fromBlocks (1+X_s) Y_s Z_s 0)` where X_s=readX p s etc (linear in p, =0 at p=0).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1698:- At p=0 (gauge slot 0): `prodAux_framedParamsReg_zero_aux`: for 1≤k≤L, `prodAux (framedParamsReg 0) k = reindex e0.symm ek.symm (fromBlocks 1 0 0 0)` (the corner).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1699:- Banked: `hasStrictFDerivAt_prodAux_entry` proves EXISTENCE of a strict derivative D for each entry `fun y => prodAux (g y) k i j` (opaque D, built by Leibniz HasStrictFDerivAt.sum/.mul induction), but NOT the explicit value.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1700:- `corner_reindex_mul`: corner * corner = corner (idempotent under the chain, reindexed).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1702:GOAL: the reg-slice `r0 ↦ deepestEPivot (r0,0)` (each output coord is a block entry (P11-1)/P12/P21 of `P=reindex(prod(framedParamsReg(r0,0)))`) has strict derivative `id` at 0. The math: dP|_0 = Σ_s corner·δC_s·corner. corner·δC_s·corner keeps only: (0,0)-block X_s for all s, (0,1)-block Y_s for the LAST layer, (1,0)-block Z_s for the FIRST layer. With gauge=0 the reg-coords route X to first layer, Y to last, Z to first (via regBoundaryToRegGauge∘regPivotFinEquiv shared with regResidualPack=regPivotFinEquiv), so each coord's derivative = the matching r0 projection.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1705:(A) Prove a NEW explicit-value Leibniz lemma `prodAux_corner_fderiv`: by induction, the strict derivative of `prodAux(framedParamsReg(r0,0)) k i j` at 0 is `Σ_{s<k} (corner_{0..s})·(δlayer_s)·(corner_{s+1..k})` — but this needs naming the running-corner-prefixes and is heavy.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1706:(B) Bypass the explicit Σ: prove directly that the COORDINATE function `r0 ↦ (block entry of reindex prod) i` has derivative `proj i`, by showing the function equals `r0 ↦ r0 i + (higher order)` — i.e. find a clean `HasStrictFDerivAt` via the structure without naming the full Σ.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1709:Which is least Lean-painful at v4.29? Give the concrete lemma statement(s) + tactic skeleton for the recommended route. Be concrete about avoiding the dependent-Fin cast blowup in the prodAux induction. Mathlib v4.29 names only.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1713:/bin/bash -lc 'rg -n "hasStrictFDerivAt_iff_isLittleO|HasStrictFDerivAt|congr_fderiv|unique.*fderiv|isLittleO" $(pwd)/.lake/packages/mathlib/Mathlib $(pwd)/.lake/packages/mathlib/Mathlib.lean' in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1716:2026-06-23T17:57:08.569602Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc 'rg -n "hasStrictFDerivAt_iff_isLittleO|HasStrictFDerivAt|congr_fderiv|unique.*fderiv|isLittleO" $(pwd)/.lake/packages/mathlib/Mathlib $(pwd)/.lake/packages/mathlib/Mathlib.lean'`: CreateProcess { message: "Rejected(\"rejected by user\")" }
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1827:/bin/bash -lc 'rg -n "hasStrictFDerivAt_prodAux_entry|prodAux_framedParamsReg_zero_aux|corner_reindex_mul|deepestEPivot|framedParamsReg|regBoundaryToRegGauge|regResidualPack|regPivotFinEquiv" -S .' in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1849:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:121:noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1850:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:129:/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1852:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:132:theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1853:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:134:    framedParamsReg H r hr hL 0 s
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1854:./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:138:  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1865:   Biggest risk: dependent `prodAux` casts plus named Leibniz derivative will spread through every entry.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1880:have hE : HasStrictFDerivAt E D_E 0 :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1887:- `HasStrictFDerivAt.comp`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1889:- `HasStrictFDerivAt.hasFDerivAt`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1903:  HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1908:Prove this coordinatewise by `hasStrictFDerivAt_pi''`. For each packed coordinate, unfold `deepestEPivot`, `framedParamsReg`, `framedLayer`, then use the gauge-zero slice facts for reads:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1911:readX H r hr hL (r0, 0) s = if s = first then X_from_reg r0 else 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1912:readY H r hr hL (r0, 0) s = if s = last  then Y_from_reg r0 else 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1913:readZ H r hr hL (r0, 0) s = if s = first then Z_from_reg r0 else 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1940:  HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1942:      -- packed residual of prod H (framedParamsReg (r0,0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1971:The wall is `deepestEPivot_regSlice_hasStrictFDerivAt_id`, specifically making `regResidualPack` and `regGaugeIdxSplit` expose that the regular coordinates are exactly `(X_first, Y_last, Z_first)`. Fallback: do A only for the reg-slice, not full `(reg,gauge)`: name a restricted Leibniz derivative for `fun r => prod H (framedParamsReg (r,0))`; collapse it to `id`; still keep `D_E := fderiv` for the full map.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:1973:/bin/bash -lc "rg -n \"hasStrictFDerivAt_pi|HasStrictFDerivAt\\.fun_sum|\\.fderiv|hasStrictFDerivAt_iff_isLittleO|isLittleO\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus lean/.lake/packages/mathlib/Mathlib/Topology -S" in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2021:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:390:theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2023:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:399:  convert HasStrictFDerivAt.fun_sum h; simp
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2056:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:364:theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2057:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:365:    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2284:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:243:alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2511:The v4.29 API names that matter are present locally: `hasStrictFDerivAt_pi'`, `hasStrictFDerivAt_pi''`, `hasStrictFDerivAt_pi`, `HasStrictFDerivAt.fun_sum`, `hasStrictFDerivAt_iff_isLittleO`, and the uniqueness route through `.hasFDerivAt.fderiv`. That means you do not need an `isLittleO` proof unless you want to reprove product differentiability from scratch.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2535:    HasStrictFDerivAt Φ Φ' x ↔ ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2539:theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2540:    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2544:    HasStrictFDerivAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) f :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2548:    HasStrictFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2549:      ∀ i, HasStrictFDerivAt (φ i) (φ' i) x :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2570:theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2571:    HasStrictFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2577:theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2578:    HasStrictFDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2579:  convert HasStrictFDerivAt.fun_sum h; simp
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2601:    HasStrictFDerivAt b (h.deriv p) p := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2613:/bin/bash -lc "rg -n \"alias .*HasStrictFDerivAt.*isLittleO|HasStrictFDerivAt\\.isLittleO|HasStrictFDerivAt\\.of_isLittleO|hasStrictFDerivAt_iff_isLittleO\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv -S" in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2623:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:243:alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2627:/bin/bash -lc "rg -n \"theorem HasStrictFDerivAt\\.mul|protected theorem HasStrictFDerivAt\\.mul|HasStrictFDerivAt.*mul\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv -S" in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2629:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:57:theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2630:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:59:theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2631:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:60:    HasStrictFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2632:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:116:theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2633:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:117:    HasStrictFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2634:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:170:theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2635:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:177:theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2636:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:270:theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2637:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:275:theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2638:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:342:theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2639:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:551:theorem HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2640:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:669:    HasStrictFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2641:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:712:    HasStrictFDerivAt Inv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2642:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:91:theorem HasStrictFDerivAt.hasStrictFDerivAt_norm_smul
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2643:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:96:  have h2 : HasStrictFDerivAt (fun y ↦ |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2644:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:105:theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2645:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:110:theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2679:/bin/bash -lc "rg -n \"theorem .*fderiv.*eq|protected theorem HasFDerivAt\\.fderiv|def fderiv|theorem HasStrictFDerivAt\\.hasFDerivAt|hasFDerivAt.*fderiv\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean -S" in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2683:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:317:protected theorem HasStrictFDerivAt.hasFDerivAt (hf : HasStrictFDerivAt f f' x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2690:I’m going to give the route as a staged API, not a giant theorem. The important design choice is to compute values by asking Lean for the `fderiv` of a function already proved strictly differentiable, then rewrite that `fderiv` to the explicit formula by uniqueness. That keeps casts local to the existing `prodAux` recursion pattern.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2708:theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2709:    (hb : HasStrictFDerivAt b b' x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2710:    HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2715:theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2716:    HasStrictFDerivAt (c * d) (c x • d' + d x • c') x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2758:web search: github mathlib4 v4.29.0 HasStrictFDerivAt.fun_sum
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2766:One place where I would add a named lemma is the packing cancellation, independent of calculus. Once `regGaugeIdxSplit_boundary_apply` is proved, all later `readX/readY/readZ` derivative/value lemmas should reduce with `simp`; without that lemma, every coordinate proof reopens the opaque `Set.range` split.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2911:/bin/bash -lc "rg -n \"HasStrictFDerivAt\\.congr|HasFDerivAt\\.congr|congr_fderiv\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv -S" in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2915:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:114:theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2918:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:125:theorem HasStrictFDerivAt.congr_of_eventuallyEq (h : HasStrictFDerivAt f f' x)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2959:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:114:theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:2996:`HasStrictFDerivAt.congr_fderiv` and `HasFDerivAt.congr_fderiv` do exist in v4.29, but they are only for replacing the derivative map after you have proved an equality of CLMs. They will not extract the value from an existential derivative by themselves.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3003:    HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3006:theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3007:    HasStrictFDerivAt f g' x :=
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3062:noncomputable def prodAuxEntryDeriv
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3077:      (prodAux H (g x) k hk' i m) •
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3082:          prodAuxEntryDeriv H g x g' k hk' i m)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3088:theorem hasStrictFDerivAt_prodAux_entry_explicit
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3092:    (hg : ∀ s i j, HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3094:    HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3095:      (fun y => prodAux H (g y) k hk i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3096:      (prodAuxEntryDeriv H g x g' k hk i j) x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3101:      simpa [prodAuxEntryDeriv] using
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3109:      -- assemble with `HasStrictFDerivAt.fun_sum`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3110:      -- close derivative-map equality with `simp [prodAuxEntryDeriv, add_comm, add_left_comm, add_assoc]`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3119:    HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3124:          (prod H (framedParamsReg H r hr hL (r0, 0)))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3152:Use it to prove `readX/readY/readZ` slice lemmas: `readX` is nonzero only at `firstLayer`, `readY` only at `lastLayer`, `readZ` only at `firstLayer`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3171:So: **do not use `hasStrictFDerivAt_iff_isLittleO` for this.** Mathlib v4.29 has it, and also has `HasStrictFDerivAt.congr_fderiv`, but the calculus API route with `HasStrictFDerivAt.mul`, `HasStrictFDerivAt.fun_sum`, `hasStrictFDerivAt_pi`, and `.hasFDerivAt.fderiv` is much less painful. The dependent-Fin casts stay confined to the single `prodAuxEntryDeriv` induction, using the same `e1/e2` pattern already working in your existence lemma.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3181:noncomputable def prodAuxEntryDeriv
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3196:      (prodAux H (g x) k hk' i m) •
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3201:          prodAuxEntryDeriv H g x g' k hk' i m)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3207:theorem hasStrictFDerivAt_prodAux_entry_explicit
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3211:    (hg : ∀ s i j, HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3213:    HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3214:      (fun y => prodAux H (g y) k hk i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3215:      (prodAuxEntryDeriv H g x g' k hk i j) x := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3220:      simpa [prodAuxEntryDeriv] using
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3228:      -- assemble with `HasStrictFDerivAt.fun_sum`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3229:      -- close derivative-map equality with `simp [prodAuxEntryDeriv, add_comm, add_left_comm, add_assoc]`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3238:    HasStrictFDerivAt
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3243:          (prod H (framedParamsReg H r hr hL (r0, 0)))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3271:Use it to prove `readX/readY/readZ` slice lemmas: `readX` is nonzero only at `firstLayer`, `readY` only at `lastLayer`, `readZ` only at `firstLayer`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:3290:So: **do not use `hasStrictFDerivAt_iff_isLittleO` for this.** Mathlib v4.29 has it, and also has `HasStrictFDerivAt.congr_fderiv`, but the calculus API route with `HasStrictFDerivAt.mul`, `HasStrictFDerivAt.fun_sum`, `hasStrictFDerivAt_pi`, and `.hasFDerivAt.fderiv` is much less painful. The dependent-Fin casts stay confined to the single `prodAuxEntryDeriv` induction, using the same `e1/e2` pattern already working in your existence lemma.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:3:product `prodAux` is continuous in its parameter argument. I've failed 3 times on the cast in the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:14:def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:20:      refine (prodAux H A k hk') * ?_
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:30:theorem continuous_prodAux (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:31:    Continuous (fun A : Params H => prodAux H A k hk) := by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:36:1. Per-entry via `continuous_matrix` + `show (prodAux H A k hk' * _) i j = _; rw [Matrix.mul_apply]`:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:37:   the `show` fails — "Function expected at `prodAux H A k hk' * ?m` but this term has type `?m`"
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:38:   (the `prodAux (k+1)` body does NOT syntactically reduce to a `*` because of the `rw [e1,e2]` cast).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:39:2. Whole-matrix `hfun : (fun A => prodAux (k+1)) = fun A => (prodAux k) * (cast layer)` then
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:48:So: `hfun` via `rfl` (whole-matrix `= (prodAux k) * (e1 ▸ e2 ▸ A ⟨k,hkL⟩)`) is the right shape and
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:69:no cast appears; or restructuring `continuous_prodAux` to avoid the cast entirely (e.g. generalize the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:70:column index, or prove `Continuous (fun A => prodAux H A k hk i j)` per-entry by first `rw`-normalizing
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:71:the `prodAux (k+1)` definitional equation via its auto-generated equation lemma `prodAux.eq_def` /
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:72:`prodAux_succ`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g151-prodaux-continuity-prompt.md:78:2. A COMPLETE Lean proof of `continuous_prodAux` that compiles at v4.29 — the full `by` block,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:17:- alignment cancel: at gauge-zero slice, readX(r0,0) s = 0 unless s=firstLayer (then = r0 at X-pivot coord); readZ similarly s=firstLayer; readY s=lastLayer. So the framed layer C_s(r0) = reindex(fromBlocks (1+X_s) Y_s Z_s 0) is CONSTANT (= corner = reindex(fromBlocks 1 0 0 0)) for every INTERIOR layer s ∉ {firstLayer,lastLayer}; only C_first and C_last vary with r0.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:18:- prodAux_framedParamsReg_zero_aux: at r0=0, prodAux k = corner (reindexed) for 1≤k≤L.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:19:- corner_reindex_mul: corner*corner=corner.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:22:TARGET: HasStrictFDerivAt (fun r0 => (P.toBlocks11 - 1) a b) (proj idx_X) 0 where P = reindex(prod(framedParamsReg(r0,0))), idx_X = regPivotFinEquiv.symm (inl(a,b)); plus the toBlocks12→Y_last and toBlocks21→Z_first analogues.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:25:(I) Define explicit `prodAuxEntryDeriv` (recursive Leibniz value) mirroring the existence proof, prove its strict-deriv, THEN prove by induction `prodAuxEntryDeriv (framedParamsReg·) 0 = the corner-sandwich Σ_s prefix·δC_s·suffix`, then read blocks. Concern: the corner-collapse induction is itself heavy + dependent-Fin casts.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:26:(II) EXPLOIT interiors-constant: rewrite prod = (prefix corners)·C_first·(mid corners)·C_last·(suffix corners) so only ≤2 factors vary, differentiate THAT. Concern: the rewrite of prodAux into this factored form has its own cast pain, and firstLayer/lastLayer positions (0 and L-1) interact with the prodAux fold direction.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:27:(III) Per-ENTRY directly: the coordinate function r0 ↦ (P11-1) a b. Since interiors constant and the corner kills cross terms, claim this entry function equals EXACTLY a single affine coordinate r0 ↦ r0 idx_X (NO higher-order terms, because the surviving sandwich corner·δ·corner is degree-1 and the higher-order product terms vanish on the corner blocks). If TRUE, the entry function is literally LINEAR (= r0 idx_X + const), and HasStrictFDerivAt is trivial via HasStrictFDerivAt of a coordinate projection + congr. IS the entry EXACTLY affine in r0 (not just to first order)? Consider L=2: P = C_0(r0)·C_1(r0), both vary (first=0,last=1). (P11) = (1+X_0)(1+X_1)_block... = block11 of product. X_0 routes the X-pivot, Y_1 the Y-pivot, etc. Is (C_0·C_1).toBlocks11 - 1 EXACTLY linear in r0? Compute: C_0=[[1+X0,Y0],[Z0,0]] but Y0=0 (Y only at last=1), Z0=routed. C_1=[[1+X1,Y1],[Z1,0]] but X1: X routes to first=0 only, so X1=0; Z1: Z to first only, so Z1=0; Y1=routed. So C_0=[[1+X0,0],[Z0,0]], C_1=[[1,Y1],[0,0]]. Product block11 = (1+X0)*1 + 0*0 = 1+X0. So P11-1 = X0 = r0 at X-pivot. EXACTLY linear! block12 = (1+X0)Y1 = Y1 + X0Y1 — NOT linear (X0Y1 cross term)! 
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:31:So the real task per block: entry = (linear in r0) + (genuinely higher order vanishing at 0). The linear part is the surviving corner-sandwich. QUESTION: given this explicit small structure (each entry = explicit polynomial: block11=X0(+products that vanish), block12=Y_last+cross, block21=Z_first+cross), what's the LEANEST Lean route? Is there a way to write each entry function as `coordinate + remainder` and use HasStrictFDerivAt.add where remainder has deriv 0 (via it being a product of two functions each 0 at 0, hasStrictFDerivAt of f*g at 0 with f0=0,g0=0 gives deriv 0)? Specifically for general L: the product of L corner-or-varying factors — the entry is multilinear-ish. Recommend the cleanest GENERAL-L route and give the key lemma statements + Mathlib v4.29 deriv API (HasStrictFDerivAt.mul, .add, mul_zero deriv tricks). Keep dependent-Fin casts minimal.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md:39:/bin/bash -lc 'rg -n "prodAux|framedParamsReg|readX|readY|readZ|corner_reindex_mul|prodAuxEntryDeriv|HasStrictFDerivAt" -S .' in /home/ubuntu/workspace/deriv-spec
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g175-hgne-bridge-answer.md:13:4. **BIGGEST RISK:** dependent-index splitting/casts for “prefix product times last layer,” not measure theory. Cheapest mitigation: prove the null theorem on an explicit split product type using `MeasurableEquiv.piFinSuccAbove`, keep algebraic statements close to `prodAux`, and use `Matrix.mulLeftLinearMap` instead of defining a custom linear map.
./expeditions/2026-06-18-voigt-discharge/threads/18-geom-route-general/codex/route-stdout.log:1826:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:60:    HasStrictFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x :=
./expeditions/2026-06-18-voigt-discharge/threads/18-geom-route-general/codex/route-stdout.log:1833:lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:117:    HasStrictFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
./expeditions/2026-06-18-voigt-discharge/threads/18-geom-route-general/codex/route-stdout.log:1992:lean/.lake/packages/mathlib/Mathlib/Analysis/Complex/RealDeriv.lean:38:    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
./expeditions/2026-06-18-voigt-discharge/threads/18-geom-route-general/codex/route-stdout.log:1994:lean/.lake/packages/mathlib/Mathlib/Analysis/Complex/RealDeriv.lean:75:    HasStrictFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by

codex
I found the relevant Lean files and also a prior codex design note for this exact corner-derivative route. I’m going to cross-check that against the current `DeepestRegSliceFderiv` state and Mathlib’s actual derivative lemmas before giving a route.
exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '1,380p' lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderiv` — the #82 PIN1 reg-slice derivative (#156/#157)

The single analytic obligation of the deepest-gauge `_deriv`: the regular-slice
`r0 ↦ deepestEPivot (r0, 0)` has strict derivative `id` at `0`. This file supplies the value-fold
(#156, `framedProd_regSlice_fderiv`) and the assembly (#157, `deepestEPivot_regSlice_fderiv_id`),
proving the `sorry` carried in `DeepestGaugeConstruction`.

## The geometry (post #120 def-change)

`regResidualPack := regPivotFinEquiv`, and `regGaugeIdxSplit`'s reg-half routes via
`regBoundaryToRegGauge ∘ regPivotFinEquiv` (`regBoundaryEmbed`). So the two SHARE `regPivotFinEquiv`,
and the gauge-zero reg-slice cancels by `Equiv.symm_apply_apply`:

- **Alignment** (`regGaugeSlotEquiv_regSlice_boundary`): at the gauge-zero slice, the slot read of a
  routed boundary index `regBoundaryToRegGauge b` returns `r0 (regPivotFinEquiv.symm b)`.
- **Off-image vanishing** (`regGaugeSlotEquiv_regSlice_zero_of_notMem`): a non-routed index reads `0`
  (the gauge half is held at `0`). Hence `readX/readY/readZ (r0,0) s` are nonzero ONLY at the routed
  layer (X,Z at `firstLayer`; Y at `lastLayer`), so all INTERIOR layers are the constant corner.
- **Product collapse** (`framedProd_regSlice_fderiv`): the only varying factors are `C_first`/`C_last`;
  the idempotent corner sandwich keeps `(0,0)→δX`, `(0,1)→δY_last`, `(1,0)→δZ_first`, `(1,1)→0`.
-/

open Matrix
open scoped BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The index-level alignment cancel (the shared `regPivotFinEquiv`) -/

/-- The reg-half of `regGaugeIdxSplit` inverts the boundary routing: `regGaugeIdxSplit.symm (inl k)`
is the routed boundary index `regBoundaryToRegGauge (regPivotFinEquiv k)`. -/
theorem regGaugeIdxSplit_symm_inl (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (k : Fin (deepestNReg H r)) :
    (regGaugeIdxSplit H r hr hL).symm (Sum.inl k)
      = regBoundaryToRegGauge H r hL (regPivotFinEquiv H r hr k) := by
  classical
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) := Fintype.ofFinite _
  unfold regGaugeIdxSplit
  simp only [Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.symm_symm, Equiv.sumCongr_apply,
    Sum.map_inl]
  rw [Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]
  rfl

/-- The forward boundary cancel: `regGaugeIdxSplit (regBoundaryToRegGauge b) = inl (pivot.symm b)`. -/
theorem regGaugeIdxSplit_boundary_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (b : BoundaryPivotIdx H r) :
    regGaugeIdxSplit H r hr hL (regBoundaryToRegGauge H r hL b)
      = Sum.inl ((regPivotFinEquiv H r hr).symm b) := by
  rw [← Equiv.apply_symm_apply (regPivotFinEquiv H r hr) b, Equiv.symm_apply_apply,
    ← regGaugeIdxSplit_symm_inl H r hr hL ((regPivotFinEquiv H r hr).symm b), Equiv.apply_symm_apply]

/-! ## The slot read on the regular slice -/

/-- The gauge-zero slot read in terms of the index split: `regGaugeSlotEquiv (r0,0) idx` is the joined
function `(r0, 0)` evaluated at `regGaugeIdxSplit idx`. -/
theorem regGaugeSlotEquiv_regSlice_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) (idx : RegGaugeIdx H r) :
    regGaugeSlotEquiv H r hr hL (r0, 0) idx
      = (Equiv.sumPiEquivProdPi (fun _ => ℝ)).symm (r0, 0) (regGaugeIdxSplit H r hr hL idx) := by
  unfold regGaugeSlotEquiv
  change (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm
      ((Homeomorph.sumPiEquivProdPi (Fin (deepestNReg H r)) (Fin (deepestNGauge H r))
        (fun _ => ℝ)).symm (r0, 0)) idx = _
  rw [Homeomorph.piCongrLeft_symm_apply]
  rfl

/-- A routed boundary index reads back the matching reg coordinate `r0 (pivot.symm b)`. -/
theorem regGaugeSlotEquiv_regSlice_boundary (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) (b : BoundaryPivotIdx H r) :
    regGaugeSlotEquiv H r hr hL (r0, 0) (regBoundaryToRegGauge H r hL b)
      = r0 ((regPivotFinEquiv H r hr).symm b) := by
  rw [regGaugeSlotEquiv_regSlice_apply, regGaugeIdxSplit_boundary_apply H r hr hL b]
  rfl

/-- A non-routed index reads `0` (the gauge half is held at `0`). -/
theorem regGaugeSlotEquiv_regSlice_zero_of_notMem (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (r0 : Fin (deepestNReg H r) → ℝ) (idx : RegGaugeIdx H r)
    (h : idx ∉ Set.range (regBoundaryEmbed H r hL)) :
    regGaugeSlotEquiv H r hr hL (r0, 0) idx = 0 := by
  classical
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) := Fintype.ofFinite _
  rw [regGaugeSlotEquiv_regSlice_apply]
  obtain ⟨m, hm⟩ : ∃ m, regGaugeIdxSplit H r hr hL idx = Sum.inr m := by
    unfold regGaugeIdxSplit
    rw [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_notMem h]
    exact ⟨_, rfl⟩
  rw [hm]; rfl

/-- The boundary image is the range of the routing (`regBoundaryEmbed`'s function is the routing). -/
theorem range_regBoundaryEmbed_eq (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    Set.range (regBoundaryEmbed H r hL) = Set.range (regBoundaryToRegGauge H r hL) := rfl

/-! ## Layer membership: X/Z hit only `firstLayer`, Y only `lastLayer` -/

/-- An X-index `⟨s, inl(inl(a,b))⟩` at `s ≠ firstLayer` is not in the boundary image. -/
theorem notMem_X_of_ne_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) (s : Fin L)
    (hs : s ≠ firstLayer hL) (a b : Fin r) :
    (⟨s, Sum.inl (Sum.inl (a, b))⟩ : RegGaugeIdx H r) ∉ Set.range (regBoundaryToRegGauge H r hL) := by
  rintro ⟨b', hb'⟩
  rcases b' with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp only [regBoundaryToRegGauge, Sigma.mk.injEq] at hb'
  · exact hs hb'.1.symm
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm

/-- A Z-index `⟨s, inr(a,b)⟩` at `s ≠ firstLayer` is not in the boundary image. -/
theorem notMem_Z_of_ne_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) (s : Fin L)
    (hs : s ≠ firstLayer hL) (a : Fin (H s.castSucc - r)) (b : Fin r) :
    (⟨s, Sum.inr (a, b)⟩ : RegGaugeIdx H r) ∉ Set.range (regBoundaryToRegGauge H r hL) := by
  rintro ⟨b', hb'⟩
  rcases b' with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp only [regBoundaryToRegGauge, Sigma.mk.injEq] at hb'
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm
  · exact hs hb'.1.symm

/-- A Y-index `⟨s, inl(inr(a,b))⟩` at `s ≠ lastLayer` is not in the boundary image. -/
theorem notMem_Y_of_ne_last (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) (s : Fin L)
    (hs : s ≠ lastLayer hL) (a : Fin r) (b : Fin (H s.succ - r)) :
    (⟨s, Sum.inl (Sum.inr (a, b))⟩ : RegGaugeIdx H r) ∉ Set.range (regBoundaryToRegGauge H r hL) := by
  rintro ⟨b', hb'⟩
  rcases b' with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp only [regBoundaryToRegGauge, Sigma.mk.injEq] at hb'
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm
  · exact hs hb'.1.symm
  · rcases hb' with ⟨hlay, harm⟩; subst hlay; simp at harm

/-! ## The `readX/readY/readZ` slice values -/

/-- `readX (r0,0) (firstLayer) a b` reads back `r0` at the X-pivot coordinate. -/
theorem readX_regSlice_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (a b : Fin r) :
    readX H r hr hL (r0, 0) (firstLayer hL) a b
      = r0 ((regPivotFinEquiv H r hr).symm (Sum.inl (a, b))) := by
  simp only [readX, Matrix.of_apply]
  have : (⟨firstLayer hL, Sum.inl (Sum.inl (a, b))⟩ : RegGaugeIdx H r)
      = regBoundaryToRegGauge H r hL (Sum.inl (a, b)) := rfl
  rw [this, regGaugeSlotEquiv_regSlice_boundary]

/-- `readX (r0,0) s = 0` for `s ≠ firstLayer` (the X-routing hits only `firstLayer`). -/
theorem readX_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (s : Fin L) (hs : s ≠ firstLayer hL) :
    readX H r hr hL (r0, 0) s = 0 := by
  ext a b
  simp only [readX, Matrix.of_apply, Matrix.zero_apply]
  exact regGaugeSlotEquiv_regSlice_zero_of_notMem H r hr hL r0 _
    (by rw [range_regBoundaryEmbed_eq]; exact notMem_X_of_ne_first H r hL s hs a b)

/-- `readZ (r0,0) (firstLayer) a b` reads back `r0` at the Z-pivot coordinate. -/
theorem readZ_regSlice_first (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (a : Fin (H (firstLayer hL).castSucc - r))
    (b : Fin r) :
    readZ H r hr hL (r0, 0) (firstLayer hL) a b
      = r0 ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inr (a, b)))) := by
  simp only [readZ, Matrix.of_apply]
  have : (⟨firstLayer hL, Sum.inr (a, b)⟩ : RegGaugeIdx H r)
      = regBoundaryToRegGauge H r hL (Sum.inr (Sum.inr (a, b))) := rfl
  rw [this, regGaugeSlotEquiv_regSlice_boundary]

/-- `readZ (r0,0) s = 0` for `s ≠ firstLayer`. -/
theorem readZ_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (s : Fin L) (hs : s ≠ firstLayer hL) :
    readZ H r hr hL (r0, 0) s = 0 := by
  ext a b
  simp only [readZ, Matrix.of_apply, Matrix.zero_apply]
  exact regGaugeSlotEquiv_regSlice_zero_of_notMem H r hr hL r0 _
    (by rw [range_regBoundaryEmbed_eq]; exact notMem_Z_of_ne_first H r hL s hs a b)

/-- `readY (r0,0) s = 0` for `s ≠ lastLayer`. -/
theorem readY_regSlice_zero_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ) (s : Fin L) (hs : s ≠ lastLayer hL) :
    readY H r hr hL (r0, 0) s = 0 := by
  ext a b
  simp only [readY, Matrix.of_apply, Matrix.zero_apply]
  exact regGaugeSlotEquiv_regSlice_zero_of_notMem H r hr hL r0 _
    (by rw [range_regBoundaryEmbed_eq]; exact notMem_Y_of_ne_last H r hL s hs a b)

/-! ## The framed-layer values on the regular slice (interiors are the constant corner) -/

/-- An INTERIOR layer (`s ≠ firstLayer`, `s ≠ lastLayer`) of the regular slice is the constant corner
`reindex (fromBlocks 1 0 0 0)` — all of `X_s, Y_s, Z_s` vanish there. -/
theorem framedParamsReg_regSlice_interior (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (r0 : Fin (deepestNReg H r) → ℝ)
    (s : Fin L) (hsf : s ≠ firstLayer hL) (hsl : s ≠ lastLayer hL) :
    framedParamsReg H r hr hL (r0, 0) s
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  simp only [framedParamsReg, framedLayer, readX_regSlice_zero_of_ne H r hr hL r0 s hsf,
    readY_regSlice_zero_of_ne H r hr hL r0 s hsl, readZ_regSlice_zero_of_ne H r hr hL r0 s hsf,
    add_zero]

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '1,380p' lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '1,180p' lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 138ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited analytic bound.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the `rlct ≤ ½·codim` direction is **Cited**
  (Aoyagi / Watanabe).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.

 succeeded in 105ms:
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct` — the gauge-sliced framed product `∏C` (#44c)

The shared concrete object both PIN 1 (`Ereg`, the regular residual) and PIN 2 (`loss_squeeze`, the
frame bridge) consume: the **framed product** `∏C_s`, where each layer
`C_s = fromBlocks (1 + X_s) Y_s Z_s T_s` is the gauge-sliced normal-form deviation (the `block_elimination`
frame puts `w0` at `blockdiag[I_r,0]`; the deviation reads the gauge blocks `(X_s, Y_s, Z_s)` off the
reg+spec slots via `gaugeSlotRead`/`regGaugeSlotEquiv` and the reduced `T_s` off the core slot).

Per the #92 producer contract: `∏C` is the CLEAN product of the per-layer normal forms (the interior
`block_elimination` frames are trivial — #77 (iii), interior layers already block-normal — so the
per-layer framing telescopes; only the two boundary frames carry units, absorbed by the endpoint
conjugation `conjugation_frobenius_comparable`). The framed product is `prod H C` for the reconstructed
gauge-sliced tuple `C : Params H` — no new fold; `prod`/`prodAux` are reused.

## Status

SCAFFOLD (decision-independent piece): the per-layer framed reconstruction `framedLayer`
(`fromBlocks` reindexed to a `Params H` layer via `rThresholdSplit`) + the framed tuple `framedParams`.
The `∏C` residual (`Ereg`) extraction + the `dlnLoss = ‖∏C − D‖²` bridge are the coupled pieces
(gated on the #77 (iii) decl-confirm + the `Ereg = E_pivot` (B)-ruling); built once confirmed.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## `ContDiff` of the gauge read (the `regGaugeSlotEquiv` linearity, for `_contdiff`)

`regGaugeSlotEquiv` (crux2 #78) is packaged as a `Homeomorph` (coordinate relabels), so its linearity is
not exposed — but the SAME relabels have `ContinuousLinearEquiv` forms in Mathlib v4.29
(`ContinuousLinearEquiv.{sumPiEquivProdPi, piCongrLeft}`), whose underlying `Homeomorph` IS the one
`regGaugeSlotEquiv` uses (`__ := Homeomorph.…`). So a CLE mirror `regGaugeSlotCLE` coerces to the SAME
function (defeq), giving `ContDiff` of `regGaugeSlotEquiv` (hence of the `readX/Y/Z` entries) via
`ContinuousLinearEquiv.contDiff`. This is a fact ABOUT crux2's def, not a change to it. -/

/-- The `ContinuousLinearEquiv` mirror of `regGaugeSlotEquiv` (same underlying Homeomorph/function). -/
noncomputable def regGaugeSlotCLE (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ≃L[ℝ] (RegGaugeIdx H r → ℝ) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin (deepestNReg H r)) (Fin (deepestNGauge H r))
      (fun _ => ℝ)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm

/-- `regGaugeSlotCLE` and `regGaugeSlotEquiv` coerce to the SAME function (the CLE and Homeomorph share
the underlying relabel). -/
theorem regGaugeSlotCLE_coe (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (regGaugeSlotCLE H r hr hL : _ → _) = regGaugeSlotEquiv H r hr hL := rfl

/-- The gauge read `regGaugeSlotEquiv` is `ContDiff ⊤` (it is the CLE `regGaugeSlotCLE`). -/
theorem contDiff_regGaugeSlotEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => regGaugeSlotEquiv H r hr hL p) := by
  rw [← regGaugeSlotCLE_coe H r hr hL]
  exact (regGaugeSlotCLE H r hr hL).contDiff

/-- Each `readX` entry is `ContDiff ⊤` (a coordinate of the `ContDiff` gauge read). -/
theorem contDiff_readX_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readX H r hr hL p s i j) := by
  simp only [readX, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- Each `readY` entry is `ContDiff ⊤`. -/
theorem contDiff_readY_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i : Fin r)
    (j : Fin (H s.succ - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readY H r hr hL p s i j) := by
  simp only [readY, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- Each `readZ` entry is `ContDiff ⊤`. -/
theorem contDiff_readZ_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i : Fin (H s.castSucc - r))
    (j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readZ H r hr hL p s i j) := by
  simp only [readZ, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- **The per-layer framed normal-form matrix** `C_s = fromBlocks (1 + X_s) Y_s Z_s T_s`, reindexed
from the block split `Fin r ⊕ Fin (H_s − r)` to the layer dimension `Fin (H_s)` (via `rThresholdSplit`),
so it types as a `Params H` layer `Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`. The gauge blocks
`(X_s, Y_s, Z_s)` are the regular/spectator gauge entries (off `gaugeSlotRead`); `T_s` is the reduced
core block. -/
noncomputable def framedLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : Fin L)
    (X : Matrix (Fin r) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin (H s.succ - r)) ℝ)
    (Z : Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
    (T : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ) :
    Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ :=
  Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
    (rThresholdSplit r (H s.succ) (hr s.succ)).symm
    (Matrix.fromBlocks (1 + X) Y Z T)

/-- **The framed parameter tuple** `C : Params H` reconstructed from a `DeepestSplit` point: each layer
is `framedLayer` of the gauge blocks `(X_s, Y_s, Z_s)` (read off the reg+spectator slot via
`readX/readY/readZ`) and the reduced core `T_s` (read off the core slot via `paramsEquivFlat (deepestM)`).
The framed product `∏C = prod H (framedParams q)` is the shared object; `dlnLoss = ‖∏A − B‖²` relates to
`‖∏C − D‖²` through the endpoint conjugation (the #77 (iii) telescoping). Decision-independent (the
product `∏C` is well-defined regardless of (iii)/(B); those affect how it relates to `dlnLoss`/`Ereg`). -/
noncomputable def framedParams (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : Params H :=
  fun s =>
    framedLayer H r hr s
      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
      (readZ H r hr hL (q.1, q.2.2) s)
      ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)

/-- **The `T = 0` framed reconstruction** (the `deepestEPivot` reconstruction half). Reconstructs the
gauge-sliced layer tuple from the `(reg, gauge)` slots ALONE, with the reduced core block `T_s := 0`
(the core is `coreAbsorb`'s domain — `deepestEPivot` is the regular residual of `∏C|_{T=0}`, the
core-INDEPENDENT pivot part, per the #115/g222 cert). Each layer is `framedLayer` of the read blocks
`(X_s, Y_s, Z_s)` with the `(1,1)` block zeroed. Layout-independent: it does not depend on the final
`Fin nReg` pack convention (the open obstruction), only on the gauge read `readX/Y/Z`. -/
noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) : Params H :=
  fun s =>
    framedLayer H r hr s
      (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
      (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)

/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
`framedLayer 0 0 0 0 = reindex (fromBlocks 1 0 0 0)` (the deepest value `blockdiag[I_r, 0]`). The base
fact for `deepestEPivot`'s `_base` (the residual of `∏ blockdiag[I_r,0]` is `0`). -/
theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    framedParamsReg H r hr hL 0 s
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
    readZ_zero H r hr hL s, add_zero]

/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
`fromBlocks (1+X) Y Z 0` block entry (reindexed), i.e. `1+readX` / `readY` / `readZ` / `0`, each
`ContDiff` (the read entries + `const`). The `_contdiff` layer input to `contDiff_prod_entry`. -/
theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s i j) := by
  -- The entry is `(fromBlocks (1+X) Y Z 0) (e₁.symm i) (e₂.symm j)`; case-split on the sum indices.
  have hentry : (fun p => framedParamsReg H r hr hL p s i j)
      = fun p => Matrix.fromBlocks (1 + readX H r hr hL p s) (readY H r hr hL p s)
          (readZ H r hr hL p s) (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)
          ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)) i)
          ((rThresholdSplit r (H s.succ) (hr s.succ)) j) := by
    funext p
    simp only [framedParamsReg, framedLayer, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
  rw [hentry]
  rcases (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) i with a | a <;>
    rcases (rThresholdSplit r (H s.succ) (hr s.succ)) j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply, Matrix.zero_apply]
  · -- (1 + X) entry: `(if a = b then 1 else 0) + readX … a b` — the `if` is a constant in `p`.
    exact contDiff_const.add (contDiff_readX_entry H r hr hL s a b)
  · exact contDiff_readY_entry H r hr hL s a b
  · exact contDiff_readZ_entry H r hr hL s a b
  · exact contDiff_const

/-! ## PIN 2 frame bridge — the telescoping (#80, next chunk)

The geometric bridge `dlnLoss H B (paramsSymm w) ≍ ‖∏(framed C) − D‖²` reduces to: the **endpoint-frame
telescoping** `prod H A = P_0⁻¹ · (prod H C) · Q_{L-1}⁻¹` (under #95-(I): interior frames `= I` via
`deepestPoint_interior_eq_corM`, boundary-inner `= I` via `deepestPoint_layer{0,Last}_*_vanish`, so the
interior interfaces `Q_s⁻¹·P_{s+1}⁻¹ = 1` collapse) → `conjugation_frobenius_comparable` (the endpoint
conjugation, banked) → `fullProduct_loss_squeeze` (the block split, banked) + the gauge-read identities.

**The statement SHAPE is solved** (the cast obstacle): state it with EXISTENTIAL endpoints —
`∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
IsUnit P0 ∧ IsUnit QL ∧ prod H C = P0 * prod H A * QL`, with hypotheses: per-layer frames
`P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ`, `Q : … (Fin (H s.succ)) …`,
`hframe : ∀ s, C s = P s * A s * Q s`, `hunit : ∀ s, IsUnit (P s) ∧ IsUnit (Q s)`, and the
INTERFACE-VANISHING conditions `Q s * P s' = 1` for adjacent `s + 1 = s'` (the #95-(I) frame-triviality
makes the interfaces `I`). Existential `P0, QL` are naturally typed where `prod` lives (`H 0`, `H (last)`)
— this DODGES the `H 0` vs `H ⟨0,_⟩.castSucc` cast that breaks an explicit-endpoint statement (probed,
typechecks). The PROOF is the cast-heavy `prodAux` induction: invariant `prodAux H C k = P0 *
prodAux H A k * (frame at k)`, interior interfaces cancelling by the `Q s * P s' = 1` conditions. The
endpoint conjugation + block split are banked (`conjugation_frobenius_comparable`,
`fullProduct_loss_squeeze`); only this induction remains for PIN 2's bridge. -/

/-! ## `ContDiff` of the layer product (the `deepestEPivot._contdiff` infrastructure)

`deepestEPivot` is `pack ∘ residual ∘ reindex ∘ prod ∘ framedParamsReg`; its `ContDiff ⊤` reduces to
`ContDiff ⊤ (fun x => prod H (g x))` for `g = framedParamsReg` (each layer affine in the slots, so
`ContDiff`). The product is the dependent-Fin `prodAux` fold — `ContDiff` ENTRY-WISE (matrix = nested
`Pi`; `contDiff_pi'` twice), mirroring the green `continuous_prodAux`: base `prodAux 0 = 1` const, step
`(prodAux k * layer) i j = ∑ m, prodAux k i m · layer m j` (`ContDiff.sum` of `ContDiff.mul`). No
`ContDiff.matrix_mul` lemma exists in v4.29 — the entry-wise route sidesteps it. -/

/-- **`ContDiff` of the partial-product ENTRIES** under a smooth reconstruction `g : X → Params H`
(each layer ENTRY `ContDiff ⊤`). Entry-wise to dodge the matrix-norm-instance friction (`Matrix` has
no canonical `NormedSpace` — `ContDiff` of a matrix-VALUED map needs an opt-in norm; the entries are
plain ℝ-valued). Induction on `k`, mirroring `continuous_prodAux`: the matrix-mul step is
`(prodAux k * layer) i j = ∑ m, prodAux k i m · layer m j` (`ContDiff.sum` of `ContDiff.mul`). -/
theorem contDiff_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g x s i j))
    (k : ℕ) (hk : k < L + 1) :
    ∀ (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => prodAux H (g x) k hk i j) := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      -- `prodAux 0 = 1`; each entry is `0` or `1`, constant.
      have : (fun x => prodAux H (g x) 0 hk i j)
          = fun _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j := rfl
      rw [this]; exact contDiff_const
  | succ k ih =>
      intro hk i j
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- `prodAux (k+1) i j = ∑ m, prodAux k i m · (cast layer k) m j`.
      have hentry : (fun x => prodAux H (g x) (k + 1) hk i j)
          = fun x => ∑ m, prodAux H (g x) k hk' i m
              * ((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) := by
        funext x; rfl
      rw [hentry]
      refine ContDiff.sum (fun m _ => ?_)
      refine (ih hk' i m).mul ?_
      -- The cast `⟨k,hk'⟩ = ⟨k,hkL⟩.castSucc` is `Fin.mk` proof-irrelevance (defeq), so the cast layer
      -- entry IS `g x ⟨k,hkL⟩ m j` up to the `eq_mpr/cast` normal form; `ContDiff` by `hg`.
      have := hg ⟨k, hkL⟩
      simp only [e1, e2, eq_mpr_eq_cast, cast_eq] at this ⊢
      exact this _ _

/-- **`ContDiff` of the full layer-product entries** (`contDiff_prodAux_entry` at `k = L`). -/
theorem contDiff_prod_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g x s i j))
    (i : Fin (H 0)) (j : Fin (H (Fin.last L))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => prod H (g x) i j) :=
  contDiff_prodAux_entry H g hg L (Nat.lt_succ_self L) i j

/-- **`HasStrictFDerivAt` of the partial-product ENTRIES** (the `_deriv` infrastructure, entry-wise to
dodge the matrix-norm instance, mirroring `contDiff_prodAux_entry`). If each layer ENTRY has a strict
derivative `g' s i j` at `x`, then each `prodAux` entry has the LEIBNIZ strict derivative
`∑ m, (prodAux k i m) · (layer deriv) + (prodAux k deriv) · (layer i m)` — built by `HasStrictFDerivAt.sum`
of `HasStrictFDerivAt.mul`. The derivative VALUE is the sum-of-products `prodAux'`; the deepest-point
specialization (idempotent sandwich, #91) collapses it to the `(Σ X_s, Y_L, Z_1)` shear. -/
theorem hasStrictFDerivAt_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)), X →L[ℝ] ℝ)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (k : ℕ) (hk : k < L + 1) :
    ∀ (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)),
      ∃ D : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j) D x := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      -- `prodAux 0 = 1`; each entry is constant, derivative `0`.
      refine ⟨0, ?_⟩
      have : (fun y => prodAux H (g y) 0 hk i j)
          = fun _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j := rfl
      rw [this]; exact hasStrictFDerivAt_const _ _
  | succ k ih =>
      intro hk i j
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- `prodAux (k+1) i j = ∑ m, prodAux k i m · (cast layer k) m j`.
      have hentry : (fun y => prodAux H (g y) (k + 1) hk i j)
          = fun y => ∑ m, prodAux H (g y) k hk' i m
              * ((by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) := by
        funext y; rfl
      rw [hentry]
      -- Each summand `prodAux k i m * (cast layer) m j` has a strict derivative (product rule).
      -- `HasStrictFDerivAt.sum` over `m`; each summand via `HasStrictFDerivAt.mul` of (ih) and (the
      -- cast-normalised layer entry, `simp [e1,e2,eq_mpr_eq_cast,cast_eq]` to `g · ⟨k,hkL⟩`, then `hg`).
      have hsummand : ∀ m : Fin (H ⟨k, hk'⟩), ∃ D : X →L[ℝ] ℝ,
          HasStrictFDerivAt (fun y => prodAux H (g y) k hk' i m
              * ((by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j)) D x := by
        intro m
        obtain ⟨Dpre, hDpre⟩ := ih hk' i m
        have hlayer : HasStrictFDerivAt
            (fun y => (by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j)
            (g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)) x := by
          have := hg ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
          simp only [eq_mpr_eq_cast, cast_eq] at this ⊢
          exact this
        exact ⟨_, hDpre.mul hlayer⟩
      choose D hD using hsummand
      exact ⟨∑ m, D m, HasStrictFDerivAt.fun_sum (fun m _ => hD m)⟩

/-- **`HasStrictFDerivAt` of the full layer-product entries** (`hasStrictFDerivAt_prodAux_entry` at
`k = L`): each entry of `fun y => prod H (g y) i j` has a strict derivative at `x`, given each layer
entry does. The `_deriv` input — `deepestEPivot` is a constant-linear post-composition of these. -/
theorem hasStrictFDerivAt_prod_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)), X →L[ℝ] ℝ)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (i : Fin (H 0)) (j : Fin (H (Fin.last L))) :
    ∃ D : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => prod H (g y) i j) D x :=
  hasStrictFDerivAt_prodAux_entry H g x g' hg L (Nat.lt_succ_self L) i j

end DLNFibre.DLN.RLCT

 succeeded in 260ms:
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Constructions

/-!
# `DLNFibre.DLN.RLCT.Foundations.Loss` — the deep-linear-network loss

The parameter space `Params H` of composable real matrix tuples, the multiplication map `prod`,
the square-Frobenius loss `dlnLoss`, and the fibre `optimalSet = mult⁻¹(B)`.

Pure polynomial layer (no measure theory). Faithful to Aoyagi 2023, §0–1 (design-spec §0–1):
the `L`-layer model `Y = (∏_{s=1}^L A⁽ˢ⁾) X + noise`, widths `H : Fin (L+1) → ℕ` with `H⁽¹⁾ = H 0`
the **output** dimension and `H⁽ᴸ⁺¹⁾ = H (last)` the **input** dimension, layer `s` a matrix of size
`H⁽ˢ⁾ × H⁽ˢ⁺¹⁾`. The identity-covariance square-Frobenius loss is RLCT-faithful (`Σ_X` drops out by
the regular whitening change of coordinates; design-spec §0).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-- A network parameter: a composable tuple of layer matrices, layer `s` of size
`H⁽ˢ⁾ × H⁽ˢ⁺¹⁾ = H s.castSucc × H s.succ`. Definitionally a function space (a `Pi` of `Pi`s),
so it inherits `TopologicalSpace`/`MeasurableSpace`/`MeasureSpace` by `inferInstanceAs`. -/
def Params (H : Fin (L + 1) → ℕ) : Type :=
  ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ

/-- The product of the first `k` layer matrices `A⁽¹⁾·…·A⁽ᵏ⁾`, of size `H 0 × H k`. -/
def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
    (k : ℕ) → (hk : k < L + 1) → Matrix (Fin (H 0)) (Fin (H ⟨k, hk⟩)) ℝ
  | 0, _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
  | k + 1, hk => by
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      refine (prodAux H A k hk') * ?_
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      rw [e1, e2]; exact A ⟨k, hkL⟩

/-- The multiplication map: the layer product `A⁽¹⁾·A⁽²⁾·…·A⁽ᴸ⁾`, of size
`H⁽¹⁾ × H⁽ᴸ⁺¹⁾ = H 0 × H (last)`. -/
def prod (H : Fin (L + 1) → ℕ) (A : Params H) :
    Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
  prodAux H A L (Nat.lt_succ_self L)

/-- The square-Frobenius loss `‖prod A − B‖²_F = ∑ᵢⱼ ((prod A − B)ᵢⱼ)²`. An honest polynomial in the
entries of `A`, hence real-analytic. Faithful to Aoyagi's Kullback function `K(w)` for the Gaussian
model (design-spec §1). -/
def dlnLoss (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (A : Params H) : ℝ :=
  ∑ i, ∑ j, ((prod H A - B) i j) ^ 2

/-- The fibre `mult⁻¹(B) = {A | prod A = B}`, the zero-set of `dlnLoss B` (a sum of squares). -/
def optimalSet (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) : Set (Params H) :=
  { A | prod H A = B }

/-- `optimalSet` is exactly the zero-set of `dlnLoss B`: the loss is a sum of squares, zero iff
`prod A = B`. -/
theorem optimalSet_eq_loss_zero (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) :
    optimalSet H B = { A | dlnLoss H B A = 0 } := by
  ext A
  simp only [optimalSet, dlnLoss, Set.mem_setOf_eq]
  constructor
  · intro h; simp [h]
  · intro h
    -- a finite sum of squares is zero iff each square is zero
    have hsq : ∀ i, ∀ j, ((prod H A - B) i j) ^ 2 = 0 := by
      have hnn : ∀ i, (0 : ℝ) ≤ ∑ j, ((prod H A - B) i j) ^ 2 := fun i =>
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hi : ∀ i, ∑ j, ((prod H A - B) i j) ^ 2 = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h i (Finset.mem_univ i)
      intro i j
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 (hi i) j (Finset.mem_univ j)
    funext i j
    have hij : (prod H A - B) i j = 0 := by
      have := hsq i j; nlinarith [this]
    have := sub_eq_zero.1 (by simpa [Matrix.sub_apply] using hij)
    simpa using this

/-- **`dlnLoss` is nonnegative.** A sum of squares: `0 ≤ dlnLoss H B A`. Reusable bedrock — needed
for the sqrt-wrapper `Real.sqrt (dlnLoss …) ^ 2 = dlnLoss …` that feeds `rlct_additive_smooth_block`
(the smooth-block split), and for the homogeneous-core work. -/
theorem dlnLoss_nonneg (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (A : Params H) :
    0 ≤ dlnLoss H B A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end DLNFibre.DLN.RLCT

codex
The current slice file has the alignment and interior-constant lemmas, but it stops before any product derivative collapse. The product derivative infrastructure in `DeepestFramedProduct` is still existential, so the design choice is whether to make that derivative value explicit or avoid it.
exec
/bin/bash -lc "sed -n '380,760p' lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 105ms:
exec
/bin/bash -lc "sed -n '1,260p' lean/CLAUDE.md" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '1,260p' lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '1,320p' lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 118ms:
import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks` — gauge-slice → Schur block algebra (#44c sub-1)

The **route-independent** matrix-algebra core of `deepest_gauge_chart_exists` (sub-lemma 1,
controller 2026-06-22). Banks regardless of the L2 transport wrapper (squeeze vs chart): the
geometric content that `deepest_gauge_chart_exists` produces and any transport consumes.

## The obligation (g150/g153 cert, refined)

At a rank-`r`-exact deepest point, each layer gauge-slices to `C_s = [[I+X_s, Y_s],[Z_s, T_s]]`. The
loss is `‖∏C_s − D‖²` with `D = blockdiag[I, 0]` (the deepest product value). Block-summing the
Frobenius norm: `loss = ∑(E²) + ‖P11‖²`, `E` = the regular residuals on the `(0,0),(0,1),(1,0)`
blocks, `P11` = the `(1,1)` block of `∏C`.

**The raw-`∏T` core is INSUFFICIENT** (g153, Codex CE verified): `C1C2C3 = blockdiag[1, −ε⁴]` has
`∑E²=0`, raw `∏T = 0` (interior `T2=0`), but `P11 = −ε⁴` — so `‖P11‖² = ε⁸ ≠ 0 = ‖∏T‖²`. A zero
INTERIOR reduced block produces a nonzero `P11` via gauge interactions invisible to `E`. So the
reduced core MUST be the **Schur complement** `R = P11 − P10·Ainv·P01` (`A = P00 ≈ I` near `w0`),
the gauge-normalized chain — NOT the raw `∏T`.

## The reusable bedrock (from `GeneralR1Recursion`)

The abstract squeeze is already PROVEN there and reused here:
- `hardPivot_schur_blockId` — `L·(fromBlocks 1 b c D)·R = fromBlocks 1 0 0 (D−c·b)` (transvection).
- `schur_row_decomp` — `b·β + D·Γ = b·(1·β + a·Γ) + (D − b·a)·Γ` (the row decomposition).
- `schur_lossDiff_eq_cofactor` — `∑(bErow+SΓ)² − ∑(SΓ)² = ∑ bErow·(bErow+2SΓ)` (loss-diff ∈ ideal).
- `schur_node_squeeze_unif` — the two-sided squeeze, explicit `c₁ = (2(1+T²))⁻¹`, `c₂ = 2+2T²`.

The genuine #44c work here is the **L2 geometric presentation**: the 2-factor gauge-sliced product
in Schur block form, matched to the `schur_*` shape (`Erow` = regular residual row, `b` = pivot
column `→ 0` at `w0`, `S·Γ` = the reduced chain).

## Status

ROUTE-INDEPENDENT bedrock (sub-1): the 2-factor block product + the Schur `(1,1)` split, GREEN. The
`L`-fold + the gauge-slice presentation are the next layers; the wrapper is controller-wired.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The 2-factor block product** (`g150_gauge_chart` cert). For two gauge-sliced rank-`r` layers
`C₁ = fromBlocks (I+X₁) Y₁ Z₁ T₁`, `C₂ = fromBlocks (I+X₂) Y₂ Z₂ T₂`, the product `C₁·C₂` has blocks
`(0,0) = (I+X₁)(I+X₂)+Y₁Z₂`, `(0,1) = (I+X₁)Y₂+Y₁T₂`, `(1,0) = Z₁(I+X₂)+T₁Z₂`, `(1,1) = Z₁Y₂+T₁T₂`.
Pure `CommRing` block algebra (`fromBlocks_multiply`). -/
theorem twofactor_block_product {r m₁ m₂ m₃ : Type*} [Fintype r] [DecidableEq r]
    [Fintype m₂] {R : Type*} [CommRing R]
    (X₁ : Matrix r r R) (Y₁ : Matrix r m₂ R) (Z₁ : Matrix m₁ r R) (T₁ : Matrix m₁ m₂ R)
    (X₂ : Matrix r r R) (Y₂ : Matrix r m₃ R) (Z₂ : Matrix m₂ r R) (T₂ : Matrix m₂ m₃ R) :
    (Matrix.fromBlocks (1 + X₁) Y₁ Z₁ T₁) * (Matrix.fromBlocks (1 + X₂) Y₂ Z₂ T₂)
      = Matrix.fromBlocks
          ((1 + X₁) * (1 + X₂) + Y₁ * Z₂) ((1 + X₁) * Y₂ + Y₁ * T₂)
          (Z₁ * (1 + X₂) + T₁ * Z₂) (Z₁ * Y₂ + T₁ * T₂) := by
  rw [Matrix.fromBlocks_multiply]

/-- **`blockdiag[I_r, 0]` is corner-idempotent**: `blockdiag · blockdiag = blockdiag`
(`fromBlocks_multiply`: the `(0,0)` corner is `1·1 = 1`, all other blocks have a `0` factor). The
step-fact of the deepest-product idempotent fold (the `_base` value-fold's `prodAux` induction — the
product of `reindex(blockdiag)` layers stays `reindex(blockdiag)`). Reusable, cast-free block algebra. -/
theorem fromBlocks_blockdiag_idem {r m₀ m₁ m₂ : Type*} [Fintype r] [DecidableEq r] [Fintype m₁]
    {R : Type*} [CommRing R] :
    ((Matrix.fromBlocks (1 : Matrix r r R) 0 0 0 : Matrix (r ⊕ m₀) (r ⊕ m₁) R)
        * (Matrix.fromBlocks (1 : Matrix r r R) 0 0 0 : Matrix (r ⊕ m₁) (r ⊕ m₂) R))
      = Matrix.fromBlocks (1 : Matrix r r R) 0 0 0 := by
  rw [Matrix.fromBlocks_multiply]; simp

/-- **The Schur split of the 2-factor product's `(1,1)` block** (g150-fix / g153). The lower-right
Schur complement `R := P₁₁ − P₁₀·Ainv·P₀₁` (`Ainv` = the pivot inverse) is the clean reduced core
(the gauge-normalized chain); `P₁₁ = R + P₁₀·Ainv·P₀₁` exhibits the endpoint leak `P₁₁ − R` as a
product of the regular residuals `P₁₀, P₀₁` (`∈ ideal(reg)`). Pure ring algebra. -/
theorem schur_P11_decomp {r mlo nhi : Type*} [Fintype r] {R : Type*} [Ring R]
    (Ainv : Matrix r r R) (P01 : Matrix r nhi R) (P10 : Matrix mlo r R)
    (P11 : Matrix mlo nhi R) :
    P11 = (P11 - P10 * Ainv * P01) + P10 * Ainv * P01 := by
  rw [sub_add_cancel]

/-- **The Frobenius block-sum** (route-independent). The entrywise-summed `f`-weight of a
`fromBlocks` matrix splits into the four block sums (`f = (·²)` gives the squared-Frobenius split).
The block-summing of `dlnLoss = ∑ f((prod − B)ᵢⱼ)` once the gauge-sliced product is in block form:
`loss = ∑E² + ‖P11‖²`, `E` the regular-residual blocks `(0,0),(0,1),(1,0)`, `P11` the `(1,1)` block.
Pure `Fintype.sum_sum_type`; stated for a general entry weight `f` to dodge a typeclass. -/
theorem frobenius_fromBlocks {r mlo nhi₀ nhi₁ : Type*} [Fintype r] [Fintype mlo]
    [Fintype nhi₀] [Fintype nhi₁] {R S : Type*} [AddCommMonoid S] (f : R → S)
    (E00 : Matrix r nhi₀ R) (E01 : Matrix r nhi₁ R)
    (E10 : Matrix mlo nhi₀ R) (E11 : Matrix mlo nhi₁ R) :
    (∑ i, ∑ j, f (Matrix.fromBlocks E00 E01 E10 E11 i j))
      = ((∑ i, ∑ j, f (E00 i j)) + (∑ i, ∑ j, f (E01 i j)))
        + ((∑ i, ∑ j, f (E10 i j)) + (∑ i, ∑ j, f (E11 i j))) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
    rw [Finset.sum_add_distrib]
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    rw [Finset.sum_add_distrib]

/-- **The matrix-core comparability squeeze** (#54, the load-bearing #44c obligation, route- and
encoding-independent). With the loss-block decomposed as `P₁₁ = leak + R` entrywise (`hsplit`: `R` =
the gauge-normalized Schur core, `leak` = the regular×regular endpoint leak) and the leak charged to
the regular block `∑ leak² ≤ t²·∑ E²` (`hleak`; `t = ‖pivot‖ → 0` at `w0`), the loss `∑E² + ‖P₁₁‖²`
is two-sidedly comparable to the clean form `∑E² + ‖R‖²`:
`(2(1+t²))⁻¹·(∑E²+‖R‖²) ≤ ∑E²+‖P₁₁‖² ≤ (2+2t²)·(∑E²+‖R‖²)`.
The thin specialisation of `squeeze_bounds_abstract` (`p = leak`, `s = R`, `p+s = P₁₁`). The g153
raw-`∏T` refutation is dodged: the leak is in the regular ideal (`hleak`), so its excess is charged
to `∑E²`, not the core — exactly where the raw-`∏T` core was insufficient. -/
theorem core_comparability_squeeze {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → ℝ) (P11 leak Rcore : κ → ℝ) (t : ℝ)
    (hsplit : ∀ j, P11 j = leak j + Rcore j)
    (hleak : (∑ j, (leak j) ^ 2) ≤ t ^ 2 * (∑ i, (E i) ^ 2)) :
    ((∑ i, (E i) ^ 2) + (∑ j, (Rcore j) ^ 2))
        ≤ (2 * (1 + t ^ 2)) * ((∑ i, (E i) ^ 2) + (∑ j, (P11 j) ^ 2))
    ∧ ((∑ i, (E i) ^ 2) + (∑ j, (P11 j) ^ 2))
        ≤ (2 + 2 * t ^ 2) * ((∑ i, (E i) ^ 2) + (∑ j, (Rcore j) ^ 2)) := by
  simp only [hsplit]
  exact squeeze_bounds_abstract E leak Rcore t hleak

/-- **The full-product Frobenius core split** (route-independent, g156-confirmed). For the FULL chain
product written in block form `P = fromBlocks P00 P01 P10 P11` with the pivot `P00` invertible, the
squared-Frobenius loss against the deepest value `blockdiag[1, 0]` splits as the regular-residual sum
`∑E²` (over the `(0,0)−1`, `(0,1)`, `(1,0)` blocks) plus `‖P11‖²`, and `P11 = leak + R` with the
**full-product Schur complement** `R = P11 − P10·⅟P00·P01` and `leak = P10·⅟P00·P01` (the regular
endpoint leak `∈ ideal(P10, P01)`). The honest reduced core is `R` (g156: NOT `∏S_s` — the Schur
complement of a product is not the product of Schur complements; but `R − ∏S_s ∈ ideal(E)`, so the
two squeeze the same). The thin assembly of `frobenius_fromBlocks` (`f = ·²`) + `schur_P11_decomp`,
ready for `core_comparability_squeeze`. -/
theorem fullProduct_core_split {r mlo nhi : Type*} [Fintype r] [DecidableEq r] [Fintype mlo]
    [Fintype nhi]
    (P00 : Matrix r r ℝ) (P01 : Matrix r nhi ℝ) (P10 : Matrix mlo r ℝ) (P11 : Matrix mlo nhi ℝ)
    [Invertible P00] :
    (∑ i, ∑ j, ((Matrix.fromBlocks P00 P01 P10 P11
            - Matrix.fromBlocks (1 : Matrix r r ℝ) (0 : Matrix r nhi ℝ)
                (0 : Matrix mlo r ℝ) (0 : Matrix mlo nhi ℝ)) i j) ^ 2)
        = (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
            + ((∑ i, ∑ j, (P10 i j) ^ 2) + (∑ i, ∑ j, (P11 i j) ^ 2)))
      ∧ (∀ i j, P11 i j = (P10 * ⅟P00 * P01) i j + (P11 - P10 * ⅟P00 * P01) i j) := by
  refine ⟨?_, ?_⟩
  · -- Frobenius block split: `fromBlocks − blockdiag[1,0] = fromBlocks (P00−1) P01 P10 P11`.
    have hsub : (Matrix.fromBlocks P00 P01 P10 P11
          - Matrix.fromBlocks (1 : Matrix r r ℝ) (0 : Matrix r nhi ℝ)
              (0 : Matrix mlo r ℝ) (0 : Matrix mlo nhi ℝ))
        = Matrix.fromBlocks (P00 - 1) P01 P10 P11 := by
      rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
      simp [sub_eq_add_neg]
    rw [hsub]
    exact frobenius_fromBlocks (fun x => x ^ 2) (P00 - 1) P01 P10 P11
  · intro i j
    have hd := schur_P11_decomp (⅟P00) P01 P10 P11
    rw [hd]
    simp [Matrix.add_apply]

/-- **Frobenius submultiplicativity** (2-factor, entrywise squared). The squared-Frobenius energy of a
matrix product is bounded by the product of the factor energies: per-entry Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`) on `(M·N) i j = ∑ₖ M i k · N k j`, then the double-sum factors by
`Finset.sum_mul_sum`. Route-independent bedrock for the leak bound `hleak`. -/
theorem frobenius_mul_le {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (M : Matrix a b ℝ) (N : Matrix b c ℝ) :
    (∑ i, ∑ j, ((M * N) i j) ^ 2)
      ≤ (∑ i, ∑ k, (M i k) ^ 2) * (∑ j, ∑ k, (N k j) ^ 2) := by
  have hentry : ∀ i j, ((M * N) i j) ^ 2 ≤ (∑ k, (M i k) ^ 2) * (∑ k, (N k j) ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => M i k) (fun k => N k j)
  calc (∑ i, ∑ j, ((M * N) i j) ^ 2)
      ≤ ∑ i, ∑ j, (∑ k, (M i k) ^ 2) * (∑ k, (N k j) ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = (∑ i, ∑ k, (M i k) ^ 2) * (∑ j, ∑ k, (N k j) ^ 2) :=
        (Finset.sum_mul_sum Finset.univ Finset.univ
          (fun i => ∑ k, (M i k) ^ 2) (fun j => ∑ k, (N k j) ^ 2)).symm

/-- **The leak bound** (`hleak` discharge, route-independent). The endpoint leak `leak = P10·N·P01`
(`N = ⅟P00 ≈ I` near the deepest point) has squared-Frobenius energy bounded by
`‖N·P01‖²·(∑ P10²)`, hence (since both `P10, P01` sit inside the regular residual energy `E`, and one
of them is `≤ t²` near `w0`) is charged to `t²·∑E²` via `core_comparability_squeeze`. Here stated as
the clean two-factor chain `∑ leak² ≤ (∑ P10²)·(∑ (N·P01)²)` — the geometric `t²` smallness is
supplied by the consumer from `P10(w0)=0` + continuity. -/
theorem leak_frobenius_bound {r mlo nhi : Type*} [Fintype r] [Fintype mlo] [Fintype nhi]
    (N : Matrix r r ℝ) (P01 : Matrix r nhi ℝ) (P10 : Matrix mlo r ℝ) :
    (∑ i, ∑ j, ((P10 * N * P01) i j) ^ 2)
      ≤ (∑ i, ∑ k, (P10 i k) ^ 2) * (∑ j, ∑ k, ((N * P01) k j) ^ 2) := by
  rw [Matrix.mul_assoc]
  exact frobenius_mul_le P10 (N * P01)

/-- **The triple-product Frobenius upper bound**: `∑(P·A·Q)² ≤ (∑P²)·(∑(A·Q)²)` (one `frobenius_mul_le`
on `P·(A·Q)`), used both directions for the conjugation comparability. -/
theorem frobenius_triple_le {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (P : Matrix a b ℝ) (A : Matrix b c ℝ) (Q : Matrix c d ℝ) :
    (∑ i, ∑ j, ((P * A * Q) i j) ^ 2)
      ≤ (∑ i, ∑ k, (P i k) ^ 2) * (∑ j, ∑ k, ((A * Q) k j) ^ 2) := by
  rw [Matrix.mul_assoc]; exact frobenius_mul_le P (A * Q)

/-- The transposed-order Frobenius product bound: `∑ j, ∑ k, ((M·N) k j)² ≤ (∑M²)·(∑N²)` (the outer
sum over the RIGHT-matrix columns), via `Finset.sum_comm` on `frobenius_mul_le`. -/
theorem frobenius_mul_le' {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (M : Matrix a b ℝ) (N : Matrix b c ℝ) :
    (∑ j, ∑ k, ((M * N) k j) ^ 2)
      ≤ (∑ i, ∑ k, (M i k) ^ 2) * (∑ j, ∑ k, (N k j) ^ 2) := by
  have hcomm : (∑ j, ∑ k, ((M * N) k j) ^ 2) = ∑ i, ∑ j, ((M * N) i j) ^ 2 := Finset.sum_comm
  rw [hcomm]; exact frobenius_mul_le M N

/-- **Conjugation Frobenius comparability** (route-independent, the #80 STEP-1 endpoint-frame bound).
For FIXED invertible endpoint frames `P, Q` (the deepest gauge frame's two boundary units, #77/(iii)),
the squared-Frobenius energy of the conjugate `P·A·Q` is two-sidedly bounded by that of `A`:
`∑A² ≤ (∑Pi²·∑Qi²)·∑(P·A·Q)²` and `∑(P·A·Q)² ≤ (∑P²·∑Q²)·∑A²` (`Pi, Qi` the inverses). The upper bound
is `frobenius_triple_le`; the lower transports it through `A = Pi·(P·A·Q)·Qi`. The bounded conjugation
carrying `dlnLoss = ‖∏A − B‖² = ‖Pi·(∏C − D)·Qi‖²` to the comparable `‖∏C − D‖²` (the framed loss) —
the interior frames telescope (`G_s = I`, #77 (iii)), leaving only the constant endpoint conjugation. -/
theorem conjugation_frobenius_comparable {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (P : Matrix n n ℝ) (Q : Matrix m m ℝ) (Pi : Matrix n n ℝ) (Qi : Matrix m m ℝ)
    (hP : Pi * P = 1) (hQ : Q * Qi = 1) (A : Matrix n m ℝ) :
    (∑ i, ∑ j, (A i j) ^ 2)
        ≤ ((∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, (Qi k j) ^ 2))
            * (∑ i, ∑ j, ((P * A * Q) i j) ^ 2)
    ∧ (∑ i, ∑ j, ((P * A * Q) i j) ^ 2)
        ≤ ((∑ i, ∑ k, (P i k) ^ 2) * (∑ j, ∑ k, (Q k j) ^ 2)) * (∑ i, ∑ j, (A i j) ^ 2) := by
  have hnnP : (0 : ℝ) ≤ ∑ i, ∑ k, (P i k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnnPi : (0 : ℝ) ≤ ∑ i, ∑ k, (Pi i k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨?_, ?_⟩
  · -- lower: `A = Pi·(P·A·Q)·Qi`, then `frobenius_triple_le` + `frobenius_mul_le'` on the `Qi`-factor.
    have hA : A = Pi * (P * A * Q) * Qi := by
      have : Pi * (P * A * Q) * Qi = (Pi * P) * A * (Q * Qi) := by
        simp only [Matrix.mul_assoc]
      rw [this, hP, hQ, Matrix.one_mul, Matrix.mul_one]
    calc (∑ i, ∑ j, (A i j) ^ 2)
        = ∑ i, ∑ j, ((Pi * (P * A * Q) * Qi) i j) ^ 2 := by rw [← hA]
      _ ≤ (∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, ((P * A * Q) * Qi) k j ^ 2) :=
          frobenius_triple_le Pi (P * A * Q) Qi
      _ ≤ (∑ i, ∑ k, (Pi i k) ^ 2) * ((∑ i, ∑ k, ((P * A * Q) i k) ^ 2)
            * (∑ j, ∑ k, (Qi k j) ^ 2)) :=
          mul_le_mul_of_nonneg_left (frobenius_mul_le' (P * A * Q) Qi) hnnPi
      _ = (∑ i, ∑ k, (Pi i k) ^ 2) * (∑ j, ∑ k, (Qi k j) ^ 2)
            * (∑ i, ∑ j, ((P * A * Q) i j) ^ 2) := by ring
  · -- upper: `frobenius_triple_le P A Q`, then `frobenius_mul_le'` on the `A·Q`-factor.
    calc (∑ i, ∑ j, ((P * A * Q) i j) ^ 2)
        ≤ (∑ i, ∑ k, (P i k) ^ 2) * (∑ j, ∑ k, ((A * Q) k j) ^ 2) := frobenius_triple_le P A Q
      _ ≤ (∑ i, ∑ k, (P i k) ^ 2) * ((∑ i, ∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (Q k j) ^ 2)) :=
          mul_le_mul_of_nonneg_left (frobenius_mul_le' A Q) hnnP
      _ = (∑ i, ∑ k, (P i k) ^ 2) * (∑ j, ∑ k, (Q k j) ^ 2) * (∑ i, ∑ j, (A i j) ^ 2) := by ring

/-- **The full-product loss squeeze** (route-independent, the #80 matrix-core). For the FULL chain
product `P = fromBlocks P00 P01 P10 P11` with pivot `P00` invertible (`= I` near the deepest), the
squared-Frobenius loss against `D = blockdiag[1,0]` is two-sidedly comparable to `∑E² + ‖R‖²`, where
`∑E²` is the regular-residual energy (`(P00−1)`, `P01`, `P10` blocks) and `R = P11 − P10·⅟P00·P01` is
the full-product Schur core. The leak `P11 − R = P10·⅟P00·P01` is charged to `∑E²` (`hleak`: its
energy `≤ t²·∑E²`, supplied by the consumer from `P10, P01 → 0` + bounded `⅟P00` near the deepest).
Assembles `fullProduct_core_split` (the `∑E²+‖P11‖²` decomposition + `P11 = leak + R`) into
`core_comparability_squeeze`. The genuine `c₁ < c₂` squeeze (NOT exact) the loss-side needs. -/
theorem fullProduct_loss_squeeze {r mlo nhi : Type*} [Fintype r] [DecidableEq r] [Fintype mlo]
    [Fintype nhi]
    (P00 : Matrix r r ℝ) (P01 : Matrix r nhi ℝ) (P10 : Matrix mlo r ℝ) (P11 : Matrix mlo nhi ℝ)
    [Invertible P00] (t : ℝ)
    (hleak : (∑ i, ∑ j, ((P10 * ⅟P00 * P01) i j) ^ 2)
        ≤ t ^ 2 * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2) + (∑ i, ∑ j, (P01 i j) ^ 2))
            + (∑ i, ∑ j, (P10 i j) ^ 2))) :

 succeeded in 150ms:
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex` — obligation (i) of `deepest_gauge_construction`

The **`split`** field of `DeepestGaugeChart` (#44c obligation (i), crux2): the measure-preserving
gauge-slice coordinate reindex
`split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge`
with `split_mp` (measure-preserving) and `split_basepoint` (carries the flat image of the deepest
point to the split origin `0`). The other three obligations (`coreAbsorb` + its `rlct` peel +
`loss_squeeze`) are cobuild-sub34's; this module is the pure **measure/coordinate geometry**.

## The MP tension, resolved (g125 vs the structure field)

pp2's g125 cert flagged that the deepest-point regular-peel chart χ is **unit-Jacobian, NOT
measure-preserving** (`det = (1+w₀)²(w₄+1)`, intrinsic to the `S₁₁`-multiplication). That looks to
clash with `split_mp : MeasurePreserving split`. The reconciliation (cobuild-sub34's g157, 3-way
aligned): the unit-Jacobian content lives **entirely in `coreAbsorb`'s non-MP inter-layer unit**, so
`split` itself is a pure measure-preserving (`det = ±1`) **linear coordinate reindex**. g125's "no
det=±1 chart for the regular peel" is about the COMBINED peel (`split ∘ coreAbsorb`), not the bare
reindex.

## The dimension identity (the load-bearing combinatorial content, this file)

`flatDim H = deepestNReg H r + flatDim (deepestM H r) + nGauge` with
`nGauge = flatDim H − deepestNReg H r − flatDim (deepestM H r) ≥ 0`. Per layer,
`H_s·H_{s+1} − (H_s−r)(H_{s+1}−r) = r(H_s + H_{s+1} − r)`, so
`flatDim H − flatDim M = Σ_s r(H_s+H_{s+1}−r)`, and subtracting `nReg = r(H⁰+Hᴸ−r)` leaves
`r(2·Σ_{interior} H_i − (L−1)r) ≥ 0` (each interior `H_i ≥ r`, `L−1` of them) — so `nGauge ≥ 0`.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The per-layer block-count identity -/

/-- **Per-layer block count.** The full per-layer size minus the reduced (bottom-right) block equals
the regular-frame size `r(H_s + H_{s+1} − r)`: `H_s·H_{s+1} = (H_s−r)(H_{s+1}−r) + r(H_s+H_{s+1}−r)`,
given `r ≤ H_s` and `r ≤ H_{s+1}`. -/
theorem layer_block_count {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) :
    a * b = (a - r) * (b - r) + r * (a + b - r) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  -- a = r + a', b = r + b'; (a−r)(b−r) = a'b', a+b−r = r+a'+b', so RHS = a'b' + r(r+a'+b').
  have hsub : r + a' + (r + b') - r = r + a' + b' := by omega
  simp only [Nat.add_sub_cancel_left, hsub]
  ring

/-- **The regular-frame total.** Summed over layers, the per-layer regular size
`r(H_s + H_{s+1} − r)` telescopes to `r(H⁰ + Hᴸ − r) + r(2·Σ_{interior} H_i − (L−1)r)` — i.e. it is
`deepestNReg H r` plus the nonnegative spectator surplus. We package the bound: `deepestNReg H r ≤
Σ_s r(H s.castSucc + H s.succ − r)` (each interior `H_i ≥ r` makes the surplus `≥ 0`). -/
theorem deepestNReg_le_layer_regular_sum (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    deepestNReg H r ≤ ∑ s : Fin L, r * (H s.castSucc + H s.succ - r) := by
  -- Factor `r` out of both sides; reduce to `(H 0 + H last − r) ≤ Σ_s (H s.castSucc + H s.succ − r)`.
  unfold deepestNReg
  rw [← Finset.mul_sum]
  refine Nat.mul_le_mul_left r ?_
  -- Lower-bound the sum by the inner-term bound.  `H 0 = H (0:Fin L).castSucc` and
  -- `H last = H (Fin.last L) = H (last index of Fin L).succ`.
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  -- s₀ = first index, sₑ = last index of `Fin (L'+1)`.
  set s₀ : Fin (L' + 1) := 0 with hs₀
  set sₑ : Fin (L' + 1) := Fin.last L' with hsₑ
  have hcast₀ : (s₀.castSucc : Fin (L' + 2)) = 0 := by simp [hs₀]
  have hsuccₑ : (sₑ.succ : Fin (L' + 2)) = Fin.last (L' + 1) := by simp [hsₑ]
  -- Each summand is `≥ 0`; isolate the `s₀` and `sₑ` contributions.
  rcases Nat.eq_zero_or_pos L' with hL'0 | hLgt
  · -- L = 1 (L' = 0): single index `0 : Fin 1`, exact match `castSucc 0 = 0`, `succ 0 = last 1`.
    subst hL'0
    rw [Fin.sum_univ_one]
    have h0 : ((0 : Fin 1).castSucc : Fin 2) = 0 := by simp
    have he : ((0 : Fin 1).succ : Fin 2) = Fin.last 1 := by simp [Fin.last]
    rw [h0, he]
  · -- L ≥ 2 (L' ≥ 1): `s₀ ≠ sₑ`, isolate both terms; the rest is `≥ 0`.
    have hne : s₀ ≠ sₑ := by
      rw [hs₀, hsₑ]; intro h
      have := congrArg Fin.val h
      simp [Fin.last] at this; omega
    have hmem₀ : s₀ ∈ (Finset.univ : Finset (Fin (L' + 1))) := Finset.mem_univ _
    have hmemₑ : sₑ ∈ (Finset.univ.erase s₀) :=
      Finset.mem_erase.2 ⟨fun h => hne h.symm, Finset.mem_univ _⟩
    -- `Σ ≥ term(s₀) + term(sₑ)`.
    have hlb :
        (H s₀.castSucc + H s₀.succ - r) + (H sₑ.castSucc + H sₑ.succ - r)
          ≤ ∑ s : Fin (L' + 1), (H s.castSucc + H s.succ - r) := by
      rw [← Finset.add_sum_erase _ _ hmem₀]
      refine Nat.add_le_add_left ?_ _
      exact Finset.single_le_sum (f := fun s => H s.castSucc + H s.succ - r)
        (fun _ _ => Nat.zero_le _) hmemₑ
    refine le_trans ?_ hlb
    -- `H 0 + H last − r ≤ (H 0 + H s₀.succ − r) + (H sₑ.castSucc + H last − r)` (Nat, all `≥ r`).
    rw [hcast₀, hsuccₑ]
    have h1 : r ≤ H (0 : Fin (L' + 2)) := hr _
    have h2 : r ≤ H (Fin.last (L' + 1)) := hr _
    have h3 : r ≤ H s₀.succ := hr _
    have h4 : r ≤ H sₑ.castSucc := hr _
    omega

/-- **The flat-dimension identity** (the load-bearing combinatorial content of obligation (i)).
`flatDim H = deepestNReg H r + flatDim (deepestM H r) + nGauge`, where the spectator count
`nGauge = flatDim H − deepestNReg H r − flatDim (deepestM H r)` is `≥ 0`. The per-layer
`layer_block_count` gives `flatDim H = flatDim M + Σ_s r(H_s+H_{s+1}−r)`; then
`deepestNReg_le_layer_regular_sum` pins `nReg ≤` that sum, so the split is `nReg + flatDim M + (the
nonnegative remainder)`. -/
theorem flatDim_deepest_split (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    flatDim H
      = deepestNReg H r + flatDim (deepestM H r)
          + (flatDim H - deepestNReg H r - flatDim (deepestM H r)) := by
  -- `flatDim H = flatDim M + Σ_s r(H_s+H_{s+1}−r)` via per-layer `layer_block_count`.
  have hflat : flatDim H
      = flatDim (deepestM H r) + ∑ s : Fin L, r * (H s.castSucc + H s.succ - r) := by
    rw [flatDim_eq, flatDim_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have := layer_block_count (a := H s.castSucc) (b := H s.succ) (r := r)
      (hr s.castSucc) (hr s.succ)
    simpa [deepestM] using this
  -- `nReg ≤ Σ_s r(…)` so the difference is nonnegative; `omega` closes the `Nat.sub` rearrangement.
  have hle := deepestNReg_le_layer_regular_sum H r hr hL
  omega

/-! ## The role-respecting block split (the precision-pin: slots BY ROLE, not arbitrary)

The controller's precision pin (#64): the split's slots must be grouped BY ROLE — the core slot the
raw `T_s` blocks (`= FlatIdx (deepestM H r)`, forced by the slot type `Fin (flatDim (deepestM H r))`),
the regular slot the gauge pivots, spectators the rest — NOT an arbitrary `equivOfCardEq`. The
load-bearing piece is the **role-respecting index bijection** `FlatIdx H ≃ RegIdx ⊕ (FlatIdx (deepestM
H r) ⊕ GaugeIdx)`, where the middle summand is exactly the `T`-block entries `{(s,i,j) | r ≤ i ∧ r ≤
j}`. Building blocks below; the per-layer `r`-threshold row split is the atom. -/

/-- The per-vertex `r`-threshold split `Fin a ≃ Fin r ⊕ Fin (a − r)` (for `r ≤ a`): the first `r`
indices (the gauge/regular rows) and the last `a − r` (the reduced `T`-block rows). The atom of the
role-respecting block decomposition. -/
noncomputable def rThresholdSplit (r a : ℕ) (ha : r ≤ a) : Fin a ≃ Fin r ⊕ Fin (a - r) :=
  (finCongr (by omega : a = r + (a - r))).trans finSumFinEquiv.symm

/-- The per-layer entry split: a layer's entry index `Fin a × Fin b` (rows × cols) splits, by the
`r`-threshold on both, into the **three regular blocks** `(X = r×r) ⊕ (Y = r×(b−r)) ⊕ (Z = (a−r)×r)`
collected on the left, and the **reduced `T`-block** `MM = (a−r)×(b−r)` isolated on the right. The
`MM`-block is exactly the reduced-width layer entry (`a−r = M s.castSucc`, `b−r = M s.succ`), so its
`Σ`-collection is `FlatIdx (deepestM H r)` (the core slot). -/
noncomputable def layerEntrySplit (r a b : ℕ) (ha : r ≤ a) (hb : r ≤ b) :
    (Fin a × Fin b)
      ≃ ((Fin r × Fin r ⊕ Fin r × Fin (b - r)) ⊕ Fin (a - r) × Fin r)
          ⊕ (Fin (a - r) × Fin (b - r)) := by
  refine ((rThresholdSplit r a ha).prodCongr (rThresholdSplit r b hb)).trans ?_
  refine (Equiv.sumProdDistrib _ _ _).trans ?_
  refine ((Equiv.prodSumDistrib _ _ _).sumCongr (Equiv.prodSumDistrib _ _ _)).trans ?_
  exact (Equiv.sumAssoc _ _ _).symm

/-- `FlatIdx H ≃ Σ s, (Fin (H s.castSucc) × Fin (H s.succ))` — the layer-grouped entry form
(`sigmaAssoc` + the constant-fiber `sigmaEquivProd`). The intermediate for the role split. -/
noncomputable def flatIdxLayerProd (H : Fin (L + 1) → ℕ) :
    FlatIdx H ≃ Σ s : Fin L, (Fin (H s.castSucc) × Fin (H s.succ)) :=
  (Equiv.sigmaAssoc (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ))).trans
    (Equiv.sigmaCongrRight fun s => Equiv.sigmaEquivProd (Fin (H s.castSucc)) (Fin (H s.succ)))

/-- The reg+gauge entry collection (the three `X/Y/Z` blocks summed over layers) — the complement of
the reduced `T`-core in `FlatIdx H`. -/
abbrev RegGaugeIdx (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  Σ s : Fin L,
    ((Fin r × Fin r ⊕ Fin r × Fin (H s.succ - r)) ⊕ Fin (H s.castSucc - r) × Fin r)

/-- **The role-respecting index split**: `FlatIdx H ≃ RegGaugeIdx H r ⊕ FlatIdx (deepestM H r)` — the
reg+gauge entries (`X/Y/Z`) and the reduced `T`-core (`= FlatIdx (deepestM)`), grouped BY ROLE. The core
slot is exactly the reduced-chain flat index (the precision pin: core = the `T_s` blocks). Per-layer
`layerEntrySplit` collected (`sigmaCongrRight`), then `sigmaSumDistrib` separates reg-gauge from the
`MM`-core, whose `Σ`-collection is `FlatIdx (deepestM H r)`. -/
noncomputable def roleSplitIdx (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    FlatIdx H ≃ RegGaugeIdx H r ⊕ FlatIdx (deepestM H r) := by
  refine (flatIdxLayerProd H).trans ?_
  refine (Equiv.sigmaCongrRight fun (s : Fin L) =>
    layerEntrySplit r (H s.castSucc) (H s.succ) (hr s.castSucc) (hr s.succ)).trans ?_
  refine (Equiv.sigmaSumDistrib _ _).trans ?_
  refine Equiv.sumCongr (Equiv.refl _) ?_
  -- `Σ s, (Fin (M s.castSucc) × Fin (M s.succ)) ≃ FlatIdx (deepestM H r)`.
  refine (Equiv.sigmaCongrRight fun (s : Fin L) =>
    (Equiv.sigmaEquivProd (Fin (deepestM H r s.castSucc)) (Fin (deepestM H r s.succ))).symm).trans ?_
  exact (Equiv.sigmaAssoc
    (fun (s : Fin L) (_ : Fin (deepestM H r s.castSucc)) => Fin (deepestM H r s.succ))).symm

/-! ## The measure-preserving gauge-slice reindex -/

/-- The spectator (gauge) coordinate count: the flat directions left after the regular frame and the
reduced core. `nGauge = flatDim H − deepestNReg H r − flatDim (deepestM H r) ≥ 0` (the surplus from
`flatDim_deepest_split`). -/
abbrev deepestNGauge (H : Fin (L + 1) → ℕ) (r : ℕ) : ℕ :=
  flatDim H - deepestNReg H r - flatDim (deepestM H r)

/-- `card (RegGaugeIdx H r) = deepestNReg + deepestNGauge` — the reg+gauge entries number the
non-core flat directions (from `roleSplitIdx` being a bijection + the dimension identity). -/
theorem card_regGaugeIdx (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Fintype.card (RegGaugeIdx H r) = deepestNReg H r + deepestNGauge H r := by
  have hcard := Fintype.card_congr (roleSplitIdx H r hr)
  rw [Fintype.card_sum] at hcard
  have hfH : Fintype.card (FlatIdx H) = flatDim H := rfl
  have hfM : Fintype.card (FlatIdx (deepestM H r)) = flatDim (deepestM H r) := rfl
  rw [hfH, hfM] at hcard
  have hdim := flatDim_deepest_split H r hr hL
  unfold deepestNGauge
  omega

/-! ## The #120 explicit boundary-pivot packing (deriv-fm, #82-deriv)

The transparent replacement for the opaque `Fintype.equivFin` reg/gauge split: route the reg slot
explicitly onto the boundary generators `(X_first, Y_last, Z_first)`, so the reg-block derivative is `id`
by construction (g213/#91). `regResidualPack` (in `DeepestGaugeConstruction`) and `regGaugeIdxSplit`
(below) both factor through the SAME `regPivotFinEquiv`, so they cancel. -/

/-- **The boundary-pivot index type** — the residual blocks `(P11−I, P12, P21)` surviving the idempotent
sandwich: `(r×r) ⊕ ((r×M_L) ⊕ (M_0×r))`, the sum type `regResidualPack` targets, of card `deepestNReg`. -/
abbrev BoundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  (Fin r × Fin r) ⊕ ((Fin r × Fin (H (Fin.last L) - r)) ⊕ (Fin (H 0 - r) × Fin r))

/-- **The card match** — `card BoundaryPivotIdx = deepestNReg` (the arithmetic `regResidualPack` proves:
`r² + r(H_L−r) + (H_0−r)r = r(H_0+H_L−r)`). -/
theorem card_boundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fintype.card (BoundaryPivotIdx H r) = deepestNReg H r := by
  simp only [BoundaryPivotIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
  obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
  unfold deepestNReg
  rw [← ha', ← hb']
  simp only [Nat.add_sub_cancel_left]
  rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
  ring

/-- **The explicit pivot packing** `Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r` — the TRANSPARENT
`finProdFinEquiv`/`finSumFinEquiv`/`finCongr` enumeration replacing the opaque `Fintype.equivFin`.
Computable (has `_apply` equation lemmas), so the cancellation reduces. -/
noncomputable def regPivotFinEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r :=
  (finCongr (show deepestNReg H r
      = r * r + (r * (H (Fin.last L) - r) + (H 0 - r) * r) by
        obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
        obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
        unfold deepestNReg
        rw [← ha', ← hb']
        simp only [Nat.add_sub_cancel_left]
        rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
        ring)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm
        (finSumFinEquiv.symm.trans
          (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm))))

/-- The first layer index `⟨0,_⟩ : Fin L` (`0 < L` from `1 ≤ L`). -/
def firstLayer (hL : 1 ≤ L) : Fin L := ⟨0, by omega⟩

/-- The last layer `⟨L-1,_⟩ : Fin L`; `.succ` is `Fin.last L` (width `H (Fin.last L)`). -/
def lastLayer (hL : 1 ≤ L) : Fin L := ⟨L - 1, by omega⟩

/-- `(lastLayer hL).succ` has the same `H`-width as `Fin.last L` — the Y_last column cast. -/
theorem H_lastLayer_succ (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    H ((lastLayer hL).succ) = H (Fin.last L) := by
  congr 1; apply Fin.ext; simp [lastLayer, Fin.succ, Fin.last]; omega

/-- **The boundary-generator routing** `BoundaryPivotIdx → RegGaugeIdx` (the reg-half target):
`X_first` ↦ layer-0 (0,0) entry, `Y_last` ↦ last-layer (0,1) entry, `Z_first` ↦ layer-0 (1,0) entry.
INJECTIVE (distinct layer-tag × sum-arm). -/
def regBoundaryToRegGauge (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    BoundaryPivotIdx H r → RegGaugeIdx H r
  | Sum.inl (i, j) => ⟨firstLayer hL, Sum.inl (Sum.inl (i, j))⟩
  | Sum.inr (Sum.inl (i, j)) =>
      ⟨lastLayer hL, Sum.inl (Sum.inr (i, (finCongr (by rw [H_lastLayer_succ H hL])) j))⟩
  | Sum.inr (Sum.inr (i, j)) => ⟨firstLayer hL, Sum.inr (i, j)⟩

/-- A LEFT INVERSE of `regBoundaryToRegGauge` (total on `RegGaugeIdx`, inverting on the image). -/
def regGaugeDecode (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    RegGaugeIdx H r → BoundaryPivotIdx H r
  | ⟨_, Sum.inl (Sum.inl (i, j))⟩ => Sum.inl (i, j)
  | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
      if h : H s.succ - r = H (Fin.last L) - r then Sum.inr (Sum.inl (i, (finCongr h) j))
      else Sum.inl (i, i)
  | ⟨s, Sum.inr (i, j)⟩ =>
      if h : H s.castSucc - r = H 0 - r then Sum.inr (Sum.inr ((finCongr h) i, j))
      else Sum.inl (j, j)

/-- **`regBoundaryToRegGauge` is INJECTIVE** (the no-collapse fact) — via the left inverse `regGaugeDecode`
(`decode ∘ route = id`, per arm: X reads back, Y/Z fire their `dif` and the `finCongr` round-trip
collapses). The reg-half read is injective, so the `Σ_s δX_s` sandwich keeps `X_first` alone. -/
theorem regBoundaryToRegGauge_injective (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    Function.Injective (regBoundaryToRegGauge H r hL) := by
  have hY : H (lastLayer hL).succ - r = H (Fin.last L) - r := by rw [H_lastLayer_succ H hL]
  have hZ : H ((firstLayer hL).castSucc) - r = H 0 - r := by
    have hc : (firstLayer hL).castSucc = (0 : Fin (L + 1)) := by
      apply Fin.ext; simp [firstLayer, Fin.castSucc, Fin.castAdd, Fin.castLE]
    rw [hc]
  refine Function.LeftInverse.injective (g := regGaugeDecode H r hL) (fun b => ?_)
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · rfl
  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hY]
    exact congrArg (fun x => Sum.inr (Sum.inl (i, x))) (Fin.ext (by simp [finCongr_apply]))
  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hZ]
    exact congrArg (fun x => Sum.inr (Sum.inr (x, j))) (Fin.ext (by simp [finCongr_apply]))

/-- **The role-respecting `Fin`-index equivalence** (the precision-pin core): `Fin (flatDim H) ≃
Fin nReg ⊕ (Fin (flatDim (deepestM H r)) ⊕ Fin nGauge)`, where the MIDDLE summand is the reduced `T`-core
(`= FlatIdx (deepestM)`) and the outer/right are the reg/gauge entries — slots BY ROLE, NOT arbitrary.
Built from `roleSplitIdx` (the role split) + `Fintype.equivFin` on each summand + `card_regGaugeIdx`
(reg-gauge count) + `finSumFinEquiv` (the reg/gauge `Fin`-split) + `sumAssoc`. -/
noncomputable def deepestRoleIndexEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Fin (flatDim H)
      ≃ Fin (deepestNReg H r) ⊕ (Fin (flatDim (deepestM H r)) ⊕ Fin (deepestNGauge H r)) := by
  -- `Fin (flatDim H) ≃ FlatIdx H ≃ RegGaugeIdx ⊕ FlatIdx (deepestM)`.
  refine (Fintype.equivFin (FlatIdx H)).symm.trans ((roleSplitIdx H r hr).trans ?_)
  -- RegGaugeIdx ≃ Fin nReg ⊕ Fin nGauge; FlatIdx (deepestM) ≃ Fin (flatDim M).
  have eReg : RegGaugeIdx H r ≃ Fin (deepestNReg H r) ⊕ Fin (deepestNGauge H r) :=
    (Fintype.equivFin (RegGaugeIdx H r)).trans
      ((finCongr (card_regGaugeIdx H r hr hL)).trans finSumFinEquiv.symm)
  have eCore : FlatIdx (deepestM H r) ≃ Fin (flatDim (deepestM H r)) :=

 succeeded in 162ms:
# Lean conventions (DLNFibre)

## Build
- Fresh shells: `source ~/.elan/env` before any `lake` command.
- Build from this `lean/` directory: `lake build DLNFibre.<Module>`, or `lake build` for the whole library.
- First build on a machine: `lake exe cache get` fetches Mathlib oleans before `lake build`.
- Toolchain: Lean `v4.29.0` (`lean-toolchain`), Mathlib `v4.29.0` (`lakefile.toml`). Matches the `ai-research-assistant` harness one level up, so its v4.29 Mathlib idioms transfer.

## Library shape — engine vs application
- **`DLNFibre.Core.*`** is the network-free **engine** (quiver orbits, Kostant partitions / rank patterns, `Ext` codimension, `(C, θ)`). It **must never import `DLNFibre.DLN`**. The dependency arrows point `DLN → Core → Mathlib`.
- **`DLNFibre.DLN.*`** is the **application** (multiplication-map fibres, the square-Frobenius loss, the RLCT payoff); it depends on `Core`.
- State each result at the specificity its claim needs; lift a piece into shared `Core` API on its **second** use, not in anticipation of one. Good API (characterizations over predicates, weakest hypotheses, name = content) is the `bedrock`/`precision` discipline, not a folder layout.

## Aggregator
- `DLNFibre.lean` is single-writer. Add new module imports at the end; do not reorder existing imports.
- New modules live at `DLNFibre/<Core|DLN>/<Topic>/<File>.lean`; one substantive theorem family per file.

## Sorry gate
- Zero `sorry` / `axiom` / `native_decide` / `#exit` in committed files. Audit with `scripts/sorries` from `lean/` before every commit.
- A `sorry` with a correct statement is a building block; a `sorry` with a wrong statement misleads. Fix wrong statements first.

## Bedrock (the bar above the sorry gate)
A green, sorry-free build is the **floor**: it defeats *technical* slop, never *conceptual* slop —
"technically correct but subtly wrong, not The Way." Build each result as **bedrock**: something the next
theorem stands on without re-opening it. Where there's nothing to check against, **beauty is the guide** — a
vacuous, mis-scoped, or overclaiming theorem is *ugly*. In practice that recurrently means (not exhaustively):
name = content; non-vacuous, with the witness *shown* in-file; the weakest hypotheses that suffice, in usable
form; characterized (an `iff`) over asserted; every *cited*/*assumed* step named (never an `…rlct…`-style
theorem that secretly claims an unproved analytic interface — here the `rlct = ½·codim` reading rests on a
cited bound). The controller judges against this taste and holds precedence — full statement:
[`../docs/policies/bedrock.md`](../docs/policies/bedrock.md).

## Style
- `↦` not `=>` for lambda arrows.
- `decide +kernel`, not `native_decide`. Avoid `@[implemented_by]`, `@[extern]`, `unsafePerformIO`.
- One-line docstrings.
- Name a lemma for what it proves: a kernel/ideal *membership* fact is `…_mem_ker`, not `…_gen` (which reads as an ideal-generation claim).
- Confirm a Mathlib lemma exists before building a proof around it: `scripts/lean-search "..."`, or `rg` over `.lake/packages/mathlib/Mathlib/`.
- Pre-stage uncertain API with `example` blocks that pin lemma names/types; keep them as durable contracts.

## Mathlib gotchas (v4.29 pin)
Toolchain-generic notes that transfer at this pin. Accumulate new, DLN-specific ones here as they are found
(the ReLU programme's proof-specific notes were intentionally not ported — they were about a different theory).

- **`Basis` is `Module.Basis` at the v4.29 pin.** Bare `Basis` is unknown even with full Mathlib imports;
  ascribe `Module.Basis (Fin _) ℝ _` (e.g. from `Pi.basisFun`). Dot-notation (`b.tensorProduct b'`) is
  unaffected. Likely to recur in any `Matrix.rank` / column-span work.
- **`decide +kernel`, never `native_decide`.** Kernel `decide` is axiom-clean; `native_decide` trusts the
  compiler and breaks `#print axioms` hygiene. Kernel-reduction cost is **heartbeat-invisible** (a
  `maxHeartbeats` bump does not speed it), so a heartbeat timeout on a `decide` is not the symptom to chase.
- **Matrix-product identities over `ℤ` by `decide`, then cast.** An `ℝ` matrix-product identity is a
  `Matrix.ext` blow-up (per-entry `simp`, times out at scale). Write the matrices over `ℤ`
  (`DecidableEq` ⟹ `Matrix.mul` decides by kernel reduction, `by decide`), define the `ℝ` ones via
  `· .map (Int.castRingHom ℝ)`, and transfer products with `← Matrix.map_mul` (cast is a ring hom). No `ℝ`
  `Matrix.ext` at all.
- **`Fin`-vector `![…]` + `fin_cases` friction.** `fin_cases i` leaves the index as `⟨k, ⋯⟩` (a `Fin.mk`),
  so `Matrix.cons_val_one`/`_two`/… do not fire on the outer selection. Normalize first with
  `rw [show (⟨k, by omega⟩ : Fin n) = (k : Fin n) from rfl]`, then the `cons_val_*` simp set fires; or prove
  the components as separate `have`s and assemble with `funext i; fin_cases i`.
- **`φ` (U+03C6) as a binder name can hit a lexer reject** (`unexpected token 'φ'; expected identifier`)
  when an editing tool inserts a confusable/variant codepoint. If a `∃ φ …` / `obtain ⟨φ, …⟩` line fails
  to parse despite looking right, rename the binder to ASCII (`phi`) or `ψ`; capital `Φ` (U+03A6) has not
  shown the problem. Cost two build cycles on `NoetherMonicPositioning.lean`.

codex
For v4.29 the calculus API matters here: the product rule returns scalar-multiplication forms, so the zero-derivative lemmas should be shaped to let `simp` discharge `f 0 = 0` and `g 0 = 0`. I’m checking the exact theorem signatures now.
exec
/bin/bash -lc "sed -n '1,180p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '1,220p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "rg -n \"theorem HasStrictFDerivAt\\.(mul|add|sub|neg|const_mul|mul_const|const_smul|smul|fun_sum|clm_apply|comp|prodMk)|def HasStrictFDerivAt|hasStrictFDerivAt_const|hasStrictFDerivAt_id|hasStrictFDerivAt_pi|hasStrictFDerivAt_apply|ContinuousLinearMap.proj\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv -S" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '1,180p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 123ms:
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The derivative of bounded linear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
bounded linear maps.
-/

public section

open Asymptotics

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable (f : E →L[𝕜] F)
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/-!
### Bundled continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `ContinuousLinearMap`, and denoted `E →L[𝕜] F`, works for topological vector spaces),
and the unbundled version (with a predicate `IsBoundedLinearMap`, requires normed spaces).
This section deals with the first form, see below for the unbundled version
-/

protected theorem hasFDerivAtFilter : HasFDerivAtFilter f f L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun x => by
    simp only [f.map_sub, sub_self, Pi.zero_apply]

@[fun_prop]
protected theorem hasStrictFDerivAt : HasStrictFDerivAt f f x :=
  f.hasFDerivAtFilter

@[fun_prop]
protected theorem hasFDerivWithinAt : HasFDerivWithinAt f f s x :=
  f.hasFDerivAtFilter

@[fun_prop]
protected theorem hasFDerivAt : HasFDerivAt f f x :=
  f.hasFDerivAtFilter

@[simp, fun_prop]
protected theorem differentiableAt : DifferentiableAt 𝕜 f x :=
  f.hasFDerivAt.differentiableAt

@[fun_prop]
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

@[simp, fun_prop]
protected theorem differentiable : Differentiable 𝕜 f := fun _ =>
  f.differentiableAt

@[fun_prop]
protected theorem differentiableOn : DifferentiableOn 𝕜 f s :=
  f.differentiable.differentiableOn

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]

@[simp]
protected theorem fderiv : fderiv 𝕜 f x = f :=
  f.hasFDerivAt.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x = f := by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

end ContinuousLinearMap

/-! ### Unbundled continuous linear maps -/

namespace IsBoundedLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F}
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

theorem hasFDerivAtFilter (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAtFilter f h.toContinuousLinearMap L :=
  h.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
theorem hasFDerivWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivWithinAt f h.toContinuousLinearMap s x :=
  h.hasFDerivAtFilter

@[fun_prop]
theorem hasFDerivAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAt f h.toContinuousLinearMap x :=
  h.hasFDerivAtFilter

@[fun_prop]
theorem differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

@[fun_prop]
theorem differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt

protected theorem fderiv (h : IsBoundedLinearMap 𝕜 f) :
    fderiv 𝕜 f x = h.toContinuousLinearMap :=
  HasFDerivAt.fderiv h.hasFDerivAt

protected theorem fderivWithin (h : IsBoundedLinearMap 𝕜 f)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = h.toContinuousLinearMap := by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv

@[fun_prop]
theorem differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun _ => h.differentiableAt

@[fun_prop]
theorem differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.differentiable.differentiableOn

end IsBoundedLinearMap

 succeeded in 178ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:51:theorem hasStrictFDerivAt_piLp :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:55:  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_hasStrictFDerivAt_iff, hasStrictFDerivAt_pi']
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:77:nonrec theorem hasStrictFDerivAt_apply (f : PiLp p E) (i : ι) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:80:  (hasStrictFDerivAt_apply i f).comp f (hasStrictFDerivAt_ofLp (𝕜 := 𝕜) p f)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:95:  (hasStrictFDerivAt_apply p f i).hasFDerivAt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:57:theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:186:theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:317:theorem hasStrictFDerivAt_const_add_iff (c : F) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:322:alias ⟨_, HasStrictFDerivAt.const_add⟩ := hasStrictFDerivAt_const_add_iff
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:390:theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:503:theorem HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:603:theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:748:  (hasStrictFDerivAt_id x).sub_const c
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:61:theorem hasStrictFDerivAt_const (c : F) (x : E) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:67:    HasStrictFDerivAt (0 : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:71:    HasStrictFDerivAt (1 : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:75:    HasStrictFDerivAt (n : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:79:    HasStrictFDerivAt (z : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:83:    HasStrictFDerivAt (ofNat(n) : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:364:  exact (hasStrictFDerivAt_const (0 : F) x).congr_of_eventuallyEq h.symm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:57:protected theorem HasStrictFDerivAt.prodMk (hf₁ : HasStrictFDerivAt f₁ f₁' x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:359:theorem hasStrictFDerivAt_pi' :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:364:theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:365:    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:368:theorem hasStrictFDerivAt_apply (i : ι) (f : ∀ i, F' i) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:372:theorem hasStrictFDerivAt_pi :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:375:  hasStrictFDerivAt_pi'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:612:  simp_rw [domDomCongr_apply, compContinuousLinearMap_apply, ContinuousLinearMap.proj_apply,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:632:    (hasStrictFDerivAt_pi.2 fun _ ↦ hasStrictFDerivAt_id _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:657:    |>.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:676:theorem hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt id (.id 𝕜 E) x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:74:  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι ↦ hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:59:theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:116:theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:118:  simpa only [smul_zero, zero_add] using hc.smul (hasStrictFDerivAt_const f x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:170:theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:177:theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:270:theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:275:theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:342:theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:402:  | nil => simp [hasStrictFDerivAt_const]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:502:    (hasStrictFDerivAt_pi.mpr fun i ↦ h (l.get i) (List.getElem_mem ..)) :) ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:551:theorem HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:558:      hasStrictFDerivAt_pi.mpr fun i ↦ h (Subtype.val i) i.prop :)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:601:    (hasStrictFDerivAt_finset_prod.comp x <| hasStrictFDerivAt_pi.mpr fun i ↦ hg i i.prop)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:95:    hasStrictFDerivAt_id (t • x) |>.const_smul t⁻¹
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:52:  | 0 => by simpa using hasStrictFDerivAt_const 1 x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:66:  hasStrictFDerivAt_id _ |>.pow' n
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:211:  hasStrictFDerivAt_id _ |>.pow n
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:100:theorem HasStrictFDerivAt.clm_apply (hc : HasStrictFDerivAt c c' x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:68:protected theorem HasStrictFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:129:def HasStrictFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:77:    |>.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))

 succeeded in 169ms:
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Multiplicative operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* multiplication of a function by a scalar function
* product of finitely many scalar functions
* taking the pointwise multiplicative inverse (i.e. `Inv.inv` or `Ring.inverse`) of a function
-/

public section

open scoped Ring
open Asymptotics ContinuousLinearMap Topology

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}

section SMul

/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `fun x ↦ c x • f x` is differentiable as well. Lemmas in this section work for
functions `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/


variable {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

variable {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'}

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x :=
  (isBoundedBilinearMap_smul.hasStrictFDerivAt (c x, f x)).comp x <| hc.prodMk hf

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.smul
    (hc : HasFDerivWithinAt c c' s x) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (c • f) (c x • f' + c'.smulRight (f x)) s x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp_hasFDerivWithinAt x <|
    hc.prodMk hf

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp x <| hc.prodMk hf

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (c • f) s x :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (c • f) x :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (hc x hx).smul (hf x hx)

@[to_fun (attr := simp, fun_prop)]
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (c • f) := fun x => (hc x).smul (hf x)

theorem fderivWithin_fun_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun y => c y • f y) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (c • f) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (c • f) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

@[fun_prop]
theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
    HasStrictFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasStrictFDerivAt_const f x)

@[fun_prop]
theorem HasFDerivWithinAt.smul_const (hc : HasFDerivWithinAt c c' s x) (f : F) :
    HasFDerivWithinAt (fun y => c y • f) (c'.smulRight f) s x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFDerivWithinAt_const f x s)

@[fun_prop]
theorem HasFDerivAt.smul_const (hc : HasFDerivAt c c' x) (f : F) :
    HasFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFDerivAt_const f x)

@[fun_prop]
theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.hasFDerivWithinAt.smul_const f).differentiableWithinAt

@[fun_prop]
theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.hasFDerivAt.smul_const f).differentiableAt

@[fun_prop]
theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
    DifferentiableOn 𝕜 (fun y => c y • f) s := fun x hx => (hc x hx).smul_const f

@[fun_prop]
theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
    Differentiable 𝕜 fun y => c y • f := fun x => (hc x).smul_const f

theorem fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smulRight f :=
  (hc.hasFDerivWithinAt.smul_const f).fderivWithin hxs

theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smulRight f :=
  (hc.hasFDerivAt.smul_const f).fderiv

end SMul

section Mul

/-! ### Derivative of the product of two functions -/

open scoped RightActions


variable {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
    (hb : HasStrictFDerivAt b b' x) :
    HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z

 succeeded in 195ms:
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Additive operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
-/

public section


open Filter Asymptotics ContinuousLinearMap

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : E → F}
variable {f' g' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

section ConstSMul

variable {R : Type*} [Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F]
  [ContinuousConstSMul R F]

/-! ### Derivative of a function multiplied by a constant -/

@[to_fun]
theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' L) (c : R) :
    HasFDerivAtFilter (c • f) (c • f') L :=
  (c • (1 : F →L[𝕜] F)).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (c • f) (c • f') x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (c • f) (c • f') s x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (c • f) (c • f') x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (c • f) s x :=
  (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (c • f) x :=
  (h.hasFDerivAt.const_smul c).differentiableAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (h x hx).const_smul c

@[to_fun (attr := fun_prop)]
theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 (c • f) := fun x => (h x).const_smul c

theorem fderivWithin_fun_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs

theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x :=
  fderivWithin_fun_const_smul hxs h c

/-- If `c` is invertible, `c • f` is differentiable at `x` within `s` if and only if `f` is. -/
lemma differentiableWithinAt_smul_iff (c : R) [Invertible c] :
    DifferentiableWithinAt 𝕜 (c • f) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.const_smul c⟩
  apply (h.const_smul ⅟c).congr_of_eventuallyEq ?_ (by simp)
  filter_upwards with x using by simp

/-- A version of `fderivWithin_const_smul` without differentiability hypothesis:
in return, the constant `c` must be invertible, i.e. if `R` is a field. -/
theorem fderivWithin_const_smul_of_invertible (c : R) [Invertible c]
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact (h.hasFDerivWithinAt.const_smul c).fderivWithin hs
  · have : ¬DifferentiableWithinAt 𝕜 (c • f) s x := by
      contrapose! h
      exact (differentiableWithinAt_smul_iff c).mp h
    simp [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this]

theorem fderiv_fun_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

/-- If `c` is invertible, `c • f` is differentiable at `x` if and only if `f` is. -/
lemma differentiableAt_smul_iff (c : R) [Invertible c] :
    DifferentiableAt 𝕜 (c • f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ, differentiableWithinAt_smul_iff, differentiableWithinAt_univ]

/-- A version of `fderiv_const_smul` without differentiability hypothesis: in return, the constant
`c` must be invertible, i.e. if `R` is a field. -/
theorem fderiv_const_smul_of_invertible (c : R) [Invertible c] :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x := by
  simp [← fderivWithin_univ, fderivWithin_const_smul_of_invertible c uniqueDiffWithinAt_univ]

end ConstSMul

section ConstSMulDivisionRing

variable {R : Type*} [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F]
  [ContinuousConstSMul R F]

/-- Special case of `fderivWithin_const_smul_of_invertible` over a division semiring: any constant
is allowed.

TODO: This would work for scalars in a `GroupWithZero` if we had a `DistribMulActionWithZero`
typeclass. -/
lemma fderivWithin_const_smul_field (c : R) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  obtain (rfl | ha) := eq_or_ne c 0
  · simp
  · have : Invertible c := invertibleOfNonzero ha
    ext x
    simp [fderivWithin_const_smul_of_invertible c (f := f) hs]

@[deprecated (since := "2026-01-11")] alias fderivWithin_const_smul_of_field :=
  fderivWithin_const_smul_field

/-- Special case of `fderiv_const_smul_of_invertible` over a division semiring: any constant is
allowed.

TODO: This would work for scalars in a `GroupWithZero` if we had a `DistribMulActionWithZero`
typeclass. -/
lemma fderiv_const_smul_field (c : R) : fderiv 𝕜 (c • f) = c • fderiv 𝕜 f := by
  simp_rw [← fderivWithin_univ]
  ext x
  simp [fderivWithin_const_smul_field c uniqueDiffWithinAt_univ]

@[deprecated (since := "2026-01-11")] alias fderiv_const_smul_of_field := fderiv_const_smul_field

end ConstSMulDivisionRing

section Add

/-! ### Derivative of the sum of two functions -/

@[to_fun]
theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' L)
    (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L :=
  .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    grind [Pi.add_apply, add_apply]

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (f + g) (f' + g') x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f + g) (f' + g') x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f + g) s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s := fun x hx => (hf x hx).add (hg x hx)

@[to_fun (attr := simp, fun_prop)]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) := fun x => (hf x).add (hg x)

-- TODO: `@[to_fun]` gives incorrect lemma name
theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :

codex
The local API confirms the useful shape: `HasStrictFDerivAt.mul` gives derivative `f x • g' + g x • f'` for real-valued functions, so a product of two functions both zero at `0` immediately has derivative `0` after `simpa [hf0, hg0]`.
exec
/bin/bash -lc "sed -n '170,230p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
    (hb : HasStrictFDerivAt b b' x) :
    HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x) :
    HasFDerivWithinAt (a * b) (a x • b' + a' <• b x) s x := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp_hasFDerivWithinAt x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (c * d) (c x • d' + d x • c') s x := by
  convert hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (a * b) (a x • b' + a' <• b x) x := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithinAt 𝕜 (a * b) s x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    DifferentiableAt 𝕜 (a * b) x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
    DifferentiableOn 𝕜 (a * b) s := fun x hx => (ha x hx).mul (hb x hx)

@[to_fun (attr := simp, fun_prop)]
theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) :
    Differentiable 𝕜 (a * b) := fun x => (ha x).mul (hb x)

theorem fderivWithin_fun_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :

exec
/bin/bash -lc "sed -n '386,410p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean && sed -n '356,378p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean && sed -n '96,115p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '390,640p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "rg -n \"def proj|theorem .*proj|ContinuousLinearMap\\.proj|proj_apply\" lean/.lake/packages/mathlib/Mathlib/Analysis lean/.lake/packages/mathlib/Mathlib/Topology -S" in /home/ubuntu/workspace/deriv-spec
 succeeded in 148ms:
lean/.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Pi.lean:52:theorem Pi.uniformContinuous_proj (i : ι) : UniformContinuous fun a : ∀ i : ι, α i => a i :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean:34:This theorem was formalized as part of the Sphere Eversion project.
lean/.lake/packages/mathlib/Mathlib/Topology/VectorBundle/Basic.lean:342:theorem zeroSection_proj [∀ x, Zero (E x)] (x : B) : (zeroSection F E x).proj = x :=
lean/.lake/packages/mathlib/Mathlib/Topology/VectorBundle/Basic.lean:576:protected def proj : TotalSpace F Z.Fiber → B :=
lean/.lake/packages/mathlib/Mathlib/Topology/VectorBundle/Basic.lean:698:theorem continuous_proj : Continuous Z.proj :=
lean/.lake/packages/mathlib/Mathlib/Topology/VectorBundle/Basic.lean:702:theorem isOpenMap_proj : IsOpenMap Z.proj :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:364:theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:388:theorem hasFDerivAt_pi'' (hφ : ∀ i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:612:  simp_rw [domDomCongr_apply, compContinuousLinearMap_apply, ContinuousLinearMap.proj_apply,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:404:    simp only [List.map_cons, List.prod_cons, ← proj_apply (R := 𝕜) (φ := fun _ : ι ↦ 𝔸) a]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:505:    proj_apply, pi_apply, Function.comp_def]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:521:    proj_apply, pi_apply, Function.comp_def]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:534:    proj_apply, pi_apply, Function.comp_def]
lean/.lake/packages/mathlib/Mathlib/Topology/ExtremallyDisconnected.lean:86:theorem StoneCech.projective [DiscreteTopology X] : CompactT2.Projective (StoneCech X) := by
lean/.lake/packages/mathlib/Mathlib/Topology/ExtremallyDisconnected.lean:256:protected theorem CompactT2.ExtremallyDisconnected.projective [ExtremallyDisconnected A]
lean/.lake/packages/mathlib/Mathlib/Topology/ExtremallyDisconnected.lean:284:protected theorem CompactT2.projective_iff_extremallyDisconnected [CompactSpace A] [T2Space A] :
lean/.lake/packages/mathlib/Mathlib/Topology/Homotopy/Product.lean:141:theorem proj_pi (i : ι) (paths : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) :
lean/.lake/packages/mathlib/Mathlib/Topology/Homotopy/Product.lean:149:theorem pi_proj (p : Path.Homotopic.Quotient as bs) : (pi fun i => proj i p) = p := by
lean/.lake/packages/mathlib/Mathlib/Topology/Homotopy/Product.lean:200:theorem projLeft_prod : projLeft (prod q₁ q₂) = q₁ := by
lean/.lake/packages/mathlib/Mathlib/Topology/Homotopy/Product.lean:206:theorem projRight_prod : projRight (prod q₁ q₂) = q₂ := by
lean/.lake/packages/mathlib/Mathlib/Topology/Homotopy/Product.lean:212:theorem prod_projLeft_projRight (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:401:private theorem edist_proj_le_edist_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:133:def projₗ (i : ι) : PiLp p β →ₗ[𝕜] β i :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:1127:def proj (i : ι) : PiLp p β →L[𝕜] β i where
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:93:theorem Lcomplement {P : M} (h : IsLprojection X P) : IsLprojection X (1 - P) :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:98:theorem Lcomplement_iff (P : M) : IsLprojection X P ↔ IsLprojection X (1 - P) :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:101:theorem commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:139:theorem mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:156:theorem join [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:165:theorem coe_compl (P : { P : M // IsLprojection X P }) : ↑Pᶜ = (1 : M) - ↑P :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:172:theorem coe_inf [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:180:theorem coe_sup [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:188:theorem coe_sdiff [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:201:theorem le_def [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:210:theorem coe_zero : ↑(0 : { P : M // IsLprojection X P }) = (0 : M) :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:217:theorem coe_one : ↑(1 : { P : M // IsLprojection X P }) = (1 : M) :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:237:theorem compl_mul {P : { P : M // IsLprojection X P }} {Q : M} : ↑Pᶜ * Q = Q - ↑P * Q := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:240:theorem mul_compl_self {P : { P : M // IsLprojection X P }} : (↑P : M) * ↑Pᶜ = 0 := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:243:theorem distrib_lattice_lemma [FaithfulSMul M X] {P Q R : { P : M // IsLprojection X P }} :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:149:def proj (A : Finset β) : X →L[𝕜] X := ∑ i ∈ A, (b.coord i).smulRight (b i)
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:153:theorem proj_empty : b.proj ∅ = 0 := by simp [proj]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:157:theorem proj_apply (A : Finset β) (x : X) : b.proj A x = ∑ i ∈ A, b.coord i x • b i := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:162:theorem proj_apply_basis_mem (A : Finset β) (i : β) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:167:theorem tendsto_proj (x : X) : Tendsto (fun A ↦ b.proj A x) L.filter (𝓝 x) := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:171:theorem range_proj_eq_span (A : Finset β) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:175:    rw [ContinuousLinearMap.coe_coe, proj_apply]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:181:    rw [ContinuousLinearMap.coe_coe, proj_apply_basis_mem, if_pos (Finset.mem_coe.mp hi)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:185:theorem proj_comp (A B : Finset β) (x : X) : b.proj A (b.proj B x) = b.proj (A ∩ B) x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:186:  simp only [proj_apply, map_sum, map_smul, b.ortho, Pi.single_apply, ite_smul, one_smul, zero_smul,
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:193:theorem finrank_range_proj (A : Finset β) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:211:theorem enorm_proj_le_enormProjBound (A : Finset β) : ‖b.proj A‖ₑ ≤ b.enormProjBound :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:215:theorem exists_norm_proj_le [CompleteSpace X] : ∃ C : ℝ, ∀ A : Finset β, ‖b.proj A‖ ≤ C := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:223:    simp only [GeneralSchauderBasis.proj_apply]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:229:    rw [GeneralSchauderBasis.proj_apply]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:242:theorem bddAbove_range_nnnorm_proj [CompleteSpace X] :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:252:theorem nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:257:theorem norm_proj_le_nnnormProjBound [CompleteSpace X] (A : Finset β) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:271:def proj (n : ℕ) : X →L[𝕜] X := GeneralSchauderBasis.proj b (Finset.range n)
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:275:theorem proj_zero : b.proj 0 = 0 := by rw [proj, Finset.range_zero, GeneralSchauderBasis.proj_empty]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:279:theorem proj_apply (n : ℕ) (x : X) : b.proj n x = ∑ i ∈ Finset.range n, b.coord i x • b i := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:280:  rw [proj, GeneralSchauderBasis.proj_apply]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:283:theorem proj_apply_basis_mem (n i : ℕ) : b.proj n (b i) = if i < n then b i else 0 := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:284:  rw [proj, GeneralSchauderBasis.proj_apply_basis_mem]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:288:theorem range_proj_eq_span (n : ℕ) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:293:theorem finrank_range_proj (n : ℕ) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:298:theorem tendsto_proj (x : X) : Tendsto (fun n ↦ b.proj n x) atTop (𝓝 x) := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:303:theorem proj_comp (n m : ℕ) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:311:theorem exists_norm_proj_le [CompleteSpace X] : ∃ C : ℝ, ∀ n : ℕ, ‖b.proj n‖ ≤ C := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:322:theorem enorm_proj_le_enormProjBound (n : ℕ) : ‖b.proj n‖ₑ ≤ b.enormProjBound :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:331:theorem bddAbove_range_nnnorm_proj [CompleteSpace X] :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:341:theorem nnnorm_proj_le_nnnormProjBound [CompleteSpace X] (n : ℕ) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:346:theorem norm_proj_le_nnnormProjBound [CompleteSpace X] (n : ℕ) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:510:theorem basis_proj : (basis D).proj = D.P := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:512:  rw [SchauderBasis.proj_apply, ← sum_succSub D.P D.proj_zero n]
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean:280:    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smulRight_apply, LinearMap.id_apply, ←
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:58:def projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) → ℝ :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:61:theorem projectiveSeminormAux_nonneg (p : FreeAddMonoid (𝕜 × Π i, E i)) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:68:theorem projectiveSeminormAux_add_le (p q : FreeAddMonoid (𝕜 × Π i, E i)) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:72:theorem projectiveSeminormAux_smul (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:79:theorem bddBelow_projectiveSemiNormAux (x : ⨂[𝕜] i, E i) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:91:theorem projectiveSeminorm_zero : ‖(0 : ⨂[𝕜] i, E i)‖ = 0 :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:95:theorem projectiveSeminorm_add_le (x y : ⨂[𝕜] i, E i) : ‖x+y‖ ≤ ‖x‖ + ‖y‖ :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:99:theorem projectiveSeminorm_smul_le (a : 𝕜) (x : ⨂[𝕜] i, E i) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:108:noncomputable def projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) := .ofSMulLE
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:112:theorem projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:115:theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean:127:theorem norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G]
lean/.lake/packages/mathlib/Mathlib/Topology/Category/CompHaus/Projective.lean:58:def projectivePresentation (X : CompHaus) : ProjectivePresentation X where
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/InjectiveSeminorm.lean:109:theorem toDualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/PiTensorProduct/InjectiveSeminorm.lean:194:theorem injectiveSeminorm_le_projectiveSeminorm :
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:966:def projKerOfRightInverse [IsTopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:971:theorem coe_projKerOfRightInverse_apply [IsTopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:977:theorem projKerOfRightInverse_apply_idem [IsTopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:984:theorem projKerOfRightInverse_comp_inv [IsTopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
lean/.lake/packages/mathlib/Mathlib/Analysis/Analytic/Polynomial.lean:75:  fun x _ ↦ .aeval_mvPolynomial (fun i ↦ ((ContinuousLinearMap.proj i).comp f).analyticAt x) p
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:191:def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:195:theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:199:theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:202:theorem coe_proj (i : ι) : (proj i).toLinearMap = (LinearMap.proj i : ((i : ι) → φ i) →ₗ[R] _) :=
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:206:theorem pi_proj : pi proj = .id R (∀ i, φ i) := rfl
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:209:theorem pi_proj_comp (f : M₂ →L[R] ∀ i, φ i) : pi (proj · ∘L f) = f := rfl
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:211:theorem iInf_ker_proj :
lean/.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:558:  exact ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt _).comp_analyticWithinAt h
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:360:  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] M' i).compContinuousMultilinearMap f
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Projective.lean:55:def projectivePresentation (X : Profinite.{u}) : ProjectivePresentation X where
lean/.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Interval.lean:36:def projIccCM : C(α, Icc a b) :=
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:91:theorem continuous_proj :
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:107:theorem continuous_projRestrict : Continuous (ProjRestrict C J) :=
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:110:theorem proj_eq_self {x : I → Bool} (h : ∀ i, x i ≠ false → J i) : Proj J x = x := by
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:116:theorem proj_prop_eq_self (hh : ∀ i x, x ∈ C → x i ≠ false → J i) : π C J = C := by
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:122:theorem proj_comp_of_subset (h : ∀ i, J i → K i) : (Proj J ∘ Proj K) =
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:126:theorem proj_eq_of_subset (h : ∀ i, J i → K i) : π (π C K) J = π C J := by
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:146:theorem continuous_projRestricts (h : ∀ i, J i → K i) : Continuous (ProjRestricts C h) :=
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:149:theorem surjective_projRestricts (h : ∀ i, J i → K i) : Function.Surjective (ProjRestricts C h) :=
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:153:theorem projRestricts_eq_id : ProjRestricts C (fun i (h : J i) ↦ h) = id := by
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:157:theorem projRestricts_eq_comp (hJK : ∀ i, J i → K i) (hKL : ∀ i, K i → L i) :
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:163:theorem projRestricts_comp_projRestrict (h : ∀ i, J i → K i) :
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:548:theorem contained_eq_proj (o : Ordinal) (h : contained C o) :
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:554:theorem isClosed_proj (o : Ordinal) (hC : IsClosed C) : IsClosed (π C (ord I · < o)) :=
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean:557:theorem contained_proj (o : Ordinal) : contained (π C (ord I · < o)) o := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:632:theorem IsLittleOTVS.proj {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:635:  ContinuousLinearMap.proj i |>.isBigOTVS_fun_comp |>.trans_isLittleOTVS h
lean/.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:655:theorem IsBigOTVS.proj {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:658:  ContinuousLinearMap.proj i |>.isBigOTVS_fun_comp |>.trans h
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Successor.lean:207:theorem C0_projOrd {x : I → Bool} (hx : x ∈ C0 C ho) : Proj (ord I · < o) x = x := by
lean/.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Nobeling/Successor.lean:221:theorem C1_projOrd {x : I → Bool} (hx : x ∈ C1 C ho) : SwapTrue o (Proj (ord I · < o) x) = x := by
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Category/ProfiniteGrp/Limits.lean:147:def proj {P : ProfiniteGrp.{u}} (U : OpenNormalSubgroup P) : P ⟶ (diagram P).obj U :=
lean/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean:51:theorem arcsin_projIcc (x : ℝ) :
lean/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean:181:protected theorem projIcc :
lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:376:  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] N i).compContinuousAlternatingMap f
lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Symmetric.lean:290:theorem _root_.Submodule.IsCompl.projection_isSymmetric_iff
lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Symmetric.lean:305:theorem _root_.Submodule.IsCompl.projection_isSymmetricProjection_iff
lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:530:theorem norm_sq_eq_add_norm_sq_projection (x : E) (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean:264:theorem OrthogonalFamily.sum_projection_of_mem_iSup [Fintype ι] {V : ι → Submodule 𝕜 E}
lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean:284:theorem OrthogonalFamily.projection_directSum_coeAddHom [DecidableEq ι] {V : ι → Submodule 𝕜 E}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:63:  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:80:        (fun x m => (@ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:86:  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
lean/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean:199:protected theorem projIcc {a b : ℝ} (h : a ≤ b) : LipschitzWith 1 (projIcc a b h) :=

 succeeded in 162ms:
variable {ι : Type*} {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸]
  [NormedAlgebra 𝕜 𝔸'] {u : Finset ι} {f : ι → E → 𝔸} {f' : ι → E →L[𝕜] 𝔸} {g : ι → E → 𝔸'}
  {g' : ι → E →L[𝕜] 𝔸'}

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
theorem hasStrictFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (∑ i : Fin l.length, ((l.take i).map x).prod •
        proj l[i] <• ((l.drop (.succ i)).map x).prod) x := by
  have := Fintype.ofFinite ι
  induction l with
  | nil => simp [hasStrictFDerivAt_const]
  | cons a l IH =>
    simp only [List.map_cons, List.prod_cons, ← proj_apply (R := 𝕜) (φ := fun _ : ι ↦ 𝔸) a]
    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
      (by ext; simp [Fin.sum_univ_succ, Finset.mul_sum, mul_assoc, add_comm])

@[fun_prop]
theorem hasStrictFDerivAt_list_prod_finRange' {n : ℕ} {x : Fin n → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ ((List.finRange n).map x).prod)
      (∑ i : Fin n, (((List.finRange n).take i).map x).prod •
        proj i <• (((List.finRange n).drop (.succ i)).map x).prod) x :=
  hasStrictFDerivAt_list_prod'.congr_fderiv <|
    Finset.sum_equiv (finCongr List.length_finRange) (by simp) (by simp)

@[fun_prop]
theorem hasStrictFDerivAt_list_prod_attach' {l : List ι} {x : {i // i ∈ l} → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.attach.map x).prod)
      (∑ i : Fin l.length, ((l.attach.take i).map x).prod •
        proj l.attach[i.cast List.length_attach.symm] <•
          ((l.attach.drop (.succ i)).map x).prod) x := by
  classical exact hasStrictFDerivAt_list_prod'.congr_fderiv <| Eq.symm <|
    Finset.sum_equiv (finCongr List.length_attach.symm) (by simp) (by simp)

@[fun_prop]
theorem hasFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (∑ i : Fin l.length, ((l.take i).map x).prod •
        proj l[i] <• ((l.drop (.succ i)).map x).prod) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_list_prod'.hasFDerivAt

@[fun_prop]
theorem hasFDerivAt_list_prod_finRange' {n : ℕ} {x : Fin n → 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ ((List.finRange n).map x).prod)
      (∑ i : Fin n, (((List.finRange n).take i).map x).prod •
        proj i <• (((List.finRange n).drop (.succ i)).map x).prod) x :=
  hasStrictFDerivAt_list_prod_finRange'.hasFDerivAt

@[fun_prop]
theorem hasFDerivAt_list_prod_attach' {l : List ι} {x : {i // i ∈ l} → 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.attach.map x).prod)
      (∑ i : Fin l.length, ((l.attach.take i).map x).prod •
        (proj l.attach[i.cast List.length_attach.symm]) <•
          ((l.attach.drop (.succ i)).map x).prod) x := by
  classical exact hasStrictFDerivAt_list_prod_attach'.hasFDerivAt

/--
Auxiliary lemma for `hasStrictFDerivAt_multiset_prod`.

For `NormedCommRing 𝔸'`, can rewrite as `Multiset` using `Multiset.prod_coe`.
-/
@[fun_prop]
theorem hasStrictFDerivAt_list_prod [DecidableEq ι] [Finite ι] {l : List ι} {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (l.map fun i ↦ ((l.erase i).map x).prod • proj i).sum x := by
  have := Fintype.ofFinite ι
  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
  conv_rhs => arg 1; arg 2; rw [← List.map_get_finRange l]
  simp only [List.map_map, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange,
    Function.comp_def, ((List.erase_getElem _).map _).prod_eq, List.eraseIdx_eq_take_drop_succ,
    List.map_append, List.prod_append, List.get_eq_getElem, Fin.getElem_fin, Nat.succ_eq_add_one]
  exact Finset.sum_congr rfl fun i _ ↦ by
    ext; simp only [smul_apply, op_smul_eq_smul, smul_eq_mul]; ring

@[fun_prop]
theorem hasStrictFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (u.map x).prod)
      (u.map (fun i ↦ ((u.erase i).map x).prod • proj i)).sum x :=
  have := Fintype.ofFinite ι
  u.inductionOn fun l ↦ by simpa using hasStrictFDerivAt_list_prod

@[fun_prop]
theorem hasFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (u.map x).prod)
      (Multiset.sum (u.map (fun i ↦ ((u.erase i).map x).prod • proj i))) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_multiset_prod.hasFDerivAt

theorem hasStrictFDerivAt_finset_prod [DecidableEq ι] [Finite ι] {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (∏ i ∈ u, · i) (∑ i ∈ u, (∏ j ∈ u.erase i, x j) • proj i) x := by
  simp only [Finset.sum_eq_multiset_sum, Finset.prod_eq_multiset_prod]
  exact hasStrictFDerivAt_multiset_prod

theorem hasFDerivAt_finset_prod [DecidableEq ι] [Finite ι] {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (∏ i ∈ u, · i) (∑ i ∈ u, (∏ j ∈ u.erase i, x j) • proj i) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_finset_prod.hasFDerivAt

section Comp

@[fun_prop]
theorem HasStrictFDerivAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasStrictFDerivAt (f i ·) (f' i) x) :
    HasStrictFDerivAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  -- After https://github.com/leanprover-community/mathlib4/issues/19108, we have to be optimistic with `:)`s; otherwise Lean decides it need to find
  -- `NormedAddCommGroup (List 𝔸)` which is nonsense.
  refine .congr_fderiv (hasStrictFDerivAt_list_prod_finRange'.comp x
    (hasStrictFDerivAt_pi.mpr fun i ↦ h (l.get i) (List.getElem_mem ..)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

/--
Unlike `HasFDerivAt.finset_prod`, supports non-commutative multiply and duplicate elements.
-/
@[fun_prop]
theorem HasFDerivAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasFDerivAt (f i ·) (f' i) x) :
    HasFDerivAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
    (hasFDerivAt_pi.mpr fun i ↦ h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

@[fun_prop]
theorem HasFDerivWithinAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasFDerivWithinAt (f i ·) (f' i) s x) :
    HasFDerivWithinAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) s x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
    (hasFDerivWithinAt_pi.mpr fun i ↦ h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

theorem fderiv_list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, DifferentiableAt 𝕜 (f i ·) x) :
    fderiv 𝕜 (fun x ↦ (l.map (f · x)).prod) x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        (fderiv 𝕜 (fun x ↦ f l[i] x) x) <• ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivAt.list_prod' fun i hi ↦ (h i hi).hasFDerivAt).fderiv

theorem fderivWithin_list_prod' {l : List ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i ∈ l, DifferentiableWithinAt 𝕜 (f i ·) s x) :
    fderivWithin 𝕜 (fun x ↦ (l.map (f · x)).prod) s x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        (fderivWithin 𝕜 (fun x ↦ f l[i] x) s x) <• ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivWithinAt.list_prod' fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]
theorem HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasStrictFDerivAt (g i ·) (g' i) x) :
    HasStrictFDerivAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasStrictFDerivAt_multiset_prod.comp x <|
      hasStrictFDerivAt_pi.mpr fun i ↦ h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

/--
Unlike `HasFDerivAt.finset_prod`, supports duplicate elements.
-/
@[fun_prop]
theorem HasFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasFDerivAt (g i ·) (g' i) x) :
    HasFDerivAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp x <| hasFDerivAt_pi.mpr fun i ↦ h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

@[fun_prop]
theorem HasFDerivWithinAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasFDerivWithinAt (g i ·) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum s x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i ↦ h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

theorem fderiv_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, DifferentiableAt 𝕜 (g i ·) x) :
    fderiv 𝕜 (fun x ↦ (u.map (g · x)).prod) x =
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • fderiv 𝕜 (g i) x).sum :=
  (HasFDerivAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivAt).fderiv

theorem fderivWithin_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (g i ·) s x) :
    fderivWithin 𝕜 (fun x ↦ (u.map (g · x)).prod) s x =
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • fderivWithin 𝕜 (g i) s x).sum :=
  (HasFDerivWithinAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs

theorem HasStrictFDerivAt.finset_prod [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasStrictFDerivAt_finset_prod.comp x <| hasStrictFDerivAt_pi.mpr fun i ↦ hg i i.prop)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

theorem HasFDerivAt.finset_prod [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finset_prod.comp x <| hasFDerivAt_pi.mpr fun i ↦ hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

theorem HasFDerivWithinAt.finset_prod [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) s x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finset_prod.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i ↦ hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

theorem fderiv_finset_prod [DecidableEq ι] {x : E} (hg : ∀ i ∈ u, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (∏ i ∈ u, g i ·) x = ∑ i ∈ u, (∏ j ∈ u.erase i, (g j x)) • fderiv 𝕜 (g i) x :=
  (HasFDerivAt.finset_prod fun i hi ↦ (hg i hi).hasFDerivAt).fderiv

theorem fderivWithin_finset_prod [DecidableEq ι] {x : E} (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hg : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (g i) s x) :
    fderivWithin 𝕜 (∏ i ∈ u, g i ·) s x =
      ∑ i ∈ u, (∏ j ∈ u.erase i, (g j x)) • fderivWithin 𝕜 (g i) s x :=
  (HasFDerivWithinAt.finset_prod fun i hi ↦ (hg i hi).hasFDerivWithinAt).fderivWithin hxs

end Comp

end Prod

section AlgebraInverse

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`.

 succeeded in 199ms:

variable {ι : Type*} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

@[fun_prop]
theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  simp only [hasStrictFDerivAt_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]

@[fun_prop]
theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x := by
  convert HasStrictFDerivAt.fun_sum h; simp

theorem HasFDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) L := by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [ContinuousLinearMap.sum_apply]

theorem HasFDerivAtFilter.sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (∑ i ∈ u, A i) (∑ i ∈ u, A' i) L := by
  convert HasFDerivAtFilter.fun_sum h; simp

  simp [hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_pi]

@[simp]
theorem hasStrictFDerivAt_pi' :
    HasStrictFDerivAt Φ Φ' x ↔ ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ

@[fun_prop]
theorem hasStrictFDerivAt_apply (i : ι) (f : ∀ i, F' i) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) f :=
  (proj (R := 𝕜) (φ := F') i).hasStrictFDerivAt

theorem hasStrictFDerivAt_pi :
    HasStrictFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasStrictFDerivAt (φ i) (φ' i) x :=
  hasStrictFDerivAt_pi'

theorem hasFDerivAtFilter_pi :
    HasFDerivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') L ↔
        ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
  (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).fderiv

@[fun_prop]
theorem HasStrictFDerivAt.clm_apply (hc : HasStrictFDerivAt c c' x)
    (hu : HasStrictFDerivAt u u' x) :
    HasStrictFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMap_apply.hasStrictFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]
theorem HasFDerivWithinAt.clm_apply (hc : HasFDerivWithinAt c c' s x)
    (hu : HasFDerivWithinAt u u' s x) :
    HasFDerivWithinAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp_hasFDerivWithinAt x
    (hc.prodMk hu)

@[fun_prop]
theorem HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x := by

codex
There is a subtle distinction in the route: proving a full “coordinate plus remainder” identity still requires expanding the general `L`-fold product, which is the same cast burden in another form. The likely leanest path is to avoid materializing the remainder and compute the strict derivative of the collapsed two-variable block formula directly.
exec
/bin/bash -lc "sed -n '2680,3300p' expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '1,220p' expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-collapse-route-answer.md" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc 'rg -n "prodAux_framedParamsReg_zero_aux|corner_reindex_mul|prod_framedParamsReg_zero|fromBlocks_blockdiag_idem|framedProd_regSlice_fderiv|corner" lean/DLNFibre/DLN/RLCT/Validate -S' in /home/ubuntu/workspace/deriv-spec
 succeeded in 139ms:
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean:61:/-- **`blockdiag[I_r, 0]` is corner-idempotent**: `blockdiag · blockdiag = blockdiag`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean:62:(`fromBlocks_multiply`: the `(0,0)` corner is `1·1 = 1`, all other blocks have a `0` factor). The
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean:65:theorem fromBlocks_blockdiag_idem {r m₀ m₁ m₂ : Type*} [Fintype r] [DecidableEq r] [Fintype m₁]
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean:319:core object). A gauge layer `C = fromBlocks (1+X) Y Z T` with invertible `(0,0)` corner
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean:54:/-- **Interior layers ARE the block-normal corner** (#95, the (iii) fix). On every strict-interior
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean:55:layer (`0 < s ∧ s+1 < L`), the constructed deepest point equals the corner block `diag(I_r, 0)`
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean:58:frame `(P_s, Q_s)` is a generic rank-normal-form, here `deepestPoint s` is ALREADY the corner, so the
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean:70:frame `P = Q = 1` carries the deepest layer to the block-normal corner — because the layer IS the
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean:71:corner (`deepestPoint_interior_eq_corM`). So in the framed product `∏ Aˢ`, the interior frames cancel
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean:128:/-- `(P_s, Q_s)` carry the deepest layer to the block-normal corner: `P_s·(deepestPoint s)·Q_s = corM`. -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:84:/-- **The corner-block idempotent product** (reindex form). The block-normal corner `fromBlocks 1 0 0 0`
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:86:`reindex eA.symm eB.symm corner * reindex eB.symm eC.symm corner = reindex eA.symm eC.symm corner`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:89:theorem corner_reindex_mul {a b c r : ℕ}
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:131:the block-normal corner `reindex (fromBlocks 1 0 0 0)` (`framedParamsReg_zero`), and the corner is
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:132:idempotent under the chain product, so the running product through `k ≥ 1` layers is again the corner
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:134:(the `[1,0;0,0]·[1,0;0,0] = [1,0;0,0]` corner idempotent) + `submatrix_mul_equiv` (interface cancel). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:135:theorem prodAux_framedParamsReg_zero_aux (H : Fin (L + 1) → ℕ) (r : ℕ)
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:155:      -- IS the corner at the running widths (`framedParamsReg_zero` then `cases e1; cases e2` collapses the
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:157:      -- the Eq.mpr-cast layer = the corner at the running widths (PROBE-proven: `framedParamsReg_zero`
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:177:        -- accumulator is `prodAux 0 = 1`; `1 * corner = corner` (`prodAux 0` reduces, then `one_mul`).
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:180:        exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:185:gauge-sliced product at the deepest gauge slot is the block-normal corner: `prod (framedParamsReg 0) =
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:194:  have h := prodAux_framedParamsReg_zero_aux H r hr hL L (Nat.lt_succ_self L) hL
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:197:  -- `⟨L, _⟩ = Fin.last L` (Fin.ext); the two corner index-forms agree.
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:8:(#156, `framedProd_regSlice_fderiv`) and the assembly (#157, `deepestEPivot_regSlice_fderiv_id`),
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:21:  layer (X,Z at `firstLayer`; Y at `lastLayer`), so all INTERIOR layers are the constant corner.
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:22:- **Product collapse** (`framedProd_regSlice_fderiv`): the only varying factors are `C_first`/`C_last`;
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:23:  the idempotent corner sandwich keeps `(0,0)→δX`, `(0,1)→δY_last`, `(1,0)→δZ_first`, `(1,1)→0`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:185:/-! ## The framed-layer values on the regular slice (interiors are the constant corner) -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:187:/-- An INTERIOR layer (`s ≠ firstLayer`, `s ≠ lastLayer`) of the regular slice is the constant corner
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:416:`0` is `id` — the idempotent-sandwich `dP|_0 = Σ_s corner·δC_s·corner` with the gauge slot held at `0`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:435:  -- idempotent-sandwich: `d(prod(framedParamsReg (r0,0)))|_0 = Σ_s corner·δC_s·corner` keeps the
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:490:  -- At the origin slot, `∏(framedParamsReg 0)` is the reindexed corner `fromBlocks 1 0 0 0`
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:491:  -- (`prod_framedParamsReg_zero`); the outer `reindex` in `P` cancels it, so `P = fromBlocks 1 0 0 0`.
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:493:  -- The matrix `P` defining the coordinates is the cancelled corner.

 succeeded in 164ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading additional input from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/deriv-spec
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019ef5ae-a927-71f0-8505-0333e9e40c20
--------
user
Lean4/Mathlib v4.29. Follow-up on a chain-product strict-derivative collapse. I have PROVEN (green) all of:
- alignment cancel: at gauge-zero slice, readX(r0,0) s = 0 unless s=firstLayer (then = r0 at X-pivot coord); readZ similarly s=firstLayer; readY s=lastLayer. So the framed layer C_s(r0) = reindex(fromBlocks (1+X_s) Y_s Z_s 0) is CONSTANT (= corner = reindex(fromBlocks 1 0 0 0)) for every INTERIOR layer s ∉ {firstLayer,lastLayer}; only C_first and C_last vary with r0.
- prodAux_framedParamsReg_zero_aux: at r0=0, prodAux k = corner (reindexed) for 1≤k≤L.
- corner_reindex_mul: corner*corner=corner.
- A banked EXISTENCE strict-deriv per entry (opaque D).

TARGET: HasStrictFDerivAt (fun r0 => (P.toBlocks11 - 1) a b) (proj idx_X) 0 where P = reindex(prod(framedParamsReg(r0,0))), idx_X = regPivotFinEquiv.symm (inl(a,b)); plus the toBlocks12→Y_last and toBlocks21→Z_first analogues.

I'm choosing between:
(I) Define explicit `prodAuxEntryDeriv` (recursive Leibniz value) mirroring the existence proof, prove its strict-deriv, THEN prove by induction `prodAuxEntryDeriv (framedParamsReg·) 0 = the corner-sandwich Σ_s prefix·δC_s·suffix`, then read blocks. Concern: the corner-collapse induction is itself heavy + dependent-Fin casts.
(II) EXPLOIT interiors-constant: rewrite prod = (prefix corners)·C_first·(mid corners)·C_last·(suffix corners) so only ≤2 factors vary, differentiate THAT. Concern: the rewrite of prodAux into this factored form has its own cast pain, and firstLayer/lastLayer positions (0 and L-1) interact with the prodAux fold direction.
(III) Per-ENTRY directly: the coordinate function r0 ↦ (P11-1) a b. Since interiors constant and the corner kills cross terms, claim this entry function equals EXACTLY a single affine coordinate r0 ↦ r0 idx_X (NO higher-order terms, because the surviving sandwich corner·δ·corner is degree-1 and the higher-order product terms vanish on the corner blocks). If TRUE, the entry function is literally LINEAR (= r0 idx_X + const), and HasStrictFDerivAt is trivial via HasStrictFDerivAt of a coordinate projection + congr. IS the entry EXACTLY affine in r0 (not just to first order)? Consider L=2: P = C_0(r0)·C_1(r0), both vary (first=0,last=1). (P11) = (1+X_0)(1+X_1)_block... = block11 of product. X_0 routes the X-pivot, Y_1 the Y-pivot, etc. Is (C_0·C_1).toBlocks11 - 1 EXACTLY linear in r0? Compute: C_0=[[1+X0,Y0],[Z0,0]] but Y0=0 (Y only at last=1), Z0=routed. C_1=[[1+X1,Y1],[Z1,0]] but X1: X routes to first=0 only, so X1=0; Z1: Z to first only, so Z1=0; Y1=routed. So C_0=[[1+X0,0],[Z0,0]], C_1=[[1,Y1],[0,0]]. Product block11 = (1+X0)*1 + 0*0 = 1+X0. So P11-1 = X0 = r0 at X-pivot. EXACTLY linear! block12 = (1+X0)Y1 = Y1 + X0Y1 — NOT linear (X0Y1 cross term)! 

So (III) FAILS for block12 (the cross term X0·Y1 is degree 2). So I DO need the derivative (first-order), where X0Y1 contributes 0 at r0=0. Given block12 = Y1 + X0·Y1, its strict deriv at 0 is δY1 (the X0·Y1 term is o(r0)). 

So the real task per block: entry = (linear in r0) + (genuinely higher order vanishing at 0). The linear part is the surviving corner-sandwich. QUESTION: given this explicit small structure (each entry = explicit polynomial: block11=X0(+products that vanish), block12=Y_last+cross, block21=Z_first+cross), what's the LEANEST Lean route? Is there a way to write each entry function as `coordinate + remainder` and use HasStrictFDerivAt.add where remainder has deriv 0 (via it being a product of two functions each 0 at 0, hasStrictFDerivAt of f*g at 0 with f0=0,g0=0 gives deriv 0)? Specifically for general L: the product of L corner-or-varying factors — the entry is multilinear-ish. Recommend the cleanest GENERAL-L route and give the key lemma statements + Mathlib v4.29 deriv API (HasStrictFDerivAt.mul, .add, mul_zero deriv tricks). Keep dependent-Fin casts minimal.
codex
I’ll inspect the local Lean code and pinned Mathlib API so the recommendation lines up with the actual definitions and v4.29 names, rather than guessing from memory.
exec
/bin/bash -lc "rg --files -g 'CLAUDE.md' -g 'lake-manifest.json' -g 'lakefile.lean' -g '*.lean'" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc ls in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc 'rg -n "prodAux|framedParamsReg|readX|readY|readZ|corner_reindex_mul|prodAuxEntryDeriv|HasStrictFDerivAt" -S .' in /home/ubuntu/workspace/deriv-spec
 succeeded in 107ms:
AGENTS.md
CLAUDE.md
README.md
ROADMAP.md
TEMPLATE.md
docs
expeditions
lean
paper-sources
theory
threads

 succeeded in 122ms:
lean/DLNFibre.lean
lean/lake-manifest.json
lean/DLNFibre/Core/BaseChange.lean
lean/DLNFibre/Core/CThetaDropM.lean
lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean
lean/DLNFibre/Core/IntervalModule.lean
lean/DLNFibre/Core/PolynomialDimension.lean
lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean
lean/DLNFibre/Core/OrbitKostant.lean
lean/DLNFibre/Core/OrbitClosure.lean
lean/DLNFibre/Core/VoigtDischarge.lean
lean/DLNFibre/Core/MeasureTheory/PolynomialZeroSet.lean
lean/DLNFibre/Core/Setup.lean
lean/DLNFibre/Core/OrbitDifferential.lean
lean/DLNFibre/Core/NoetherMonicPositioning.lean
lean/DLNFibre/Core/OrbitTangentCotangent.lean
lean/DLNFibre/Core/OrbitSmooth.lean
lean/DLNFibre/Core/OrbitDifferentialRank.lean
lean/DLNFibre/Core/CThetaGeometric.lean
lean/DLNFibre/Core/DeformationExt.lean
lean/DLNFibre/Core/AffineNoetherRank.lean
lean/DLNFibre/Core/OrbitLinearCodim.lean
lean/DLNFibre/Core/CThetaExplicit.lean
lean/DLNFibre/Core/Submult.lean
lean/DLNFibre/Core/JacobianTrdeg.lean
lean/DLNFibre/Core/BoxMoveDegeneration.lean
lean/DLNFibre/Core/Basic.lean
lean/DLNFibre/Core/BoxMoveGeneration.lean
lean/DLNFibre/Core/CThetaValue.lean
lean/DLNFibre/Core/PolynomialCurveLimit.lean
lean/DLNFibre/Core/CThetaThetaBridge.lean
lean/DLNFibre/Core/SmoothPointRegular.lean
lean/DLNFibre/Core/OrbitImageDim.lean
lean/DLNFibre/Core/BoxMoveGeneral.lean
lean/DLNFibre/Core/Barcode.lean
lean/DLNFibre/Core/CThetaQIP.lean
lean/DLNFibre/Core/MatrixKaehler.lean
lean/DLNFibre/Core/IntegralDimension.lean
lean/DLNFibre/Core/Gabriel.lean
lean/DLNFibre/Core/OrbitVariety.lean
lean/DLNFibre/Core/NullstellensatzCodim.lean
lean/DLNFibre/Core/RankLocusClosed.lean
lean/DLNFibre/Core/CTheta.lean
lean/DLNFibre/Core/AffineDomainDimension.lean
lean/DLNFibre/Core/CThetaQIPConverse.lean
lean/DLNFibre/Core/OrbitCodim.lean
lean/DLNFibre/Core/Matrix/RankNormalForm.lean
lean/DLNFibre/Core/RankPattern.lean
lean/DLNFibre/Core/CotangentJacobian.lean
lean/DLNFibre/Core/OrbitPullbackDim.lean
lean/DLNFibre/Core/Orbit.lean
lean/DLNFibre/DLN/Basic.lean
lean/DLNFibre/DLN/RLCT/BGEngine.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Spectator.lean
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1G5.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1SmoothBlock.lean
lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean
lean/DLNFibre/DLN/RLCT/Foundations/Lambda.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean
lean/DLNFibre/DLN/RLCT/Foundations/DeepestSplitHaar.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Transport.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1G5Charts.lean
lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean
lean/DLNFibre/DLN/RLCT/Foundations/CoreShearMP.lean
lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean
lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean
lean/DLNFibre/DLN/RLCT/Validate/Case111.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean
lean/DLNFibre/DLN/RLCT/Validate/ScratchAlign.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean
lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean
lean/DLNFibre/DLN/RLCT/Validate/Case212.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean
lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Block.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Value.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean
lean/DLNFibre/DLN/RLCT/Validate/Case111Bridge.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean
lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean
lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean
lean/DLNFibre/DLN/RLCT/AxCheck.lean
lean/DLNFibre/DLN/RLCT/Skeleton.lean
lean/CLAUDE.md
CLAUDE.md
expeditions/2026-06-18-voigt-discharge/threads/33-A1-kahler-trdeg-api/probes/KahlerTrdegProbe.lean
expeditions/2026-06-18-voigt-discharge/threads/33-A1-kahler-trdeg-api/probes/RingKrullTrdegProbe.lean

 succeeded in 186ms:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:11:      HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL (r0, 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:16:`hasStrictFDerivAt_prod_entry` returns `∃ D, HasStrictFDerivAt (prod entry) D x` — D is an OPAQUE
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:23:    -- goal: HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:31:Output coord = `(P.toBlocks₁₁ − 1) a b` where `P = reindex (prod (framedParamsReg (r0,0)))`. By the #91
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:35:`(framedParamsReg (r0,0)) reads readX_first (r0) a b = regGaugeSlotEquiv (r0,0) ⟨0, inl(inl(a,b))⟩`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:46:    -- d(prod (framedParamsReg (r0,0)))|_0 = Σ_s (corner prefix) · δC_s · (corner suffix), and the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:49:      HasFDerivAt (fun r0 => (reindex (prod (framedParamsReg (r0,0)))) i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:54:1. `prod_framedParamsReg_zero` (banked): at r0=0, `prod (framedParamsReg 0) = reindex (fromBlocks 1 0 0 0)`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:56:2. The product derivative at 0 (Leibniz, cobuild's `hasStrictFDerivAt_prodAux_entry` VALUE, or a direct
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:57:   `prodAux` induction): `dP|_0 = Σ_s prodAux_prefix(0) · δC_s · prodAux_suffix(0)`. The prefix/suffix
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:58:   AT r0=0 are the idempotent corner (by `prodAux_framedParamsReg_zero_aux` — the partial products at 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:62:   only for the FIRST. The `fromBlocks_multiply` / `corner_reindex_mul` kernels (banked in
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:64:4. `δC_s = framedLayer` derivative = `fromBlocks (δreadX) (δreadY) (δreadZ) 0` (T=0), and readX/Y/Z are
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:65:   LINEAR in r0 (regGaugeSlotEquiv is a CLE — `regGaugeSlotCLE`), so `δreadX_s = readX_s` etc. (a linear
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:66:   map's derivative is itself). So `Σ_s δX_s = Σ_s readX_s(r0)`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:84:- `prod_framedParamsReg_zero`, `prodAux_framedParamsReg_zero_aux`, `corner_reindex_mul`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:86:- `regGaugeSlotCLE` (DeepestFramedProduct) — readX/Y/Z linearity (δread = read).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:87:- `hasStrictFDerivAt_prodAux_entry` (cobuild @2bf7065) — IF a Leibniz value is wanted; else direct induction.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:96:- The Σ_s collapse to δX_first needs `readX_s (r0,0) = 0` for s ≠ 0 (interior X in the GAUGE slot, held
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:98:  entries are in the gauge half (the complement), and gauge = 0. STATE this as `readX_interior_zero`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:99:- If the per-coordinate derivative-of-(P11−1) doesn't directly give `Σ_s readX_s`, fall back to the
./lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean:33:def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
./lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean:39:      refine (prodAux H A k hk') * ?_
./lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean:50:  prodAux H A L (Nat.lt_succ_self L)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean:63:step-fact of the deepest-product idempotent fold (the `_base` value-fold's `prodAux` induction — the
./lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:76:  -- `simp` reduces the layer product `prodAux` (clearing its recursive casts) to `1 * A 0 * A 1`;
./lean/DLNFibre/DLN/RLCT/Validate/Case111.lean:79:  simp [prodAux]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:16:gauge-sliced tuple `C : Params H` — no new fold; `prod`/`prodAux` are reused.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:38:function (defeq), giving `ContDiff` of `regGaugeSlotEquiv` (hence of the `readX/Y/Z` entries) via
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:62:/-- Each `readX` entry is `ContDiff ⊤` (a coordinate of the `ContDiff` gauge read). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:63:theorem contDiff_readX_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:65:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readX H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:66:  simp only [readX, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:69:/-- Each `readY` entry is `ContDiff ⊤`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:70:theorem contDiff_readY_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:73:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readY H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:74:  simp only [readY, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:77:/-- Each `readZ` entry is `ContDiff ⊤`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:78:theorem contDiff_readZ_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:81:    ContDiff ℝ (⊤ : ℕ∞) (fun p => readZ H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:82:  simp only [readZ, Matrix.of_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:102:`readX/readY/readZ`) and the reduced core `T_s` (read off the core slot via `paramsEquivFlat (deepestM)`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:111:      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:112:      (readZ H r hr hL (q.1, q.2.2) s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:120:`Fin nReg` pack convention (the open obstruction), only on the gauge read `readX/Y/Z`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:121:noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:126:      (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:129:/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:132:theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:134:    framedParamsReg H r hr hL 0 s
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:138:  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:139:    readZ_zero H r hr hL s, add_zero]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:141:/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:142:`fromBlocks (1+X) Y Z 0` block entry (reindexed), i.e. `1+readX` / `readY` / `readZ` / `0`, each
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:144:theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:147:    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:149:  have hentry : (fun p => framedParamsReg H r hr hL p s i j)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:150:      = fun p => Matrix.fromBlocks (1 + readX H r hr hL p s) (readY H r hr hL p s)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:151:          (readZ H r hr hL p s) (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)

 succeeded in 291ms:
 succeeded in 0ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:149:irreducible_def fderivWithin (f : E → F) (s : Set E) (x : E) : E →L[𝕜] F :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:158:irreducible_def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:317:protected theorem HasStrictFDerivAt.hasFDerivAt (hf : HasStrictFDerivAt f f' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:405:protected theorem HasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:412:theorem fderiv_eq
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:477:  h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:519:theorem fderivWithin_eq_fderiv

codex
I’m going to give the route as a staged API, not a giant theorem. The important design choice is to compute values by asking Lean for the `fderiv` of a function already proved strictly differentiable, then rewrite that `fderiv` to the explicit formula by uniqueness. That keeps casts local to the existing `prodAux` recursion pattern.
exec
/bin/bash -lc "sed -n '232,246p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "rg -n \"namespace ContinuousLinearMap|def proj|theorem proj_apply|def pi \\(|theorem pi_apply|def prod\" lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module -S" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '160,190p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:

/-! ### Derivative of the product of two functions -/

open scoped RightActions


variable {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
    (hb : HasStrictFDerivAt b b' x) :
    HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x) :
    HasFDerivWithinAt (a * b) (a x • b' + a' <• b x) s x := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp_hasFDerivWithinAt x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]

exec
/bin/bash -lc "sed -n '400,418p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:

theorem DifferentiableOn.eventually_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  (eventually_eventually_nhds.2 hs).mono fun _ => h.differentiableAt

protected theorem HasFDerivAt.fderiv
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : HasFDerivAt f f' x) :
    fderiv 𝕜 f x = f' := by
  ext
  rw [h.unique h.differentiableAt.hasFDerivAt]

theorem fderiv_eq
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    {f' : E → E →L[𝕜] F} (h : ∀ x, HasFDerivAt f (f' x) x) : fderiv 𝕜 f = f' :=
  funext fun x => (h x).fderiv

protected theorem HasFDerivWithinAt.fderivWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]

 succeeded in 101ms:
 succeeded in 106ms:
web search: 
web search: site:leanprover-community.github.io/mathlib4_docs Mathlib Analysis Calculus FDeriv Prod hasStrictFDerivAt_pi'' v4.29
web search: 
web search: github mathlib4 v4.29.0 HasStrictFDerivAt.fun_sum
web search: 
web search: https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.29.0/Mathlib/Analysis/Calculus/FDeriv/Prod.lean
web search: 
web search: github.com/leanprover-community/mathlib4/blob/v4.29.0/Mathlib/Analysis/Calculus/FDeriv/Prod.lean hasStrictFDerivAt_pi
web search: 
web search: https://github.com/leanprover-community/mathlib4/blob/v4.29.0/Mathlib/Analysis/Calculus/FDeriv/Prod.lean
codex
One place where I would add a named lemma is the packing cancellation, independent of calculus. Once `regGaugeIdxSplit_boundary_apply` is proved, all later `readX/readY/readZ` derivative/value lemmas should reduce with `simp`; without that lemma, every coordinate proof reopens the opaque `Set.range` split.
exec
/bin/bash -lc "rg -n \"sumCompl|ofInjective|Set\\.sumCompl\" lean/.lake/packages/mathlib/Mathlib/Data/Equiv lean/.lake/packages/mathlib/Mathlib/Logic lean/.lake/packages/mathlib/Mathlib/Order -S" in /home/ubuntu/workspace/deriv-spec
 exited 2 in 0ms:
rg: lean/.lake/packages/mathlib/Mathlib/Data/Equiv: No such file or directory (os error 2)
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Set.lean:113:  { Equiv.ofInjective _ f.injective with
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Set.lean:134:  toEquiv := Equiv.ofInjective f h_mono.injective
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:40:  toEquiv := .sumCompl (r · x)
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:49:theorem sumLexComplLeft_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:53:theorem sumLexComplLeft_symm_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:60:  toEquiv := (Equiv.sumComm _ _).trans <| .sumCompl (r x)
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:69:theorem sumLexComplRight_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:73:theorem sumLexComplRight_symm_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:18:* `Equiv.ofInjective`: an injective function is (noncomputably) equivalent to its range.
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:293:See also `Equiv.sumCompl`. -/
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:294:protected def sumCompl {α} (s : Set α) [DecidablePred (· ∈ s)] : s ⊕ (sᶜ : Set α) ≃ α :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:295:  Equiv.sumCompl (· ∈ s)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:298:theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:299:    Equiv.Set.sumCompl s (Sum.inl x) = x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:303:theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : (sᶜ : Set α)) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:304:    Equiv.Set.sumCompl s (Sum.inr x) = x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:307:theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:308:    (hx : x ∈ s) : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:309:  sumCompl_symm_apply_of_pos hx
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:311:theorem sumCompl_symm_apply_of_notMem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:312:    (hx : x ∉ s) : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:313:  sumCompl_symm_apply_of_neg hx
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:316:theorem sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· ∈ s)] (x : s) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:317:    (Equiv.Set.sumCompl s).symm x = Sum.inl x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:318:  sumCompl_symm_apply_pos x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:321:theorem sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:322:    (x : (sᶜ : Set α)) : (Equiv.Set.sumCompl s).symm x = Sum.inr x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:323:  sumCompl_symm_apply_neg x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:390:        α ≃ s ⊕ (sᶜ : Set α) := (Set.sumCompl s).symm
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:392:        _ ≃ β := Set.sumCompl t)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:394:      simp only [Sum.map_inl, trans_apply, sumCongr_apply, Set.sumCompl_apply_inl,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:395:        Set.sumCompl_symm_apply, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:399:    · simp only [Set.sumCompl_symm_apply_of_mem hx, ← e.prop ⟨x, hx⟩, Sum.map_inl, sumCongr_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:400:        trans_apply, Set.sumCompl_apply_inl, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:401:    · simp only [Set.sumCompl_symm_apply_of_notMem hx, Sum.map_inr, subtypeEquiv_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:402:        Set.sumCompl_apply_inr, trans_apply, sumCongr_apply, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:405:      simp only [Sum.map_inr, subtypeEquiv_apply, Set.sumCompl_apply_inr, Function.comp_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:407:        Set.sumCompl_symm_apply_compl]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:534:noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ range f :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:537:theorem apply_ofInjective_symm {α β} {f : α → β} (hf : Injective f) (b : range f) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:538:    f ((ofInjective f hf).symm b) = b :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:539:  Subtype.ext_iff.1 <| (ofInjective f hf).apply_symm_apply b
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:542:theorem ofInjective_symm_apply {α β} {f : α → β} (hf : Injective f) (a : α) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:543:    (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a := by
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:544:  apply (ofInjective f hf).injective
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:547:theorem coe_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:548:    ((ofInjective f hf).symm : range f → α) = rangeSplitting f := by
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:554:theorem self_comp_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:555:    f ∘ (ofInjective f hf).symm = Subtype.val :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:556:  funext fun x => apply_ofInjective_symm hf x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:558:theorem ofLeftInverse_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : Nonempty α → β → α)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:561:      ofInjective f ((isEmpty_or_nonempty α).elim (fun _ _ _ _ => Subsingleton.elim _ _)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:566:theorem ofLeftInverse'_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : β → α)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:567:    (hf : LeftInverse f_inv f) : ofLeftInverse' f f_inv hf = ofInjective f hf.injective := by
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:40:`Equiv.ofLeftInverse` instead. This is the computable version of `Equiv.ofInjective`.
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:57:theorem Function.Embedding.toEquivRange_eq_ofInjective :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:58:    f.toEquivRange = Equiv.ofInjective f f.injective := by
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:119:  rw [sumCompl_symm_apply_of_pos hx, Sum.map_inl, sumCompl_apply_inl]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:130:  rw [sumCompl_symm_apply_of_neg hx, Sum.map_inr, sumCompl_apply_inr]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:56:  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:64:  permCongr (sumCompl p) (sumCongr ep en)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:549:inverse, or `Equiv.ofInjective` in the general case.
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:253:section sumCompl
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:260:that are not necessarily `IsCompl p q`. See also `Equiv.Set.sumCompl` for a version on sets. -/
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:261:def sumCompl {α : Type*} (p : α → Prop) [DecidablePred p] :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:274:theorem sumCompl_apply_inl {α} {p : α → Prop} [DecidablePred p] (x : { a // p a }) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:275:    sumCompl p (Sum.inl x) = x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:279:theorem sumCompl_apply_inr {α} {p : α → Prop} [DecidablePred p] (x : { a // ¬p a }) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:280:    sumCompl p (Sum.inr x) = x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:284:theorem sumCompl_symm_apply_of_pos {α} {p : α → Prop} [DecidablePred p] {a : α} (h : p a) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:285:    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:289:theorem sumCompl_symm_apply_of_neg {α} {p : α → Prop} [DecidablePred p] {a : α} (h : ¬p a) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:290:    (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:294:alias sumCompl_apply_symm_of_pos := sumCompl_symm_apply_of_pos
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:296:alias sumCompl_apply_symm_of_neg := sumCompl_symm_apply_of_neg
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:299:theorem sumCompl_symm_apply_pos {α} {p : α → Prop} [DecidablePred p] (x : {x // p x}) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:300:    (sumCompl p).symm x = Sum.inl x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:301:  sumCompl_symm_apply_of_pos x.2
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:304:theorem sumCompl_symm_apply_neg {α} {p : α → Prop} [DecidablePred p] (x : {x // ¬ p x}) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:305:    (sumCompl p).symm x = Sum.inr x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:306:  sumCompl_symm_apply_of_neg x.2
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:308:end sumCompl
lean/.lake/packages/mathlib/Mathlib/Order/Partition/Equipartition.lean:118:  let f := (Equiv.sumCompl _).symm.trans ((el.sumCongr es).trans finSumFinEquiv)
lean/.lake/packages/mathlib/Mathlib/Logic/Embedding/Set.lean:92:See also `Equiv.sumCompl`, for when `IsCompl p q`. -/
lean/.lake/packages/mathlib/Mathlib/Logic/Small/Basic.lean:31:  small_map (Equiv.ofInjective f hf)
lean/.lake/packages/mathlib/Mathlib/Logic/Denumerable.lean:320:    Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).injective
lean/.lake/packages/mathlib/Mathlib/Order/SuccPred/LinearLocallyFinite.lean:371:  toEquiv := Equiv.ofInjective _ injective_toZ
lean/.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:418:  RelIso.symm ⟨(Equiv.ofInjective f f.injective).trans
lean/.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:423:  Equiv.apply_ofInjective_symm f.injective _
lean/.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:427:  Equiv.ofInjective_symm_apply f.injective _

exec
/bin/bash -lc 'rg -n "def ofInjective|theorem ofInjective|ofInjective_apply|sumCompl_apply|sumCompl_symm" lean/.lake/packages/mathlib/Mathlib -S' in /home/ubuntu/workspace/deriv-spec
 succeeded in 182ms:
lean/.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Arithmetic.lean:864:  refine ⟨h, ?_⟩; rintro ⟨x, hx⟩; simp [h, Set.sumCompl_symm_apply_of_mem, hx]
lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Ker.lean:187:noncomputable def ofInjective {f : G →* N} (hf : Function.Injective f) : G ≃* f.range :=
lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Ker.lean:194:theorem ofInjective_apply {f : G →* N} (hf : Function.Injective f) {x : G} :
lean/.lake/packages/mathlib/Mathlib/Algebra/Lie/Subalgebra.lean:771:noncomputable def ofInjective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) : L₁ ≃ₗ⁅R⁆ f.range :=
lean/.lake/packages/mathlib/Mathlib/Algebra/Lie/Subalgebra.lean:776:theorem ofInjective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) (x : L₁) :
lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Basis.lean:42:    Submodule.restrictScalarsEquiv_apply, LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
lean/.lake/packages/mathlib/Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:544:noncomputable def ofInjective' (f : F) (hf : Function.Injective f) :
lean/.lake/packages/mathlib/Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:549:theorem ofInjective'_apply (f : F) (hf : Function.Injective f) (x : A) :
lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Basic.lean:722:          Equiv.Set.sumCompl_apply_inl]
lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:633:noncomputable def ofInjective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:637:theorem ofInjective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) :
lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:642:noncomputable def ofInjectiveField {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:298:theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:303:theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : (sᶜ : Set α)) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:307:theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:309:  sumCompl_symm_apply_of_pos hx
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:311:theorem sumCompl_symm_apply_of_notMem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:313:  sumCompl_symm_apply_of_neg hx
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:316:theorem sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· ∈ s)] (x : s) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:318:  sumCompl_symm_apply_pos x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:321:theorem sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:323:  sumCompl_symm_apply_neg x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:394:      simp only [Sum.map_inl, trans_apply, sumCongr_apply, Set.sumCompl_apply_inl,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:395:        Set.sumCompl_symm_apply, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:399:    · simp only [Set.sumCompl_symm_apply_of_mem hx, ← e.prop ⟨x, hx⟩, Sum.map_inl, sumCongr_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:400:        trans_apply, Set.sumCompl_apply_inl, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:401:    · simp only [Set.sumCompl_symm_apply_of_notMem hx, Sum.map_inr, subtypeEquiv_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:402:        Set.sumCompl_apply_inr, trans_apply, sumCongr_apply, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:405:      simp only [Sum.map_inr, subtypeEquiv_apply, Set.sumCompl_apply_inr, Function.comp_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:407:        Set.sumCompl_symm_apply_compl]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:534:noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ range f :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:542:theorem ofInjective_symm_apply {α β} {f : α → β} (hf : Injective f) (a : α) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:119:  rw [sumCompl_symm_apply_of_pos hx, Sum.map_inl, sumCompl_apply_inl]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:130:  rw [sumCompl_symm_apply_of_neg hx, Sum.map_inr, sumCompl_apply_inr]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:274:theorem sumCompl_apply_inl {α} {p : α → Prop} [DecidablePred p] (x : { a // p a }) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:279:theorem sumCompl_apply_inr {α} {p : α → Prop} [DecidablePred p] (x : { a // ¬p a }) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:284:theorem sumCompl_symm_apply_of_pos {α} {p : α → Prop} [DecidablePred p] {a : α} (h : p a) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:289:theorem sumCompl_symm_apply_of_neg {α} {p : α → Prop} [DecidablePred p] {a : α} (h : ¬p a) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:294:alias sumCompl_apply_symm_of_pos := sumCompl_symm_apply_of_pos
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:296:alias sumCompl_apply_symm_of_neg := sumCompl_symm_apply_of_neg
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:299:theorem sumCompl_symm_apply_pos {α} {p : α → Prop} [DecidablePred p] (x : {x // p x}) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:301:  sumCompl_symm_apply_of_pos x.2
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:304:theorem sumCompl_symm_apply_neg {α} {p : α → Prop} [DecidablePred p] (x : {x // ¬ p x}) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:306:  sumCompl_symm_apply_of_neg x.2

exec
/bin/bash -lc "rg -n \"HasStrictFDerivAt\\.congr|HasFDerivAt\\.congr|congr_fderiv\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv -S" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "rg -n \"congr_fderiv|congr.*fderiv|EventuallyEq\\.fderiv|fderiv_eq_of\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus -S" in /home/ubuntu/workspace/deriv-spec
 succeeded in 166ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:114:theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:118:theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:121:theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:125:theorem HasStrictFDerivAt.congr_of_eventuallyEq (h : HasStrictFDerivAt f f' x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:174:theorem HasFDerivAt.congr_of_eventuallyEq (h : HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:57:    refine this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:77:    exact this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:96:    exact this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:206:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:215:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:224:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:405:    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:413:  hasStrictFDerivAt_list_prod'.congr_fderiv <|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:422:  classical exact hasStrictFDerivAt_list_prod'.congr_fderiv <| Eq.symm <|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:458:  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:501:  refine .congr_fderiv (hasStrictFDerivAt_list_prod_finRange'.comp x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:517:  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:530:  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:556:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:570:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:580:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:600:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:607:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:614:  simpa [← Finset.prod_attach u] using .congr_fderiv

 succeeded in 174ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:113:    apply Filter.EventuallyEq.fderivWithin_eq A
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:124:      (fderivWithin_eventually_congr_set h).fderivWithin_eq_of_nhds
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:394:  exact (h.fderivWithin hs.uniqueDiffOn).congr (fun x hx ↦ (fderivWithin_of_isOpen hs hx).symm)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:518:    · rw [Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ 0)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:405:    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:413:  hasStrictFDerivAt_list_prod'.congr_fderiv <|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:422:  classical exact hasStrictFDerivAt_list_prod'.congr_fderiv <| Eq.symm <|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:458:  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:501:  refine .congr_fderiv (hasStrictFDerivAt_list_prod_finRange'.comp x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:517:  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:530:  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:556:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:570:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:580:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:600:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:607:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:614:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:94:theorem fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:114:theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:118:theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:121:theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:218:  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:221:theorem Filter.EventuallyEq.fderivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:226:theorem Filter.EventuallyEq.fderivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:230:theorem Filter.EventuallyEq.fderivWithin_eq_of_insert (hs : f₁ =ᶠ[𝓝[insert x s] x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:232:  apply Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:235:theorem Filter.EventuallyEq.fderivWithin' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:239:      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:242:protected theorem Filter.EventuallyEq.fderivWithin (hs : f₁ =ᶠ[𝓝[s] x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:246:theorem Filter.EventuallyEq.fderivWithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:258:theorem Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:261:protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:57:    refine this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:77:    exact this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:96:    exact this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:206:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:215:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:224:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:323:  rwa [Filter.EventuallyEq.fderiv_eq]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:603:  h.hasStrictFDerivAt.congr_fderiv <| congr_arg _ h'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:606:  HasFDerivAt.congr_fderiv h <| congr_arg _ h'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:610:  HasFDerivWithinAt.congr_fderiv h <| congr_arg _ h'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:646:  rwa [Filter.EventuallyEq.fderiv_eq]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Star.lean:56:  · exact DFunLike.congr_fun (fderivWithin_star hxs) _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Star.lean:60:  DFunLike.congr_fun fderiv_star _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:161:    refine ((hp.fderivWithin m hm x hx).congr' (hpq m hm.le).symm hx).congr_fderiv ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:930:    apply Filter.EventuallyEq.fderiv_eq
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:866:  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:880:    contDiffOn_congr fun x hx ↦ fderivWithin_of_isOpen hs hx]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:893:  (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:351:  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:633:    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:637:    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx

codex
`HasStrictFDerivAt.congr_fderiv` and `HasFDerivAt.congr_fderiv` do exist in v4.29, but they are only for replacing the derivative map after you have proved an equality of CLMs. They will not extract the value from an existential derivative by themselves.
exec
/bin/bash -lc "sed -n '108,122p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl

theorem Filter.EventuallyEq.hasStrictFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
    HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x :=
  h.prodMap_nhds h |>.hasFDerivAtFilter_iff h'

theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
    HasStrictFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
    HasFDerivWithinAt f g' s x :=

exec
/bin/bash -lc "sed -n '185,200p' lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '35,48p' lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 287ms:

theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The projections from a family of topological modules are continuous linear maps. -/
def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
  ⟨LinearMap.proj i, continuous_apply _⟩

@[simp]
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl

@[simp]
theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl


 succeeded in 176ms:
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

/-- The Cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    M₁ →L[R] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R] M₂).prod f₂, f₁.2.prodMk f₂.2⟩

@[simp, norm_cast]
theorem coe_prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    (f₁.prod f₂ : M₁ →ₗ[R] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl


codex
**Recommendation:** use an **A-lite + uniqueness** route. Do not prove the closed-form `Σ_{s<k} corner · δC_s · corner` as the primary theorem, and do not use `littleO` directly. Instead, expose the recursive derivative that your current existential proof already constructs, then specialize/evaluate it at the corner.

The existential lemma is a dead end for values: uniqueness only says an existing derivative equals another derivative after you prove the other derivative exists.

Core lemma:

```lean
noncomputable def prodAuxEntryDeriv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ s i j, X →L[ℝ] ℝ) :
    (k : ℕ) → (hk : k < L + 1) →
      Fin (H 0) → Fin (H ⟨k, hk⟩) → X →L[ℝ] ℝ
| 0, hk, i, j => 0
| k + 1, hk, i, j => by
    have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
    have hkL : k < L := Nat.lt_of_succ_lt_succ hk
    have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
      apply Fin.ext; simp [Fin.castSucc]
    have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
      apply Fin.ext; simp [Fin.succ]
    exact ∑ m : Fin (H ⟨k, hk'⟩),
      (prodAux H (g x) k hk' i m) •
          g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
      +
      (((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) •
          prodAuxEntryDeriv H g x g' k hk' i m)
```

Then prove the non-existential version by copying the current induction:

```lean
theorem hasStrictFDerivAt_prodAux_entry_explicit
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ s i j, X →L[ℝ] ℝ)
    (hg : ∀ s i j, HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (k : ℕ) (hk : k < L + 1) (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)) :
    HasStrictFDerivAt
      (fun y => prodAux H (g y) k hk i j)
      (prodAuxEntryDeriv H g x g' k hk i j) x := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      simpa [prodAuxEntryDeriv] using
        (hasStrictFDerivAt_const (x := x)
          ((1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j))
  | succ k ih =>
      intro hk i j
      -- same `hk'`, `hkL`, `e1`, `e2`, `hentry` as your existential lemma
      -- rewrite product entry to a finite sum
      -- each summand: `(ih ...).mul hlayer`
      -- assemble with `HasStrictFDerivAt.fun_sum`
      -- close derivative-map equality with `simp [prodAuxEntryDeriv, add_comm, add_left_comm, add_assoc]`
      ...
```

Then keep the corner computation **below this**, in block-coordinate lemmas, not as a universal prefix/suffix theorem:

```lean
theorem hasStrictFDerivAt_prod_block11_regSlice
    (a b : Fin r) :
    HasStrictFDerivAt
      (fun r0 : Fin (deepestNReg H r) → ℝ =>
        let P := Matrix.reindex
          (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
          (prod H (framedParamsReg H r hr hL (r0, 0)))
        (P.toBlocks₁₁ - 1) a b)
      (ContinuousLinearMap.proj
        ((regPivotFinEquiv H r hr).symm (Sum.inl (a, b)))) 0
```

and analogously:

```lean
hasStrictFDerivAt_prod_block12_regSlice
  -- derivative is proj ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inl (a,b))))

hasStrictFDerivAt_prod_block21_regSlice
  -- derivative is proj ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inr (a,b))))
```

Add one packing lemma first:

```lean
theorem regGaugeIdxSplit_boundary_apply (b : BoundaryPivotIdx H r) :
    regGaugeIdxSplit H r hr hL (regBoundaryToRegGauge H r hL b)
      = Sum.inl ((regPivotFinEquiv H r hr).symm b) := by
  classical
  simp [regGaugeIdxSplit, regBoundaryEmbed, regBoundaryToRegGauge,
        Equiv.Set.sumCompl_symm_apply_of_mem,
        Equiv.ofInjective_symm_apply]
```

Use it to prove `readX/readY/readZ` slice lemmas: `readX` is nonzero only at `firstLayer`, `readY` only at `lastLayer`, `readZ` only at `firstLayer`.

Final assembly:

```lean
rw [show ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)
    = ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i) from by
      ext x i; rfl]
refine hasStrictFDerivAt_pi.2 (fun i => ?_)
rcases hpack : regResidualPack H r hr i with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
· have h := hasStrictFDerivAt_prod_block11_regSlice H r hr hL a b
  have hi : (regPivotFinEquiv H r hr).symm (Sum.inl (a,b)) = i := by
    rw [regResidualPack] at hpack
    rw [← hpack, Equiv.symm_apply_apply]
  simpa [deepestEPivot, hpack, hi] using h
· ...
· ...
```

So: **do not use `hasStrictFDerivAt_iff_isLittleO` for this.** Mathlib v4.29 has it, and also has `HasStrictFDerivAt.congr_fderiv`, but the calculus API route with `HasStrictFDerivAt.mul`, `HasStrictFDerivAt.fun_sum`, `hasStrictFDerivAt_pi`, and `.hasFDerivAt.fderiv` is much less painful. The dependent-Fin casts stay confined to the single `prodAuxEntryDeriv` induction, using the same `e1/e2` pattern already working in your existence lemma.
tokens used
128,863
**Recommendation:** use an **A-lite + uniqueness** route. Do not prove the closed-form `Σ_{s<k} corner · δC_s · corner` as the primary theorem, and do not use `littleO` directly. Instead, expose the recursive derivative that your current existential proof already constructs, then specialize/evaluate it at the corner.

The existential lemma is a dead end for values: uniqueness only says an existing derivative equals another derivative after you prove the other derivative exists.

Core lemma:

```lean
noncomputable def prodAuxEntryDeriv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ s i j, X →L[ℝ] ℝ) :
    (k : ℕ) → (hk : k < L + 1) →
      Fin (H 0) → Fin (H ⟨k, hk⟩) → X →L[ℝ] ℝ
| 0, hk, i, j => 0
| k + 1, hk, i, j => by
    have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
    have hkL : k < L := Nat.lt_of_succ_lt_succ hk
    have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
      apply Fin.ext; simp [Fin.castSucc]
    have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
      apply Fin.ext; simp [Fin.succ]
    exact ∑ m : Fin (H ⟨k, hk'⟩),
      (prodAux H (g x) k hk' i m) •
          g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
      +
      (((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) •
          prodAuxEntryDeriv H g x g' k hk' i m)
```

Then prove the non-existential version by copying the current induction:

```lean
theorem hasStrictFDerivAt_prodAux_entry_explicit
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ s i j, X →L[ℝ] ℝ)
    (hg : ∀ s i j, HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (k : ℕ) (hk : k < L + 1) (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)) :
    HasStrictFDerivAt
      (fun y => prodAux H (g y) k hk i j)
      (prodAuxEntryDeriv H g x g' k hk i j) x := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      simpa [prodAuxEntryDeriv] using
        (hasStrictFDerivAt_const (x := x)
          ((1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j))
  | succ k ih =>
      intro hk i j
      -- same `hk'`, `hkL`, `e1`, `e2`, `hentry` as your existential lemma
      -- rewrite product entry to a finite sum
      -- each summand: `(ih ...).mul hlayer`
      -- assemble with `HasStrictFDerivAt.fun_sum`
      -- close derivative-map equality with `simp [prodAuxEntryDeriv, add_comm, add_left_comm, add_assoc]`
      ...
```

Then keep the corner computation **below this**, in block-coordinate lemmas, not as a universal prefix/suffix theorem:

```lean
theorem hasStrictFDerivAt_prod_block11_regSlice
    (a b : Fin r) :
    HasStrictFDerivAt
      (fun r0 : Fin (deepestNReg H r) → ℝ =>
        let P := Matrix.reindex
          (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
          (prod H (framedParamsReg H r hr hL (r0, 0)))
        (P.toBlocks₁₁ - 1) a b)
      (ContinuousLinearMap.proj
        ((regPivotFinEquiv H r hr).symm (Sum.inl (a, b)))) 0
```

and analogously:

```lean
hasStrictFDerivAt_prod_block12_regSlice
  -- derivative is proj ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inl (a,b))))

hasStrictFDerivAt_prod_block21_regSlice
  -- derivative is proj ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inr (a,b))))
```

Add one packing lemma first:

```lean
theorem regGaugeIdxSplit_boundary_apply (b : BoundaryPivotIdx H r) :
    regGaugeIdxSplit H r hr hL (regBoundaryToRegGauge H r hL b)
      = Sum.inl ((regPivotFinEquiv H r hr).symm b) := by
  classical
  simp [regGaugeIdxSplit, regBoundaryEmbed, regBoundaryToRegGauge,
        Equiv.Set.sumCompl_symm_apply_of_mem,
        Equiv.ofInjective_symm_apply]
```

Use it to prove `readX/readY/readZ` slice lemmas: `readX` is nonzero only at `firstLayer`, `readY` only at `lastLayer`, `readZ` only at `firstLayer`.

Final assembly:

```lean
rw [show ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)
    = ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i) from by
      ext x i; rfl]
refine hasStrictFDerivAt_pi.2 (fun i => ?_)
rcases hpack : regResidualPack H r hr i with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
· have h := hasStrictFDerivAt_prod_block11_regSlice H r hr hL a b
  have hi : (regPivotFinEquiv H r hr).symm (Sum.inl (a,b)) = i := by
    rw [regResidualPack] at hpack
    rw [← hpack, Equiv.symm_apply_apply]
  simpa [deepestEPivot, hpack, hi] using h
· ...
· ...
```

So: **do not use `hasStrictFDerivAt_iff_isLittleO` for this.** Mathlib v4.29 has it, and also has `HasStrictFDerivAt.congr_fderiv`, but the calculus API route with `HasStrictFDerivAt.mul`, `HasStrictFDerivAt.fun_sum`, `hasStrictFDerivAt_pi`, and `.hasFDerivAt.fderiv` is much less painful. The dependent-Fin casts stay confined to the single `prodAuxEntryDeriv` induction, using the same `e1/e2` pattern already working in your existence lemma.

exec
/bin/bash -lc 'rg -n "toBlocks₁₁|toBlocks11|toBlocks₁₂|toBlocks₂₁|fromBlocks_apply" lean/.lake/packages/mathlib/Mathlib lean/DLNFibre -S' in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '70,220p' lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
    prodAux H A (k + 1) hk
      = prodAux H A k (Nat.lt_of_succ_lt hk) * Matrix.reindex eC.symm eS.symm M := by
  have hkL : k < L := Nat.lt_of_succ_lt_succ hk
  have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
  have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
    apply Fin.ext; simp [Fin.castSucc]
  have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
    apply Fin.ext; simp [Fin.succ]
  show prodAux H A k hk' *
      ((by rw [e1, e2]; exact A ⟨k, hkL⟩ :
        Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) = _
  refine congrArg (prodAux H A k hk' * ·) ?_
  rw [hlayer]; cases e1; cases e2; rfl

/-- **The corner-block idempotent product** (reindex form). The block-normal corner `fromBlocks 1 0 0 0`
is idempotent under the chain product, and reindexing along a shared middle interface `eB` cancels:
`reindex eA.symm eB.symm corner * reindex eB.symm eC.symm corner = reindex eA.symm eC.symm corner`.
Via `reindex_apply` (→ `submatrix`), `submatrix_mul_equiv` (the `eB.symm` interface), `fromBlocks_multiply`
(`[1,0;0,0]·[1,0;0,0] = [1,0;0,0]`). -/
theorem corner_reindex_mul {a b c r : ℕ}
    (eA : Fin a ≃ Fin r ⊕ Fin (a - r)) (eB : Fin b ≃ Fin r ⊕ Fin (b - r))
    (eC : Fin c ≃ Fin r ⊕ Fin (c - r)) :
    (Matrix.reindex eA.symm eB.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0))
        * (Matrix.reindex eB.symm eC.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0))
      = Matrix.reindex eA.symm eC.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) eA eB eC]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **Reindex distributes over a left endpoint-frame product** (the FOLD3 general-layer kernel). For a
SQUARE row-frame `P : Matrix m m ℝ` and a general layer `A : Matrix m n ℝ`, reindexing the product
`P * A` along `(eC, eS)` factors as `(reindex eC eC P) * (reindex eC eS A)` — the frame `P` rides on the
row-index alone, so its reindex is the diagonal `(eC, eC)` and the shared middle interface `eC.symm`
cancels (`submatrix_mul_equiv`). This is the boundary-frame extraction the `endpoint_telescoping` base
step needs (`reindex (C ⟨0⟩) = (cast P₀) · reindex (A ⟨0⟩)` when `C ⟨0⟩ = P₀ · A ⟨0⟩`). Generic over the
index types — `m, n` any Fintypes, `eC, eS` any reindex equivs. -/
theorem reindex_mul_distrib_left {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    (P : Matrix m m ℝ) (A : Matrix m n ℝ) (eC : m ≃ m') (eS : n ≃ n') :
    Matrix.reindex eC eS (P * A)
      = Matrix.reindex eC eC P * Matrix.reindex eC eS A := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv P A eC.symm eC.symm eS.symm]

/-- **Reindex distributes over a right endpoint-frame product** (the FOLD3 boundary-`Q` kernel). For a
general layer `A : Matrix m n ℝ` and a SQUARE column-frame `Q : Matrix n n ℝ`, reindexing `A * Q` along
`(eC, eS)` factors as `(reindex eC eS A) * (reindex eS eS Q)` — `Q` rides on the column-index, so the
shared middle interface `eS.symm` cancels. The boundary-right-frame extraction the `endpoint_telescoping`
final step needs (`reindex (C ⟨Lm⟩) = reindex (A ⟨Lm⟩) · (cast Q_Lm)` when `C ⟨Lm⟩ = A ⟨Lm⟩ · Q_Lm`). -/
theorem reindex_mul_distrib_right {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    (A : Matrix m n ℝ) (Q : Matrix n n ℝ) (eC : m ≃ m') (eS : n ≃ n') :
    Matrix.reindex eC eS (A * Q)
      = Matrix.reindex eC eS A * Matrix.reindex eS eS Q := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv A Q eC.symm eS.symm eS.symm]

/-- **The idempotent fold at `0`** (`prodAux` form, `1 ≤ k`). At the deepest gauge slot, every layer is
the block-normal corner `reindex (fromBlocks 1 0 0 0)` (`framedParamsReg_zero`), and the corner is
idempotent under the chain product, so the running product through `k ≥ 1` layers is again the corner
(at width `H 0 × H ⟨k⟩`). Proven by `prodAux_succ` + `framedParamsReg_zero` + `fromBlocks_multiply`
(the `[1,0;0,0]·[1,0;0,0] = [1,0;0,0]` corner idempotent) + `submatrix_mul_equiv` (interface cancel). -/
theorem prodAux_framedParamsReg_zero_aux (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ (k : ℕ) (hk : k < L + 1), 1 ≤ k →
      prodAux H (framedParamsReg H r hr hL 0) k hk
        = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
            (rThresholdSplit r (H ⟨k, hk⟩) (hr ⟨k, hk⟩)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  intro k
  induction k with
  | zero => intro _ hk0; exact absurd hk0 (by norm_num)
  | succ k ih =>
      intro hk _
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      -- INDEX-level equalities (the `prodAux` def's own, `Fin.ext`).
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- `prodAux (k+1)` unfolds (def at Loss.lean) to `prodAux k * (Eq.mpr-cast layer)`, and that layer
      -- IS the corner at the running widths (`framedParamsReg_zero` then `cases e1; cases e2` collapses the
      -- two `Eq.mpr` casts to `rfl`). Rewrite the whole succ-step in one `rw [hstep]`.
      -- the Eq.mpr-cast layer = the corner at the running widths (PROBE-proven: `framedParamsReg_zero`
      -- then `cases e1; cases e2` collapses the two `Eq.mpr` casts to `rfl`).
      have hlayer : ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
            Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ))
          = Matrix.reindex (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩)).symm
              (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩)).symm
              (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
        rw [framedParamsReg_zero H r hr hL ⟨k, hkL⟩]; cases e1; cases e2; rfl
      have hstep : prodAux H (framedParamsReg H r hr hL 0) (k + 1) hk
          = prodAux H (framedParamsReg H r hr hL 0) k hk' *
              Matrix.reindex (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩)).symm
                (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩)).symm
                (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
        show prodAux H (framedParamsReg H r hr hL 0) k hk' *
            ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
              Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) = _
        exact congrArg (prodAux H (framedParamsReg H r hr hL 0) k hk' * ·) hlayer
      rw [hstep]
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        -- accumulator is `prodAux 0 = 1`; `1 * corner = corner` (`prodAux 0` reduces, then `one_mul`).
        exact Matrix.one_mul _
      · rw [ih hk' hkpos]
        exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩))
          (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩))

/-- **The idempotent fold at `0` — `prod` form** (`#123` (1), the `deepestEPivot_base` input). The full
gauge-sliced product at the deepest gauge slot is the block-normal corner: `prod (framedParamsReg 0) =
reindex (fromBlocks 1 0 0 0)` (at width `H 0 × H (last)`). `prod = prodAux L`; specialize the `aux`
fold at `k = L` (`1 ≤ L`). The `Fin.last L = ⟨L, _⟩` index form aligns by `Fin.ext`. -/
theorem prodAux_framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    prod H (framedParamsReg H r hr hL 0)
      = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  have h := prodAux_framedParamsReg_zero_aux H r hr hL L (Nat.lt_succ_self L) hL
  rw [prod]
  rw [h]
  -- `⟨L, _⟩ = Fin.last L` (Fin.ext); the two corner index-forms agree.
  congr 1

/-- **PIN2 endpoint-frame telescoping** (existential endpoints, cobuild's banked shape). If every layer
of `C` is the framed layer `C s = P s · A s · Q s` with `P s, Q s` units, and the interior interfaces
collapse (`Q s = I`, `P ⟨s+1⟩ = I` for adjacent layers — the #95-(I) frame-triviality), then the full
products relate by endpoint conjugation: `∃ P₀ Q_L units, ∏C = P₀ · (∏A) · Q_L`. The endpoints are typed
where `prod` lives (`Fin (H 0)`, `Fin (H (last))`), dodging the layer-index cast. -/
theorem endpoint_telescoping (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (A C : Params H)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hframe : ∀ s : Fin L, C s = P s * A s * Q s)
    (hinterface : ∀ (s : Fin L) (hs : (s : ℕ) + 1 < L),
      Q s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        P ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix _ _ ℝ)) :
    ∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
      prod H C = P0 * prod H A * QL := by
  -- ALL interior frames are identity (`hinterface`). `P s = 1` for `1 ≤ s` (interior-left + boundary), and
  -- `Q s = 1` for `s ≤ Lm-1` (interior-right). So `C 0 = P 0 · A 0`, `C s = A s` (1 ≤ s ≤ Lm-1),
  -- `C Lm = A Lm · Q Lm`. Then `∏C = P 0 · ∏A · Q Lm` (P 0 rides at fixed width `Fin (H 0)`).
  obtain ⟨Lm, rfl⟩ : ∃ Lm, L = Lm + 1 := ⟨L - 1, by omega⟩
  -- `P s = 1` for `1 ≤ (s:ℕ)`: from `hinterface (s-1)`'s `P ((s-1)+1) = P s = 1`.
  have hPid : ∀ s : Fin (Lm + 1), 1 ≤ (s : ℕ) →

exec
/bin/bash -lc "sed -n '400,530p' lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
        | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
        | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b := rfl
  rw [hcoord]
  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · simp only [Matrix.toBlocks₁₁, Matrix.sub_apply, Matrix.of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    exact (hprod _ _).sub contDiff_const
  · simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
    exact hprod _ _
  · simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
    exact hprod _ _

/-- **`deepestEPivot`'s reg-block derivative at `0` is the IDENTITY** (the #91 analytic crux,
g213-pin1-de0). Restricted to the regular slice `r ↦ deepestEPivot (r, 0)`, the strict derivative at
`0` is `id` — the idempotent-sandwich `dP|_0 = Σ_s corner·δC_s·corner` with the gauge slot held at `0`
keeps ONLY the `(0,0)`-block `X`-pivot (which equals the reg-input on the pivot coords). This is the
single analytic obligation of `_deriv`; everything else (the product strict-derivative, the shear-CLE
packaging) is banked. **OBLIGATION:** the `regResidualPack` ↔ `(X_first, Y_last, Z_first)` pivot-coord
correspondence at the gauge-zero slice (the #91 transcription / pp2 coordinate cert). -/
theorem deepestEPivot_regSlice_fderiv_id (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
        deepestEPivot H r hr hL (r0, 0))
      (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)) 0 := by
  -- #120 (deriv-fm): the opaque-pack wall is DISSOLVED — `regResidualPack := regPivotFinEquiv` and
  -- `regGaugeIdxSplit`'s reg-half route via `regBoundaryToRegGauge ∘ regPivotFinEquiv` (the SHARED
  -- `regPivotFinEquiv`), so the reg-coords ARE the boundary pivots (X_first/Y_last/Z_first) by
  -- construction. Coordinate-wise (`hasStrictFDerivAt_pi'`): each output coord `i`'s derivative is the
  -- `i`-th projection.
  rw [show (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ))
      = ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i) from by ext x i; rfl]
  refine hasStrictFDerivAt_pi.2 (fun i => ?_)
  -- Per-coordinate: `HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0`. The #91
  -- idempotent-sandwich: `d(prod(framedParamsReg (r0,0)))|_0 = Σ_s corner·δC_s·corner` keeps the
  -- surviving boundary block at coord `i`; the SHARED `regPivotFinEquiv` cancel identifies it with `r0 i`.
  -- REMAINING ANALYTIC ATOM (the #91 transcription, per deriv-alignment-sandwich-tactic-cert.md): the
  -- per-coordinate product-derivative value + the cancel. Skeleton validated (shape typechecks); the
  -- atom is the patient analytic fill (the Leibniz sandwich VALUE through `prodAux` + the cancel).
  sorry

/-- **`deepestEPivot`'s derivative at `0` is the invertible SHEAR** (#120-corrected: NOT `fst`). By #91
(`d(P−B)|_0 = (Σ_s X_s, Y_L, Z_1)`, idempotent sandwich), the reg-residual's derivative reads the
reg-X + sums the gauge-X's into reg while keeping the gauge free — the unitriangular shear
`D_E = [[I, Σ],[0, I]]` on `reg×gauge → reg` (its total `regStraightenTotalCLM D_E` is `[[I,Σ],[0,I]]`
on `DeepestSplit`, det 1, invertible). Bundled: `∃ D_E (e : ≃L), HasStrictFDerivAt deepestEPivot D_E 0
∧ (e : →L) = regStraightenTotalCLM D_E`. ASSEMBLED from `_contdiff` (→ `D_E := fderiv`), the reg-block
identity `deepestEPivot_regSlice_fderiv_id` (the #91 crux), and the generic shear-CLE
`regStraightenTotalCLM_equiv_of_regBlock_id`. -/
theorem deepestEPivot_deriv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ (D_E : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ))
      (e : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r)),
      HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 ∧
      (e : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r))
        = regStraightenTotalCLM D_E := by
  -- `D_E := fderiv ℝ deepestEPivot 0` (free from `_contdiff`); its reg-block is `id` (the #91 fact),
  -- so `regStraightenTotalCLM D_E` is the invertible shear (`regStraightenTotalCLM_equiv_of_regBlock_id`).
  set D_E := fderiv ℝ (deepestEPivot H r hr hL) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 :=
    (deepestEPivot_contdiff H r hr hL).hasStrictFDerivAt (by simp)
  -- The reg-block: `D_E.comp regInCLM = id`. The reg-slice `r ↦ deepestEPivot (r,0)` has strict
  -- derivative `D_E.comp regInCLM` (chain rule) AND `id` (#91), so they agree.
  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => ((r0, 0) :
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)))
      (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) 0 := by
    have := (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt (x := 0)
    simpa [regInCLM] using this
  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEPivot H r hr hL (r0, 0)) (D_E.comp regInCLM) 0 := by
    have hsd0 : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E
        (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))) := hsd
    exact hsd0.comp (x := (0 : Fin (deepestNReg H r) → ℝ)) hregIn
  have hblock : D_E.comp (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
      = ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ) := by
    have h1 := hcomp.hasFDerivAt.fderiv
    have h2 := (deepestEPivot_regSlice_fderiv_id H r hr hL).hasFDerivAt.fderiv
    rw [← h1, ← h2]
  obtain ⟨e, he⟩ := regStraightenTotalCLM_equiv_of_regBlock_id (C := Fin (flatDim (deepestM H r)) → ℝ)
    D_E hblock
  exact ⟨D_E, e, hsd, he⟩

theorem deepestEPivot_base (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    deepestEPivot H r hr hL 0 = 0 := by
  -- At the origin slot, `∏(framedParamsReg 0)` is the reindexed corner `fromBlocks 1 0 0 0`
  -- (`prod_framedParamsReg_zero`); the outer `reindex` in `P` cancels it, so `P = fromBlocks 1 0 0 0`.
  funext i
  -- The matrix `P` defining the coordinates is the cancelled corner.
  have hP : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H (Fin.last L))
        (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL 0)))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 := by
    rw [prodAux_framedParamsReg_zero H r hr hL, ← Matrix.reindex_symm,
      Equiv.apply_symm_apply]
  -- Each coordinate reads a block of `P`; all blocks of `fromBlocks 1 0 0 0` give `0` in the residual.
  simp only [deepestEPivot, hP, Pi.zero_apply]
  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    simp only [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.sub_apply,
      Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, sub_self]

/-- **PIN 2 — the loss squeeze** (the geometric heart). Near the deepest point (flat coords), the loss
is two-sidedly bounded by `Φ = ∑ (regStraighten (split w)).1² + deepestCoreF (coreAbsorb (split w)).2.1`.
The matrix-block reduction `∏C − blockNormal → P11 = leak + Rcore` (g164 boundary frames) feeding the
banked `core_comparability_squeeze` (#54: leak ∈ ideal(reg), charged to `∑E²`). `regStraighten` is the
(C)-fallback total continuous fn; the squeeze is the local `∃ U` germ where `(regStraighten w).1 = E`.
**Takes the concrete-map defining identities** (`hregval`: reg-output is the pivot residual
`deepestEPivot`; `hcoreabs`: `coreAbsorb` is the cutoff Schur shear) — without them the maps are
arbitrary and the bound is unprovable (the g161-class confound). -/
theorem deepest_loss_squeeze (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (coreAbsorb : DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit_base : split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEPivot H r hr hL (q.1, q.2.2))
    (hcoreabs : coreAbsorb = deepestCoreAbsorb H r hr hL) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ U ∈ 𝓝 ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)),
        ∀ w ∈ U,
          0 ≤ ((∑ i, (regStraighten (split w)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split w)).2.1) ∧
          c₁ * ((∑ i, (regStraighten (split w)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split w)).2.1)

 succeeded in 194ms:
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Determinant.lean:814:      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Determinant.lean:816:    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Determinant.lean:825:        Matrix.fromBlocks_apply₂₂, b, D]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Basic.lean:256:  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Basic.lean:266:      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Basic.lean:270:  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Basic.lean:271:      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Relations.lean:51:      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, add_zero, Finset.sum_const_zero]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Relations.lean:57:      Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.fromBlocks_apply₁₂,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Relations.lean:59:      Matrix.fromBlocks_apply₂₂, zero_add, ite_mul, zero_mul, Matrix.smul_apply, smul_ite, smul_add,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Relations.lean:164:        Matrix.mul_apply, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Relations.lean:178:        Matrix.fromBlocks_apply₂₁, Matrix.of_apply, hki, reduceIte, zero_mul, Finset.sum_const_zero,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Relations.lean:179:        Matrix.fromBlocks_apply₂₂, mul_ite, ite_mul, mul_zero, ← ite_and, if_neg (hx _), add_zero,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Block.lean:221:      Equiv.sumCompl_apply_inl, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Block.lean:222:      fromBlocks_apply₂₂, Matrix.submatrix_apply]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Symmetric.lean:169:    ⟨(congr_arg toBlocks₁₁ h :), (congr_arg toBlocks₂₁ h :), (congr_arg toBlocks₁₂ h :),
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:702:        simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:703:          fromBlocks_apply₂₂]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:717:        rw [hx, fromBlocks_apply₂₁, zero_apply]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean:151:    ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h,
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean:527:    simp [toBlocks₁₂, this, listTransvecCol_mul_mul_listTransvecRow_last_row M hM]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean:530:    simp [toBlocks₂₁, this, listTransvecCol_mul_mul_listTransvecRow_last_col M hM]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean:563:  simp only [not_and_or, IsTwoBlockDiagonal, toBlocks₁₂, toBlocks₂₁, ← Matrix.ext_iff] at H
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Transvection.lean:601:  let M'' := toBlocks₁₁ M'
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:113:    invertibleOfLeftInverse _ (⅟(fromBlocks A B 0 D)).toBlocks₁₁ <| by
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:117:        congr_arg Matrix.toBlocks₁₁ this
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:130:    invertibleOfRightInverse _ (⅟(fromBlocks A 0 C D)).toBlocks₁₁ <| by
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:133:      replace := congr_arg Matrix.toBlocks₁₁ this
lean/.lake/packages/mathlib/Mathlib/Algebra/Lie/Classical.lean:358:      Sum.elim_inl, if_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
lean/.lake/packages/mathlib/Mathlib/Algebra/Lie/Classical.lean:359:      Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
lean/.lake/packages/mathlib/Mathlib/Algebra/Lie/Classical.lean:360:      Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr, Sum.elim_inr, Sum.inl_injective.eq_iff,
lean/.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:309:private lemma jacobiMatrix_comp_₁₂ : (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0 := by
lean/.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:311:  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]
lean/.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:325:    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det = Q.jacobian := by
lean/.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:379:    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det *
lean/.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:383:    convert Matrix.det_fromBlocks_zero₁₂ (Q.comp P).jacobiMatrix.toBlocks₁₁
lean/.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:384:      (Q.comp P).jacobiMatrix.toBlocks₂₁ (Q.comp P).jacobiMatrix.toBlocks₂₂

exec
/bin/bash -lc "sed -n '330,410p' lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
      (∀ q : DeepestSplit H r (deepestNGauge H r), (deepestCoreAbsorb H r hr hL q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r))
        = rlctAtOn
            (fun q : DeepestSplit H r (deepestNGauge H r) =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
            (0 : DeepestSplit H r (deepestNGauge H r)) :=
  coreShear_satisfies_coreAbsorb H r (deepestNGauge H r) (schurCutoffShift H r hr hL)
    (continuous_schurCutoffShift H r hr hL) (schurCutoffShift_zero H r hr hL)

/-! ## The shared pivot map `deepestEPivot` (the PIN1↔PIN2 coupling object)

The reg-straightening's reg-output is `deepestEPivot` — the genuine nonlinear straightened residual
reading the reg + spectator slots, with `dE(0) = id` (typed `HasStrictFDerivAt deepestEPivot (fst) 0`).
PIN 1 needs ONLY that derivative fact (the IFT/peel is form-agnostic); PIN 2's squeeze needs its
concrete value (`(deepestEPivot (split w).reg, (split w).spec)` ≍ the loss residual `E`). So this is
the SHARED coupling object — defined once, consumed by both pins. Its three properties (`ContDiff ⊤`,
`HasStrictFDerivAt (fst) 0`, `0 ↦ 0`) are the residual gauge-geometry obligation: the product-residual
expansion `∏(I+X_s) − I` read off the gauge slots, certified `dE(0) = id` (pp2 #91, general L). -/

/-- The pack equivalence `Fin nReg ≃ (r×r) ⊕ ((r×M_L) ⊕ (M_0×r))` — the THREE regular residual blocks
`(P11−I, P12, P21)` of `∏C` flatten into the `nReg = r(H_0+H_L−r)` reg coordinates. **#120 explicit:**
`:= regPivotFinEquiv` (the TRANSPARENT `finProdFinEquiv`/`finSumFinEquiv` enumeration in
`DeepestSplitReindex`), SHARED with `regGaugeIdxSplit`'s reg-half (which routes via
`regBoundaryToRegGauge ∘ regPivotFinEquiv`), so the two cancel and the gauge-zero reg-slice derivative is
`id` by construction. `_base`/`_contdiff` need only that it is a coordinate bijection (it is, an `Equiv`). -/
noncomputable def regResidualPack (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin (deepestNReg H r)
      ≃ (Fin r × Fin r) ⊕ ((Fin r × Fin (H (Fin.last L) - r)) ⊕ (Fin (H 0 - r) × Fin r)) :=
  regPivotFinEquiv H r hr

/-- The regular residual blocks `(P11 − I, P12, P21)` of the framed product `∏C|_{T=0}`, packed into
`Fin nReg → ℝ` via `regResidualPack`. `P = ∏ (framedParamsReg p)` reindexed to `r ⊕ M` block shape;
`P11 = toBlocks₁₁`, `P12 = toBlocks₁₂`, `P21 = toBlocks₂₁`; the residual is `(P11−1, P12, P21)`. -/
noncomputable def deepestEPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ) → (Fin (deepestNReg H r) → ℝ) :=
  fun p =>
    let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H (Fin.last L))
      (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL p))
    fun i => match regResidualPack H r hr i with
      | Sum.inl (a, b) => (P.toBlocks₁₁ - 1) a b
      | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
      | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b

theorem deepestEPivot_contdiff (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestEPivot H r hr hL) := by
  -- Each layer entry of `framedParamsReg` is `ContDiff` (`contDiff_framedParamsReg_entry`), so each
  -- entry of `prod H (framedParamsReg ·)` is `ContDiff` (`contDiff_prod_entry`).
  have hlayer : ∀ (s : Fin L) (a : Fin (H s.castSucc)) (b : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s a b) :=
    contDiff_framedParamsReg_entry H r hr hL
  have hprod : ∀ (a : Fin (H 0)) (b : Fin (H (Fin.last L))),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => prod H (framedParamsReg H r hr hL p) a b) :=
    fun a b => contDiff_prod_entry H (framedParamsReg H r hr hL) hlayer a b
  -- `deepestEPivot p` is a `Fin nReg → ℝ` whose each coordinate is (a `prod`-entry, reindexed) − const.
  refine contDiff_pi.2 (fun i => ?_)
  -- The `i`-coordinate selects one match-arm (independent of `p`); rewrite to that arm, then it is a
  -- reindexed `prod`-entry (minus the constant `1` on the `inl` arm).
  have hcoord : (fun p => deepestEPivot H r hr hL p i)
      = fun p =>
        let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
          (prod H (framedParamsReg H r hr hL p))
        match regResidualPack H r hr i with
        | Sum.inl (a, b) => (P.toBlocks₁₁ - 1) a b
        | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
        | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b := rfl
  rw [hcoord]
  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · simp only [Matrix.toBlocks₁₁, Matrix.sub_apply, Matrix.of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    exact (hprod _ _).sub contDiff_const
  · simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
    exact hprod _ _
  · simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,

exec
/bin/bash -lc "sed -n '1,130p' lean/.lake/packages/mathlib/Mathlib/Data/Matrix/Block.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Block Matrices

## Main definitions

* `Matrix.fromBlocks`: build a block matrix out of 4 blocks
* `Matrix.toBlocks₁₁`, `Matrix.toBlocks₁₂`, `Matrix.toBlocks₂₁`, `Matrix.toBlocks₂₂`:
  extract each of the four blocks from `Matrix.fromBlocks`.
* `Matrix.blockDiagonal`: block diagonal of equally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonalRingHom`.
* `Matrix.blockDiag`: extract the blocks from the diagonal of a block diagonal matrix.
* `Matrix.blockDiagonal'`: block diagonal of unequally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonal'RingHom`.
* `Matrix.blockDiag'`: extract the blocks from the diagonal of a block diagonal matrix.
-/

@[expose] public section

variable {l m n o p q : Type*} {m' n' p' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type*} {β : Type*}

open Matrix

namespace Matrix

theorem dotProduct_block [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (v w : m ⊕ n → α) :
    v ⬝ᵥ w = v ∘ Sum.inl ⬝ᵥ w ∘ Sum.inl + v ∘ Sum.inr ⬝ᵥ w ∘ Sum.inr :=
  Fintype.sum_sum_type _

section BlockMatrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
@[pp_nodot]
def fromBlocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
    Matrix (n ⊕ o) (l ⊕ m) α :=
  of <| Sum.elim (fun i => Sum.elim (A i) (B i)) (fun j => Sum.elim (C j) (D j))

@[simp]
theorem fromBlocks_apply₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : l) : fromBlocks A B C D (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp]
theorem fromBlocks_apply₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : n) (j : m) : fromBlocks A B C D (Sum.inl i) (Sum.inr j) = B i j :=
  rfl

@[simp]
theorem fromBlocks_apply₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : l) : fromBlocks A B C D (Sum.inr i) (Sum.inl j) = C i j :=
  rfl

@[simp]
theorem fromBlocks_apply₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) (i : o) (j : m) : fromBlocks A B C D (Sum.inr i) (Sum.inr j) = D i j :=
  rfl

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
def toBlocks₁₁ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix n l α :=
  of fun i j => M (Sum.inl i) (Sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def toBlocks₁₂ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix n m α :=
  of fun i j => M (Sum.inl i) (Sum.inr j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def toBlocks₂₁ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix o l α :=
  of fun i j => M (Sum.inr i) (Sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def toBlocks₂₂ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix o m α :=
  of fun i j => M (Sum.inr i) (Sum.inr j)

theorem fromBlocks_toBlocks (M : Matrix (n ⊕ o) (l ⊕ m) α) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M := by
  ext i j
  rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

@[simp]
theorem toBlocks_fromBlocks₁₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₁ = A :=
  rfl

@[simp]
theorem toBlocks_fromBlocks₁₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₁₂ = B :=
  rfl

@[simp]
theorem toBlocks_fromBlocks₂₁ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₁ = C :=
  rfl

@[simp]
theorem toBlocks_fromBlocks₂₂ (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α)
    (D : Matrix o m α) : (fromBlocks A B C D).toBlocks₂₂ = D :=
  rfl

/-- Two block matrices are equal if their blocks are equal. -/
theorem ext_iff_blocks {A B : Matrix (n ⊕ o) (l ⊕ m) α} :
    A = B ↔
      A.toBlocks₁₁ = B.toBlocks₁₁ ∧
        A.toBlocks₁₂ = B.toBlocks₁₂ ∧ A.toBlocks₂₁ = B.toBlocks₂₁ ∧ A.toBlocks₂₂ = B.toBlocks₂₂ :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ => by
    rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, h₁₁, h₁₂, h₂₁, h₂₂]⟩

@[simp]
theorem fromBlocks_inj {A : Matrix n l α} {B : Matrix n m α} {C : Matrix o l α} {D : Matrix o m α}
    {A' : Matrix n l α} {B' : Matrix n m α} {C' : Matrix o l α} {D' : Matrix o m α} :
    fromBlocks A B C D = fromBlocks A' B' C' D' ↔ A = A' ∧ B = B' ∧ C = C' ∧ D = D' :=
  ext_iff_blocks

theorem fromBlocks_map (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α)
    (f : α → β) : (fromBlocks A B C D).map f =

exec
/bin/bash -lc "sed -n '108,120p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl

theorem Filter.EventuallyEq.hasStrictFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
    HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x :=
  h.prodMap_nhds h |>.hasFDerivAtFilter_iff h'

theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
    HasStrictFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
  h' ▸ h


exec
/bin/bash -lc "sed -n '1,90p' lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Foundations.Loss
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestTelescoping` — the PIN2 endpoint-frame telescoping

The cast-heavy `prodAux` induction behind PIN2's frame bridge:
`∏C = P₀ · (∏A) · Q_{L-1}` when each layer is framed `C s = P s · A s · Q s` and the interior
interfaces cancel (`Q s · P (s+1) = 1`). Stated with EXISTENTIAL endpoints (cobuild's banked
statement-shape, `@eee22a1`) to dodge the `H 0` vs `H ⟨0,_⟩.castSucc` definitional mismatch.

**STATUS (crux2 2026-06-23): the cast mechanics are DE-RISKED, the induction is the XL-cast — DEFERRED
to a fresh-session-with-Codex (HEq-induction design), per controller's 3-attempt discipline.** Two
findings shape the eventual proof:
- (PROBE 1, BUILDS) the running-width identifications `H ⟨k,hk⟩` and `H (⟨k,hkL⟩.castSucc)` are
  DEFINITIONALLY `rfl` (Fin proof-irrelevance + `castSucc ⟨k,_⟩` reduction). So the index VALUES agree
  freely — the obstacle is purely the elaborator's `HMul` instance synthesis, NOT a real value-mismatch.
- (`prodAux_succ` SHAPE, typechecks) the `k+1` fold IS the running product times the layer transported
  by `Matrix.reindex (finCongr ·) (finCongr ·)` (the explicit form of the def's `rw [e1,e2]`). This is
  the right unfold; its `rfl`-discharge needs an entry-chase through `reindex_apply` vs the def's `Eq.mpr`
  cast — the bridge that wants Codex's design (3-attempt cap hit on the entry-chase).
The `endpoint_telescoping` statement-SHAPE is cobuild's (`@eee22a1`); it typechecks (signature GREEN).
The remaining work is the prefix-fold induction with interface-cancellation in the reindexed types.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **DE-RISK PROBE 1 (BUILDS `rfl`).** The two running-width identifications are definitionally equal —
the index values agree freely; only `HMul` instance synthesis (not a value-mismatch) is the obstacle. -/
example (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k + 1 < L + 1) :
    H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
      = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc) := rfl

/-- **`prodAux` recursion, reindex-explicit** (statement TYPECHECKS; proof is the deferred entry-chase).
The `k+1` fold is the running product times the `k`-th layer, transported to the running-width type by
`Matrix.reindex (finCongr ·) (finCongr ·)` — the explicit form of the def's `rw [e1,e2]; exact A …`. -/
theorem prodAux_succ (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (e1 : H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
    (e2 : H (⟨k + 1, hk⟩ : Fin (L+1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) :
    prodAux H A (k + 1) hk
      = (prodAux H A k (Nat.lt_of_succ_lt hk)) *
          (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩)) := by
  obtain rfl : e1 = rfl := Subsingleton.elim _ _
  obtain rfl : e2 = rfl := Subsingleton.elim _ _
  rfl

/-- **SHARED step-cast helper** (#123, the family kernel). If the `k`-th layer of `A` is the reindexed
block `Matrix.reindex eC.symm eS.symm M` at the running widths, then the `prodAux` succ-step is the clean
product `prodAux k * reindex eC.symm eS.symm M` — the def's `Eq.mpr` cast is collapsed by the index-level
`cases e1; cases e2` idiom (the `contDiff_prodAux_entry` precedent). All three folds (value / deriv /
telescope) apply this then their own block-composition. `eC, eS` are the threshold splits at `H ⟨k,hk'⟩`,
`H ⟨k+1,hk⟩`. -/
theorem prodAux_succ_layer (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    {p q : ℕ} (eC : Fin (H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1))) ≃ Fin p ⊕ Fin q)
    {p' q' : ℕ} (eS : Fin (H (⟨k + 1, hk⟩ : Fin (L+1))) ≃ Fin p' ⊕ Fin q')
    (M : Matrix (Fin p ⊕ Fin q) (Fin p' ⊕ Fin q') ℝ)
    (hlayer : A (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L)
      = (by rw [show (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc
                = (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1)) from by apply Fin.ext; simp [Fin.castSucc],
              show (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ
                = (⟨k + 1, hk⟩ : Fin (L+1)) from by apply Fin.ext; simp [Fin.succ]]
            exact Matrix.reindex eC.symm eS.symm M :
          Matrix (Fin (H (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
            (Fin (H (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) ℝ)) :
    prodAux H A (k + 1) hk
      = prodAux H A k (Nat.lt_of_succ_lt hk) * Matrix.reindex eC.symm eS.symm M := by
  have hkL : k < L := Nat.lt_of_succ_lt_succ hk
  have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
  have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
    apply Fin.ext; simp [Fin.castSucc]
  have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
    apply Fin.ext; simp [Fin.succ]
  show prodAux H A k hk' *
      ((by rw [e1, e2]; exact A ⟨k, hkL⟩ :
        Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) = _
  refine congrArg (prodAux H A k hk' * ·) ?_
  rw [hlayer]; cases e1; cases e2; rfl

/-- **The corner-block idempotent product** (reindex form). The block-normal corner `fromBlocks 1 0 0 0`
is idempotent under the chain product, and reindexing along a shared middle interface `eB` cancels:
`reindex eA.symm eB.symm corner * reindex eB.symm eC.symm corner = reindex eA.symm eC.symm corner`.
Via `reindex_apply` (→ `submatrix`), `submatrix_mul_equiv` (the `eB.symm` interface), `fromBlocks_multiply`
(`[1,0;0,0]·[1,0;0,0] = [1,0;0,0]`). -/
theorem corner_reindex_mul {a b c r : ℕ}
    (eA : Fin a ≃ Fin r ⊕ Fin (a - r)) (eB : Fin b ≃ Fin r ⊕ Fin (b - r))

codex
Use a hybrid of **(II) + remainder**, but keep the `prodAux` work algebraic, not differential.

Do **not** build the full recursive derivative value unless the product normal form gets stuck. The leanest general route is:

1. Prove a value-level regular-slice product collapse after the final outer `reindex`.
2. Read the three target blocks from that collapse.
3. Differentiate the resulting scalar formulas.

For `2 ≤ L`, the useful normal form is:

```lean
P(r0) =
  Matrix.fromBlocks
    (1 + Xfirst r0)
    ((1 + Xfirst r0) * Ylast r0)
    (Zfirst r0)
    (Zfirst r0 * Ylast r0)
```

For `L = 1`, it is just:

```lean
P(r0) =
  Matrix.fromBlocks (1 + Xfirst r0) (Ylast r0) (Zfirst r0) 0
```

So the target blocks become:

```lean
(P(r0).toBlocks₁₁ - 1) a b = r0 idxX
P(r0).toBlocks₂₁ a b       = r0 idxZ
P(r0).toBlocks₁₂ a b       = r0 idxY + ∑ c : Fin r, r0 (idxX a c) * r0 (idxY c b) -- if 2 ≤ L
```

For `L = 1`, the `P12` quadratic sum is absent. Also: `P21` is exactly linear; the quadratic `Zfirst * Ylast` lands in block `₂₂`, outside the regular residual.

Key calculus lemmas:

```lean
theorem hasStrictFDerivAt_mul_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (hfx : f x = 0) (hgx : g x = 0) :
    HasStrictFDerivAt (fun y => f y * g y) (0 : E →L[ℝ] ℝ) x := by
  simpa [hfx, hgx] using hf.mul hg
```

```lean
theorem hasStrictFDerivAt_sum_mul_zero
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ι → E → ℝ) (f' g' : ι → E →L[ℝ] ℝ) {x : E}
    (hf : ∀ i, HasStrictFDerivAt (f i) (f' i) x)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x)
    (hf0 : ∀ i, f i x = 0) (hg0 : ∀ i, g i x = 0) :
    HasStrictFDerivAt (fun y => ∑ i, f i y * g i y) 0 x := by
  simpa using
    (HasStrictFDerivAt.fun_sum (u := Finset.univ)
      (A := fun i y => f i y * g i y)
      (A' := fun _ => (0 : E →L[ℝ] ℝ))
      (fun i _ => hasStrictFDerivAt_mul_zero (hf i) (hg i) (hf0 i) (hg0 i)))
```

Coordinate projections:

```lean
simpa using
  (hasStrictFDerivAt_apply (𝕜 := ℝ) idx (0 : Fin (deepestNReg H r) → ℝ))
```

Then `P12` for `2 ≤ L` is:

```lean
have hY :
    HasStrictFDerivAt (fun r0 : Reg => r0 idxY)
      (ContinuousLinearMap.proj idxY) 0 := by
  simpa using (hasStrictFDerivAt_apply (𝕜 := ℝ) idxY (0 : Reg))

have hquad :
    HasStrictFDerivAt
      (fun r0 : Reg => ∑ c : Fin r, r0 (idxX a c) * r0 (idxY c b))
      0 0 := by
  exact hasStrictFDerivAt_sum_mul_zero _ _ _ _
    (fun c => by simpa using hasStrictFDerivAt_apply (𝕜 := ℝ) (idxX a c) (0 : Reg))
    (fun c => by simpa using hasStrictFDerivAt_apply (𝕜 := ℝ) (idxY c b) (0 : Reg))
    (fun c => rfl) (fun c => rfl)

simpa [entry_formula, zero_add] using hY.add hquad
```

Mathlib v4.29 API to use:

```lean
HasStrictFDerivAt.mul
HasStrictFDerivAt.add
HasStrictFDerivAt.sub
HasStrictFDerivAt.fun_sum
hasStrictFDerivAt_apply
hasStrictFDerivAt_pi
ContinuousLinearMap.hasStrictFDerivAt
```

For the product collapse, avoid a general prefix/suffix theorem. Since `firstLayer = 0` and `lastLayer = L - 1`, prove only:

```lean
framedProd_regSlice_reindex_eq_of_one
framedProd_regSlice_reindex_eq_of_two_le
```

Use your `prodAux_succ_layer` to contain the dependent-Fin casts, plus two cast-free block algebra kernels:

```lean
firstShape_mul_corner_reindex
firstShape_mul_last_reindex
```

both proved by `Matrix.submatrix_mul_equiv` + `Matrix.fromBlocks_multiply` + `simp`.

That route leaves all calculus scalar and local. The only `prodAux` induction is the value collapse through interior corners.
tokens used
156,969
Use a hybrid of **(II) + remainder**, but keep the `prodAux` work algebraic, not differential.

Do **not** build the full recursive derivative value unless the product normal form gets stuck. The leanest general route is:

1. Prove a value-level regular-slice product collapse after the final outer `reindex`.
2. Read the three target blocks from that collapse.
3. Differentiate the resulting scalar formulas.

For `2 ≤ L`, the useful normal form is:

```lean
P(r0) =
  Matrix.fromBlocks
    (1 + Xfirst r0)
    ((1 + Xfirst r0) * Ylast r0)
    (Zfirst r0)
    (Zfirst r0 * Ylast r0)
```

For `L = 1`, it is just:

```lean
P(r0) =
  Matrix.fromBlocks (1 + Xfirst r0) (Ylast r0) (Zfirst r0) 0
```

So the target blocks become:

```lean
(P(r0).toBlocks₁₁ - 1) a b = r0 idxX
P(r0).toBlocks₂₁ a b       = r0 idxZ
P(r0).toBlocks₁₂ a b       = r0 idxY + ∑ c : Fin r, r0 (idxX a c) * r0 (idxY c b) -- if 2 ≤ L
```

For `L = 1`, the `P12` quadratic sum is absent. Also: `P21` is exactly linear; the quadratic `Zfirst * Ylast` lands in block `₂₂`, outside the regular residual.

Key calculus lemmas:

```lean
theorem hasStrictFDerivAt_mul_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (hfx : f x = 0) (hgx : g x = 0) :
    HasStrictFDerivAt (fun y => f y * g y) (0 : E →L[ℝ] ℝ) x := by
  simpa [hfx, hgx] using hf.mul hg
```

```lean
theorem hasStrictFDerivAt_sum_mul_zero
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ι → E → ℝ) (f' g' : ι → E →L[ℝ] ℝ) {x : E}
    (hf : ∀ i, HasStrictFDerivAt (f i) (f' i) x)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x)
    (hf0 : ∀ i, f i x = 0) (hg0 : ∀ i, g i x = 0) :
    HasStrictFDerivAt (fun y => ∑ i, f i y * g i y) 0 x := by
  simpa using
    (HasStrictFDerivAt.fun_sum (u := Finset.univ)
      (A := fun i y => f i y * g i y)
      (A' := fun _ => (0 : E →L[ℝ] ℝ))
      (fun i _ => hasStrictFDerivAt_mul_zero (hf i) (hg i) (hf0 i) (hg0 i)))
```

Coordinate projections:

```lean
simpa using
  (hasStrictFDerivAt_apply (𝕜 := ℝ) idx (0 : Fin (deepestNReg H r) → ℝ))
```

Then `P12` for `2 ≤ L` is:

```lean
have hY :
    HasStrictFDerivAt (fun r0 : Reg => r0 idxY)
      (ContinuousLinearMap.proj idxY) 0 := by
  simpa using (hasStrictFDerivAt_apply (𝕜 := ℝ) idxY (0 : Reg))

have hquad :
    HasStrictFDerivAt
      (fun r0 : Reg => ∑ c : Fin r, r0 (idxX a c) * r0 (idxY c b))
      0 0 := by
  exact hasStrictFDerivAt_sum_mul_zero _ _ _ _
    (fun c => by simpa using hasStrictFDerivAt_apply (𝕜 := ℝ) (idxX a c) (0 : Reg))
    (fun c => by simpa using hasStrictFDerivAt_apply (𝕜 := ℝ) (idxY c b) (0 : Reg))
    (fun c => rfl) (fun c => rfl)

simpa [entry_formula, zero_add] using hY.add hquad
```

Mathlib v4.29 API to use:

```lean
HasStrictFDerivAt.mul
HasStrictFDerivAt.add
HasStrictFDerivAt.sub
HasStrictFDerivAt.fun_sum
hasStrictFDerivAt_apply
hasStrictFDerivAt_pi
ContinuousLinearMap.hasStrictFDerivAt
```

For the product collapse, avoid a general prefix/suffix theorem. Since `firstLayer = 0` and `lastLayer = L - 1`, prove only:

```lean
framedProd_regSlice_reindex_eq_of_one
framedProd_regSlice_reindex_eq_of_two_le
```

Use your `prodAux_succ_layer` to contain the dependent-Fin casts, plus two cast-free block algebra kernels:

```lean
firstShape_mul_corner_reindex
firstShape_mul_last_reindex
```

both proved by `Matrix.submatrix_mul_equiv` + `Matrix.fromBlocks_multiply` + `simp`.

That route leaves all calculus scalar and local. The only `prodAux` induction is the value collapse through interior corners.

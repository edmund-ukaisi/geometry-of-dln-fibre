<task>
Lean 4 + Mathlib formalisation (DLNFibre). I am closing the general-L (L≥3) case of a
diffeo-invariance step `hstep2` in a deep-linear-network RLCT proof. I need an independent read on
the cleanest DECOMPOSITION before I build ~300+ lines. Diagnose the plan; do not write Lean.

## The target (`hstep2`, L≥3)
`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, where both functions of the flat parameter `x` share
the SAME reg term verbatim, differing only in the core summand:
  Φscore x = (∑ i, (regStraighten (split x)).1 i ^2) + Score x
  Φcore  x = (∑ i, (regStraighten (split x)).1 i ^2) + deepestCoreF H r (coreAbsorb (split x)).2.1
`split : Flat ≃ₜ DeepestSplit H r nGauge` (measure-preserving reindex; `split wstar = 0`).
`DeepestSplit H r nGauge = (Fin nReg → ℝ) × ((Fin (flatDim (deepestM)) → ℝ) × (Fin nGauge → ℝ))`
  (reg × reducedcore × spectator), `deepestM s = H s - r`.

## Banked facts (reuse; do NOT rebuild)
- `deepestCoreF H r y = ‖prod (deepestM) (decode y)‖²` (dlnLoss of the reduced chain at 0).
- coreAbsorb = `deepestCoreAbsorb` a homeomorph, and near 0:
    `deepestCoreF (coreAbsorb q).2.1 = frobSqMat (prod (deepestM) (fun s => decode(q.2.1) s + schurCorrection(q.1,q.2.2) s))`
    where `schurCorrection ... s = − Z_s (1+X_s)⁻¹ Y_s`, and `X_s,Y_s,Z_s = gaugeReadX/Y/Z (q.1,q.2.2) s`
    (linear reads off the reg+spectator slot), `T_s = decode(q.2.1) s` (the reduced core layer).
    So `deepestCoreF (coreAbsorb q).2.1 = ‖∏_s blockSchur(fromBlocks (1+X_s) Y_s Z_s T_s)‖²`.
- `Score x = ‖ blockSchur( reindex (endpointP0·(prod(symm x) − B)·endpointQL) ) ‖²`, with a `+1` corner
    inside the pivot (`(M₁₁+1)⁻¹`). endpointP0/QL are the block-triangular endpoint frames; hPtri
    (`P0.toBlocks₁₂=0`), hQtri (`QL.toBlocks₂₁=0`) available.
- Abstract Schur-product LDU recursion (banked, general L):
    `blockSchur (partProd C L) = coreProd C L`, where for a chain `C : (s:ℕ) → Matrix (r⊕m s)(r⊕m(s+1))`:
    `partProd C k = C 0·…·C(k-1)`, `blockSchur P = P₂₂ − P₂₁ (P₁₁)⁻¹ P₁₂`,
    `Kcoup C k = (C k)₂₁ (partProd C (k+1))₁₁⁻¹ (partProd C k)₁₂`,
    `coreProd C (k+1) = coreProd C k · (1 − Kcoup C k) · blockSchur(C k)`.
    Carries `Invertible` hyps on each layer pivot (k<L) and each partial-product pivot (k≤L).
    NOTE `Kcoup C 0 = 0` automatically (partProd C 0 = 1 ⟹ (partProd C 0)₁₂ = 0).
- Block-decomp seeds: `reindex_mul_fromBlocks`, `prod_eq_prodAux_mul_last` (prod = prodAux(L-1)·last),
    `rcore_eq_schur_of_corner_split` (the +1 corner: Schur over (Mw₁₁+1) = Schur of Mhat=fromBlocks 1 0 0 0 + Mw),
    `schur_frame_transform` (block-lower P·M·block-upper Q Schur = D_P·Schur(M)·D_Q, frame corners cancel).
- The general-L absorbing shear `Ψ = deepestPsiCoreShear K` on DeepestSplit: fixes reg (.1) and
    spectator (.2.2); on core, decode, do `S_s ↦ (1 − K_s q)·S_s` per layer, re-encode. BANKED:
    ContDiff ⊤ (given `hKcd: ∀s, ContDiff ⊤ (K s ·)`), `dΨ(0)=id` and `Ψ 0=0` (given `hK0: ∀s, K s 0=0`),
    packaged as `deepestPsiCoreShear_isLocalDiffeoAt`. `DeepestCoupling H r nGauge = (s:Fin L) →
    DeepestSplit → Matrix (Fin (deepestM s.castSucc)) (Fin (deepestM s.castSucc)) ℝ`.
- RLCT bridges: `rlctAtOn_diffeo_bridge_of` (given Psi:Flat→Flat ContDiff⊤, dPsi(wstar)=CLE, Psi wstar=wstar,
    and `Φcore∘Psi =ᶠ[𝓝 wstar] Φscore`, concludes `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`);
    `rlctAtOn_comp_homeomorph` (MP homeomorph transport); `rlctAtOn_comp_localDiffeo`.
- The L=2 analog is closed by a ~3000-line bridge using a DIFFERENT raw action `psiSplitRawL2` (acts on
    RAW core before Schur normalization). The general-L plan instead uses the banked `Ψ` acting on the
    ALREADY-Schur-normalized core (post-coreAbsorb), via the CONJUGATE g = coreAbsorb.symm ∘ Ψ ∘ coreAbsorb.

## The plan I intend to build
Flat diffeo `Psi := split.symm ∘ coreAbsorb.symm ∘ Ψ ∘ coreAbsorb ∘ split`. Then
`split (Psi x) = coreAbsorb.symm (Ψ (coreAbsorb (split x)))`; so
  core term of Φcore∘Psi: `deepestCoreF (coreAbsorb (split (Psi x))).2.1 = deepestCoreF (Ψ (coreAbsorb (split x))).2.1`
     (coreAbsorb∘coreAbsorb.symm cancel) `= ‖∏(1−K_s) S_s‖²` where S_s = blockSchur(fromBlocks(1+X_s)Y_s Z_s T_s).
  UNTWIST GOAL: `‖∏_s (1−K_s) S_s‖² = Score x`, with K_s = Kcoup(Cq) s for the raw gauge chain
     `Cq s := fromBlocks (1+X_s) Y_s Z_s T_s`. Since K_0 = 0, `∏_s(1−K_s)S_s = coreProd Cq L = blockSchur(partProd Cq L)`.
     Then relate `blockSchur(∏ Cq_s)` to `Score` via `prod_eq_prodAux_mul_last` + `rcore_eq_schur_of_corner_split`
     + `schur_frame_transform` (frames P0,QL) + the cast from DLN `prod` (Fin (H k) widths) to `partProd Cq L`
     (r⊕Fin(deepestM k) types).
  reg term: g fixes reg (.1) and spectator (.2.2) [coreAbsorb, Ψ, coreAbsorb.symm all fix them], and
     regStraighten's .1-output is core-independent (reads only reg+spectator), so
     `(regStraighten (split (Psi x))).1 = (regStraighten (split x)).1`.
Coupling K (piece 4): `K s q := Kcoup (Cq q) s` (width cast Fin L ↔ ℕ; m s = Fin(deepestM ...)).
  hK0: at q=0, X=Y=Z=0 and T=0 so Cq_s(0) = fromBlocks 1 0 0 0, partProd pivots = 1, off-blocks = 0 ⟹ K_s 0 = 0.
  hKcd: Kcoup involves Ring.inverse of partial-product pivots → smooth only where pivots invertible →
     multiply by a cutoff bump χ (support in the locus where all pivots invertible, =1 near 0), like the
     banked `schurCutoffShift`. But then K = χ·Kcoup, and the untwist identity ∏(1−K)S = coreProd only holds
     where χ=1 (near 0) — fine since Φcore∘Psi =ᶠ Φscore is a GERM at wstar.

## Questions
1. Is the CONJUGATE plan (Psi = split.symm∘coreAbsorb.symm∘Ψ∘coreAbsorb∘split) sound and the cleanest,
   or is there a hidden wall? In particular: is `Psi` genuinely ContDiff ⊤ and dPsi(wstar)=id-CLE given
   the banked pieces? `coreAbsorb`/`coreAbsorb.symm` are homeomorphs but is their ContDiff ⊤ + d(·)(0)=id
   banked (contDiff_coreShearHomeo / hasStrictFDerivAt_coreShearHomeo_symm_zero exist)? And `split` — is
   an affine measure-preserving reindex ContDiff ⊤ with derivative a CLE? Any subtlety composing 5 maps
   for the `rlctAtOn_diffeo_bridge_of` single-CLE derivative requirement?
2. Is `Cq s := fromBlocks (1+X_s) Y_s Z_s T_s` (RAW gauge chain, 1+X pivot, NO frames) the correct chain
   for the coupling K, given the untwist must land on `Score` (which has frames P0,QL and the deepBlk
   constants)? i.e., do the frames/deepBlk constants get ABSORBED into the frame-transform step
   (schur_frame_transform) so the coupling K itself is frame-free, or must K carry frame data?
3. hKcd cutoff: does multiplying Kcoup by a scalar cutoff bump χ preserve the untwist identity as a GERM
   (χ=1 near 0), AND keep hK0? Any issue that (1 − χ·Kcoup) is not the same as the (1−Kcoup) the recursion
   needs off the germ (should be irrelevant since we only need Φcore∘Psi =ᶠ Φscore)? Confirm or flag.
4. Biggest wall risk in this plan (rank the top 2), and the single cheapest de-risking check for each.
5. Should I build piece 4 (K + hKcd + hK0) as a fully standalone module now (bankable independent of
   piece 5), or is the coupling to piece 5's frame-transform tight enough that I should co-design them?
</task>

<output_contract>
Five numbered answers matching the five questions. For each, ≤8 sentences. Be concrete about Lean-level
obstructions (cast/defeq/instance/motive issues), not just math. End with a 3-line "BUILD ORDER"
recommendation (what to build first, second, third).
</output_contract>

<grounding_rules>
Flag clearly when you are INFERRING vs stating a known Mathlib/Lean fact. If a banked lemma's exact
availability is uncertain, say so and give the fallback. Do not invent Mathlib lemma names.
</grounding_rules>

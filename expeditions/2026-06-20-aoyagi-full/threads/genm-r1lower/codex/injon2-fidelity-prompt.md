<task>
Independent fidelity review of a just-completed Lean 4 (Mathlib) lemma in a research formalisation. I have already read all the code; I want a decorrelated second opinion on three SOUNDNESS/FIDELITY questions. Treat the Lean statements below as exact (transcribed from the source).

CONTEXT: L=2 deep-linear-network RLCT lower bound. `BparamsLeaf ha y : Params M` is a chart-parameter map; its component `0` is the layer-0 matrix, component `1` the layer-1 matrix; the radial scalar is hardwired to 1. We want: BparamsLeaf is INJECTIVE on the domain D = kLDU '' (pbo '' interiorLiveInjDom), where:
  - interiorLiveInjDom = {u | u leafPivot ≠ 0 ∧ ∀ j ∈ E, u j ≠ 0}, with E = Finset.univ (so: ALL coordinates nonzero).
  - pbo = pivotBlowupOn activeM leafPivot : scales every coord in `activeM` by the pivot value `x leafPivot`, fixes the pivot itself, fixes coords outside activeM. activeM does NOT contain any K-slot.
  - kLDU : per-coordinate map; on K-frame slots at boundary k, replaces coord by an entry of kLens(readK x k) (an LDU-rebuilt matrix); identity on all non-K coords.

THE MAIN LEMMA (sorry-free, axioms = [propext, Classical.choice, Quot.sound]):
  theorem interiorLive_BparamsLeaf_injOn : Set.InjOn (BparamsLeaf ha) (kLDU '' (pbo '' interiorLiveInjDom))
Proof structure: intro y hy y' hy' heq; from heq get h0 (BparamsLeaf y 0 = BparamsLeaf y' 0) and h1 (layer 1). Then:
  hK := slotReadV0_K_det_ne_zero_of_mem hy        -- (slotReadV0 ha y).1.det ≠ 0
  hV0 := slotReadV0_eq_of_BparamsLeaf0_eq hK h0    -- slotReadV0 y = slotReadV0 y'
  hN := (Nfun y = Nfun y' from hV0)
  (hW,hLeaf) := Wfun_Lfun_eq_of_BparamsLeaf1_eq hN h1
  Then (eIn ha).injective applied: show (eIn y).1 = (eIn y').1 (= slotReadV0, via eIn_projV0+hV0), (eIn y).2.1 = (eIn y').2.1 (= (Wfun,Lfun) readers, via hW/hLeaf), PUnit tail rfl. eIn is a LinearEquiv (Fin (flatDim M) → ℝ) ≃ₗ StairProd, flatDim M = routeMAmbient M definitionally.

KEY SUPPORTING LEMMA (the K-det discharge), which I want vetted hardest:
  theorem slotReadV0_K_det_ne_zero_of_mem (hy : y ∈ kLDU '' (pbo '' interiorLiveInjDom)) : (slotReadV0 ha y).1.det ≠ 0
Proof: obtain y = kLDU (pbo x₀) with x₀ ∈ interiorLiveInjDom. Establish hpbo_ne: ∀ q, (pbo x₀) q ≠ 0 (because all x₀ coords nonzero and pbo multiplies/keeps nonzeros). Goal becomes (Matrix.of (readK (kLDU (pbo x₀)) ⟨0⟩)).det ≠ 0. Rewrite with readK_kLDU_det:
    (Matrix.of (readK (kLDU x) k)).det = ∏ i, (matrixSplit (Matrix.of (readK x k))).2.1 i        [here x := pbo x₀]
so goal = ∏ i, (matrixSplit (Matrix.of (readK (pbo x₀) ⟨0⟩))).2.1 i ≠ 0. Via Finset.prod_ne_zero_iff reduce to each factor ≠ 0. (matrixSplit K).2.1 i is DEFINED as `fun i => K i i` (the diagonal). readK x k i j = x (chartIdxEquiv.symm ⟨k,...(i,j)...⟩) is a PURE coordinate projection of its argument x. So the diagonal entry (Matrix.of (readK (pbo x₀) ⟨0⟩)) i i = (pbo x₀)(some single index), which hpbo_ne says ≠ 0.

The three definitions I want you to assume exact:
  matrixSplit (LinearEquiv): toFun K = (lower-entries, fun i => K i i, upper-entries), so (matrixSplit K).2.1 = the diagonal.
  kLens K = matrixSplit.symm (lduCoreMap (matrixSplit K)); det(kLens K) = ∏ i (matrixSplit K).2.1 i (unit-triangular factors det 1).
  schurFrameMap (K,N,X,E) = (K, K*N, (X*K, X*K*N+E)).
  schurFrameMap_inj_of_det_ne_zero: from K.det≠0, recovers K (top-left), N (left-cancel K⁻¹·KN), X (right-cancel XK·K⁻¹), E (add_left_cancel). Requires IsUnit K.det.
  slotReadV0 ha y = (readK y ⟨0⟩, readN y ⟨0⟩, readX y ⟨0⟩, readE y ⟨0⟩) so .1 = readK y ⟨0⟩.
  slotReadV0_eq_of_BparamsLeaf0_eq: from h0, get layer0SchurMap y = layer0SchurMap y' where layer0SchurMap y = flatBlockLE (schurFrameMap (slotReadV0 y)); strip injective flatBlockLE LinearEquiv → schurFrameMap (slotReadV0 y) = schurFrameMap (slotReadV0 y'); apply schurFrameMap_inj_of_det_ne_zero hK.

QUESTIONS:
Q1 (K-det discharge soundness): Is the det discharge correct? Specifically: readK_kLDU_det rewrites the det of the POST-kLDU K-block into ∏ of the diagonal pivots of the PRE-kLDU K-block (readK x, x = pbo x₀). The factor it needs nonzero is (matrixSplit (readK (pbo x₀) ⟨0⟩)).2.1 i = the (i,i) diagonal entry of readK (pbo x₀) ⟨0⟩, which is a single coordinate of pbo x₀. Is there any way this "diagonal entry of readK" is actually a LENSED combination (so that the single-coordinate-nonzero argument fails)? Or is readK a genuine coordinate projection making this airtight? Also: is it legitimate to need only the PRE-kLDU coordinate nonzero (not the post-kLDU det directly)?

Q2 (no vacuity / domain match): The InjOn domain "all coords nonzero" is the complement of finitely many hyperplanes (full measure, dense, nonempty for routeMAmbient M ≥ 0). The downstream cov engine ldu_cov_of_differentiable_injOn consumes InjOn on {u | u p ≠ 0 ∧ ∀ j∈E, u j ≠ 0} with E=univ, and uses it in lintegral_image_eq_lintegral_abs_det_fderiv_mul on the punctured box. Is there any vacuity trap — e.g., could the InjOn be trivially true because the domain is empty, or could "all coords nonzero" accidentally be empty/degenerate? (routeMAmbient could be 0 only if flatDim=0.) Does the cov substitution genuinely require injectivity?

Q3 (recovery completeness / overclaim): The recovery reconstructs eIn's three components: V0 = slotReadV0 (the K,N,X,E frame), V1 = (Wfun, Lfun) readers, PUnit tail. Since eIn is a LinearEquiv (bijective), matching all three components forces y = y'. Is matching {V0, V1-pair, PUnit} EXHAUSTIVE of eIn's codomain StairProd (eihdV M) 2 — i.e., is there a hidden 4th component that goes unmatched, which would make (eIn y) = (eIn y') NOT follow from the three Prod.ext legs? The Prod.ext is: Prod.ext ?V0 (Prod.ext ?V1 ?PUnit). Is that the right nesting for a 3-deep product V0 × ((W,leaf) × PUnit)?
</task>

<output_contract>
Three sections Q1/Q2/Q3. For each: VERDICT (SOUND / FLAW-FOUND / UNDER-SPECIFIED), then 2-4 sentences. If FLAW-FOUND, give the minimal concrete counterexample or the exact line of reasoning that breaks. Be terse. End with a one-line overall: PASS or FAIL.
</output_contract>

<grounding_rules>
You are reasoning from the transcribed statements only; you do NOT have the repo. Flag any place where your verdict DEPENDS on a definition detail you cannot verify from what I gave (mark it "ASSUMPTION:"). Do not invent Mathlib lemma behavior; if a step's validity hinges on exact Mathlib semantics (e.g. Prod.ext associativity, LinearEquiv.injective), say so. Distinguish "this is mathematically sound" from "the Lean will typecheck" where relevant.
</grounding_rules>

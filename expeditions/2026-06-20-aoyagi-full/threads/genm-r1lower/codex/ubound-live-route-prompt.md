<task>
Lean 4 + Mathlib (v4.29) formalisation. I must build 3 analytic atoms for an interior achiever chart,
matching frozen sorry signatures in a contract I cannot edit. Decide the CHEAPEST SOUND route, and flag
which (if any) are genuinely blocked.

DEFINITIONS (all in DLNFibre.DLN.RLCT; M : Fin (2+1) → ℕ, so L=2, fixed depth):
- interiorLivePhi ha h0r h0c x = phiFlatLiveAt M ha (leafPivot) (kLDU x)
- interiorLiveUnit ha h0r h0c x = VvalGen (x leafPivot) M (tach M) (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (kLDU x)) (kLDU x)) hle
  where VvalGen u B hle = ∑ i, ∑ j, (HrGen u B hle i j)^2, HrGen = reindex of (chainOfMt u B hle).toChain.Hmat 0.
  Chain.Hmat / suffix are CommRing-generic, built by downward recursion (HmatAux/suffixAux) using only Matrix.mul / Matrix.add / reindex / fromBlocks.
  genBlkFlatLive's blocks are bmatStack/rmatPad of readK/X/N/E/W (each reader = a single coordinate x(idx), so continuous in x). rfinFixedPivot entries are `if (i,j)=(0,0) then 1 else x(leafSlot i j)`.
  kLDU is continuous AND differentiable (BANKED: differentiable_kLDU). (kLDU x) leafPivot = x leafPivot (BANKED: kLDU_leafPivot).

BANKED (reusable, proven): differentiable_kLDU, differentiable_kLens, differentiable_pivotBlowupOn,
  interiorLive_diff : Differentiable ℝ interiorLivePhi (so interiorLivePhi is CONTINUOUS),
  continuous_routeMCore : Continuous (routeMCore M), measurable_routeMCore,
  routeMCore_interiorLivePhi : routeMCore (interiorLivePhi x) = (x leafPivot)^2 * interiorLiveUnit x  (identity ∀x),
  interiorLiveUnit_nonneg : 0 ≤ interiorLiveUnit x  (sum of squares),
  achieverUfun = eval x UPolyGen (a NONZERO MvPolynomial, RouteMAchieverVvalPoly): achieverUfun_measurable, achieverUfun_ae_pos, MvPolynomial.ae_eval_ne_zero. BUT this is for the DEAD-LEAF genBlkFlatStruct decoder, NOT genBlkFlatLive+rfinFixedPivot+kLDU.
  Mathlib has full matrix-continuity API: Continuous.matrix_mul, continuous_matrix, Continuous.matrix_reindex, fromBlocks continuity, MvPolynomial.continuous_eval.
  Witness exists_UvalLiveR1_ne_zero_interior : ∃ w, UvalLiveR1 (...rfin=0...) w ≠ 0 (for the R1 chart, radial at structPivot — a DIFFERENT chart from phiFlatLiveAt; uses Function.update Rmat at pivot p, not rfinFixedPivot leaf).

THE 3 ATOMS:
1. interiorLive_image : ∀ε>0, ∃δ>0, interiorLivePhi '' [0,δ]^N ⊆ cubeBox N ε.
   Mirror is phi3333_image_subset_cubeBox: needs Continuous interiorLivePhi (HAVE, via interiorLive_diff) + interiorLivePhi 0 = 0. PROBLEM: rfinFixedPivot plants a fixed 1 at leaf pivot (0,0), so interiorLivePhi 0 is likely ≠ 0 (the chart does not map 0→0). Is there another image argument that doesn't need φ0=0?
2. interiorLive_Umeas : Measurable (interiorLiveUnit). interiorLiveUnit is continuous in x IF I thread Continuous through the fixed-depth (L=2) Chain.Hmat recursion (all building blocks continuous). No such VvalGen-continuity helper is banked. Alternatively: rate identity gives (x leafPivot)^2 * interiorLiveUnit = continuous, but division fails on the pivot-zero hyperplane.
3. interiorLive_Ubound : box-bound (Continuous on compact box ⟹ max) + a.e.-positivity (∀ᵐ x, 0 < interiorLiveUnit x). a.e.-positivity is the SOUNDNESS PIN. To use MvPolynomial.ae_eval_ne_zero I need interiorLiveUnit = eval x (nonzero poly). That needs kLens/kLDU over MvPolynomial (kLens = matrixSplit.symm ∘ lduCoreMap ∘ matrixSplit, all ℝ-only LinearEquiv/FiniteDimensional). Generic-ifying matrixSplit/lowMatL/upMatL/lduCoreMap to CommRing + a kLDU_eval naturality lemma is ~150-250 new LoC. The dead-leaf witness (achieverUfun_wInt_ne_zero) is for genBlkFlatStruct, not the live+rfinFixedPivot decoder.

Already established by me: interiorLiveUnit = G ∘ kLDU where G y = VvalGen (y leafPivot) (genBlkFlatLive (rfinFixedPivot y) y) hle (clean, since (kLDU x) leafPivot = x leafPivot).
</task>

<output_contract>
Three numbered sections, one per atom, IN THIS ORDER: image, Umeas, Ubound.
For EACH: (a) verdict — ACHIEVABLE-CHEAP / ACHIEVABLE-MEDIUM / BLOCKED-NEEDS-INFRA; (b) the single cheapest sound route in ≤5 concrete Lean steps (name the lemmas/tactics); (c) the precise blocker if BLOCKED.
Then a final section "CHEAPEST OVERALL ORDER" — which to attempt first, and whether any unlock the others.
Be concrete about Lean lemma names. Flag any step you are INFERRING vs KNOW exists in Mathlib v4.29.
</output_contract>

<grounding_rules>
You may propose Mathlib lemma names but must mark each as KNOWN (you're confident it exists at v4.29) or GUESS (verify before use). Do not assume any DLNFibre lemma exists beyond those I listed as BANKED. If a route needs a lemma I did not list as banked, call it out as new work. Distinguish "continuous ⟹ measurable" (trivial) from "a.e.-positive" (needs zero-set nullity, much harder).
</grounding_rules>

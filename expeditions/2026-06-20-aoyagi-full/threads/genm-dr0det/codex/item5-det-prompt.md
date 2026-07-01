<task>
Lean 4 + Mathlib formalisation. I am building the "deepRank=0" interior det for a deep-linear-network
box-divergence proof. I need to validate the DESIGN of a boundary factor B so that a chart determinant
equals EXACTLY a single-axis monomial |u_p|^(minAdm-1), with |det DB| = 1.

SETUP (all banked, sorry-free):
- routeMAmbient M = ambient flat coordinate space (Fin N -> R), N = routeMAmbient M.
- activeM M ha = a Finset of coords, = activeEImg ∪ activeLeafImg. At deepRank=0 (e.g. M=(1,1,2)):
  activeLeafImg = ∅ (leaf block is 0-dim, Text M (tach M) 2 = 0), so activeM = activeEImg, card = minAdm = M0*M1.
- eBlockPivot ∈ activeM is ONE of the E-block slots (an activeSlotE at boundary 0).
- pivotBlowupOn active p₀ x = fun i => if i=p₀ then x p₀ else if i ∈ active then x p₀ * x i else x i.
  (pivot fixed to itself; other active coords scaled by x p₀; spectators fixed.)
- The chart φ := phiFlatLiveAt M ha _ eBlockPivot x
     = phiGen (x eBlockPivot) M tach (genBlkFlatLive M tach ha (rfinFixedPivot x) x).
  Here rfinFixedPivot is a LEAF reader; at deepRank=0 the leaf block is 0-dim so it's a vacuous 0×W matrix.
  phiGen u ... = paramsEquivFlat (chartParamsGen u ...). chartParamsGen is per-layer reindex of Agen.
  Agen depends only on (Nblk k, Wblk k, Cgen (k+1)). At an INTERIOR boundary k=0,
     Cgen v ... = schurFrameProd ... v (readK x)(readX x)(readN x)(readE x)   [banked]
  and schurFrameProd ... v K X N E = schurFrameProd ... 1 K X N (v • E)   [banked, "u_to_E"].
- readE x ⟨0⟩ i j = x (activeSlotE ... ⟨0⟩ i j). The E-slots ARE the activeM slots at deepRank=0.
- The radial calculus radialComp_abs_det_at gives, for φ = B ∘ pivotBlowupOn active p₀ with
  HasFDerivAt B DB (pbo p₀ u):  |det Dφ u| = |u p₀|^(minAdm-1) · |det DB|.  So I want |det DB| = 1.

THE LEAF-CASE TEMPLATE (works, sorry-free) for a leaf pivot p₀ (NOT an E-slot):
- B = BchartLeaf reads residual coords with radial hardwired to 1: for the leaf it uses rfinDirect
  (reads leaf slot (0,0) directly, not pinned), for the E-block it uses readE directly.
- The match works because ALL activeM slots (E and leaf) ≠ leaf-pivot, so pbo scales them uniformly by x p₀,
  and readE(pbo x) = (x p₀)·readE x on EVERY E-slot; then schurFrameProd_u_to_E moves the (x p₀) into E.
- In the leaf case |det DB| = ∏ engine (nontrivial: K-block LDU gives exponents). That case has K-blocks.

THE deepRank=0 DIFFICULTY (role inversion):
- Now p₀ = eBlockPivot IS an E-slot. So readE(pbo x) at the PIVOT E-slot = x eBlockPivot (UNSCALED,
  pbo fixes the pivot to itself), while at OTHER E-slots = (x eBlockPivot)·(x slot) (scaled).
- On the chart side, schurFrameProd_u_to_E turns Cgen (x eBlockPivot) into schurFrameProd 1 K X N
  ((x eBlockPivot) • readE x). At the pivot E-slot this is (x eBlockPivot)·(readE x at pivot) =
  (x eBlockPivot)·(x eBlockPivot) = (x eBlockPivot)^2, but readE(pbo x) at pivot = x eBlockPivot. MISMATCH.
- So the B-decoder's E-reader must PIN the pivot E-slot to 1 (analog of rfinFixedPivot which pins leaf (0,0)):
  define readE_B(pbo x) = (if E-slot = pivot then 1 else (pbo x)(E-slot)). Then
  (x eBlockPivot) • readE_B(pbo x) at pivot = (x eBlockPivot)·1 = x eBlockPivot = readE(pbo x) ✓, and at
  non-pivot = (x eBlockPivot)·(x eBlockPivot · x slot)? NO — that overscales. Let me restate precisely below.

MY PROPOSED DESIGN — please validate or correct:
  B reads chart params with radial=1 and an E-reader Ehat that reads (pbo x) directly on ALL E-slots
  EXCEPT it does NOT scale — i.e. B := paramsEquivFlat (chartParamsGen 1 M tach (genBlkFlatLive ... rfin' y))
  evaluated at y = pbo x, where the E-block is read by readE directly from y. Then:
    chart side at pivot E-slot: Cgen(x eBlockPivot) has E-entry = (x eBlockPivot)·(readE x @pivot)
       = (x eBlockPivot)·(x eBlockPivot).   [since readE x @pivot = x eBlockPivot]
    B side at pivot E-slot: Cgen(1) has E-entry = readE(pbo x)@pivot = (pbo x)(pivot) = x eBlockPivot.
  These differ by a factor (x eBlockPivot). So a DIRECT readE on the B side does NOT match.

QUESTIONS (answer each, ranked, concrete):
1. Is |det DB| = 1 actually the right target at deepRank=0, or is it |det DB| = |u_p| (i.e. does the
   single factor (x eBlockPivot) that the LEAF case would put on the leaf-radial instead land on |det DB|)?
   The build-state note says "det = EXACTLY single-axis |u_p|^{minAdm-1} (kLDU=id at deepRank=0 drops a
   factor)". Reconcile: with p₀ an E-slot, the pivot E-slot is BOTH the radial axis (contributing
   |u_p|^{minAdm-1} via radial card) AND an E-residual coordinate. Does the chart-param map read the pivot
   E-slot at all (given the radial already consumed it)? i.e. should B's E-reader SKIP/pin the pivot slot?
2. What is the correct definition of B's E-reader so that (a) the chart-param match holds EXACTLY and
   (b) |det DB| = 1? Give the reader as a piecewise (pivot slot -> ?, non-pivot E-slot -> ?).
3. Sanity check on a 1-D toy: M=(1,1,2), minAdm = M0*M1 = 1. Then activeM.card = 1 = minAdm, so
   |u_p|^(minAdm-1) = |u_p|^0 = 1, and the radial is over a SINGLETON active set. Does the whole det then
   collapse to |det DB| alone? If active.card=1 the "other E-slots" set is empty. Work out the det for this
   minimal case explicitly to anchor the general claim.
4. Given the singleton subtlety in Q3, is the RIGHT general statement "|det Dφ| = |u_p|^(minAdm-1)" with the
   B-factor being genuinely identity-like (det 1), and is there any hidden Jacobian factor from the E-block
   residual coords being SCALED by pbo that I am missing (the non-pivot E-slots get x_p·x_j — does the
   chart-param read them scaled, contributing extra |u_p| factors that must cancel)?
</task>

<output_contract>
Answer Q1-Q4 in order, each ≤ 8 sentences. For Q2 give the explicit piecewise reader. For Q3 give the
explicit 1-line det for M=(1,1,2). End with a 3-line VERDICT: (a) is |det DB|=1 correct? yes/no;
(b) the one correct B E-reader definition; (c) the single biggest risk to the "pure single-axis monomial"
claim.
</output_contract>

<grounding_rules>
This is a design question about a specific banked Lean construction. Distinguish clearly what FOLLOWS from
the stated banked lemmas (schurFrameProd_u_to_E, pivotBlowupOn def, radialComp_abs_det_at) vs what is a
plausible-but-unverified inference. Flag any step where you are guessing the behavior of a definition I did
not fully specify (e.g. how chartParamsGen folds the E-block into the layer matrix determinant).

<task>
Lean 4 + Mathlib v4.29 formalisation. I must prove ONE determinant equality (`hDtot`) and I need the
single most-tractable Lean route, given the EXACT atoms already banked. This is a deep DLN-fibre
formalisation; assume I know the math. I need a tactical/structural verdict, not the math.

THE GOAL (`hDtot`):
  `|LinearMap.det (Dtot ha (pbo u))| = |det K| ^ (r + c)`
where (all over OPAQUE widths `Text M (tach M) k`, `Wext M k`, at L=2):
  `Dtot ha y₀ = (paramsEquivFlatCLE M).toCLM.comp (fderiv ℝ BparamsLeaf y₀) |>.toLinearMap`
    : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ),  N = flatDim M = routeMAmbient M = ∑_s M_s·M_{s+1}.
  `BparamsLeaf ha y = chartParamsGen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirect ha y) y) hle`
    : (Fin N → ℝ) → Params M,  Params M = (s : Fin 3) → Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ.
  `paramsEquivFlat` is a fixed measure-preserving linear coordinate-reindex (|det| = 1), so
  `|det Dtot| = |det (fderiv BparamsLeaf y₀)|` once we read `fderiv BparamsLeaf` as an endo via the flatten.
  `K = readK ⟨0⟩` at the blown-up point; `r = Text1 − Text2`, `c = Wext1 − Text2`.

STRUCTURE (numerically VERIFIED by me at (3,3,4), exact): writing `BparamsLeaf y` per Params-layer:
  - layer 0 output = `Agen 1 .. 0 = Cgen 1` (the Schur frame `C1`), c0 = Wext0−Text1 = 0 so no chainA lift.
    `C1 = bmatStack(K,X)·chainQ(N) + 1·rmatPad(E)` = Schur frame [[K, K·N],[X·K, X·K·N + E]] over
    inputs {K, X, N, E}. Map (K,X,N,E) ↦ C1 IS exactly `schurFrameDeriv X K N` (banked: `schurFrameDeriv_det`
    gives `det = K.det^(r+c)`).
  - layer 1 output = `Agen 1 .. 1 = chainA(N, W, C2)`, C2 = rfinDirect (the leaf, read directly).
    chainA kept row = `C2 − N·W`, lift rows = `W`. Map (W, leaf) ↦ Agen1 is block-triangular, det 1.
  - THE COUPLING: N (= readN ⟨0⟩) is SHARED: it feeds layer-0's frame (K·N, X·K·N) AND layer-1's
    kept row (−N·W). Reordered Jacobian: rows=[C1 ; Agen1], cols=[{K,X,N,E} ; {W,leaf}] is
    BLOCK-LOWER-TRIANGULAR: J01 = 0 EXACTLY (C1 independent of W,leaf), J10 ≠ 0 (Agen1 depends on N).
    det J00 = K.det^(r+c), det J11 = ±1, total = product.

BANKED ATOMS (Lean, all sorry-free):
  - `stairMap_abs_det_twoConj (V) (n) (f) (c) (eIn eOut : E ≃ₗ StairProd V n) (D) (hD : eOut∘D∘eIn.symm = stairMap V n f c) (hreg : |det (eOut.symm∘eIn)| = 1) : |det D| = ∏_s |det (f s)|`.
  - `lowerTri (f : M→ₗM) (g : N→ₗN) (h : M→ₗN) : M×N →ₗ M×N := (m,n) ↦ (f m, g n + h m)`, and `lowerTri_det : det (lowerTri f g h) = f.det * g.det`.
  - `schurFrameDeriv X K N : SchurInc t r c →ₗ SchurInc t r c` with `schurFrameDeriv_det : det = K.det^(r+c)`.
  - fderiv VALUE CLMs already built (opaque width): `chainAFDeriv`/`hasFDerivAt_chainA`,
    `chainQFDeriv`/`hasFDerivAt_chainQ`, `hasFDerivAt_Cgen_interior`, `hasFDerivAt_Agen_interior`,
    `hasFDerivAt_Agen_leaf`. Plus differentiability atoms `diffAt_matmul/read/smul`.
  - `paramsEquivFlatCLE` (CLE, measure-preserving), and the reduction `Bchart_abs_det_eq_Dtot` already
    strips paramsEquivFlat: `|det (fderiv BchartLeaf)| = |det Dtot|`.

The prior thread NAMED hDtot as "a cast-heavy MULTI-TIDE piece, not a 3-4-attempt fill", citing the
opaque-width StairProd `eIn/eOut` construction + the `eOut∘Dtot∘eIn.symm = stairMap` entry-match.

THREE CANDIDATE ROUTES:
(A) Full `stairMap V 2` + build `eIn eOut : (Fin N→ℝ) ≃ₗ StairProd V 2` over opaque Params/flat widths,
    prove the entry-match, fire twoConj.
(B) Mirror the banked (2,2,2) `litMatLT` template: factor `BparamsLeaf = pack_M ∘ T`, reindex
    `toMatrix' (fderiv T)` via a slot bijection to an explicit block-lower-triangular matrix; det via
    `Matrix.det_of_lowerTriangular`. (Worked at (2,2,2) but used literal `![…]` — needs opaque-width
    generalization of the slot bijection + the per-entry collapse.)
(C) Use `lowerTri`/`lowerTri_det` directly at the LINEAR-MAP level: build ONE linear equiv
    `e : (Fin N→ℝ) ≃ₗ (V0 × V1)` (V0 = Schur-frame input/output space, V1 = chain space), show
    `Dtot = e.symm ∘ lowerTri f g h ∘ e'` for input equiv e', identify f with schurFrameDeriv (det K^(r+c))
    and g with the chain unit (det 1). Essentially (A) with n=2 unrolled to one lowerTri, possibly
    skipping the StairProd nesting.

My read: the genuinely hard sub-pieces are shared across all three: (i) `fderiv BparamsLeaf y₀` as an
explicit CLM assembled from the atoms; (ii) the input slot-partition equiv `eIn` ((Fin N→ℝ) ≃ role
blocks {K,X,N,E,W,leaf}) over opaque widths via chartIdxEquiv; (iii) identifying the layer-0 block of
the assembled fderiv with `schurFrameDeriv` (matching readers + radial-1 + the c0=0 collapse).
</task>

<output_contract>
1. RANK the three routes (A/B/C) by total Lean tractability for a single multi-step thread, given the
   banked atoms. One sentence each on why.
2. For the TOP route: list the ordered sub-lemmas (≤8), each with a one-line "what it proves" and a
   risk tag (LOW/MED/HIGH) + the specific Mathlib/cast hazard if HIGH.
3. Identify the SINGLE most likely wall (the sub-piece where a green-but-wrong reindex or an
   intractable opaque-width cast hides), and the cheapest way to de-risk it FIRST.
4. VERDICT: is this genuinely reachable in one focused thread (state the dominant cost), or is the
   prior "multi-tide wall" assessment correct? If a wall: name the precise sub-goal that walls.
Be terse and concrete. ≤500 words total.
</output_contract>

<grounding_rules>
You have NOT seen the Lean files. Treat my structural claims as given (they are numerically verified
or read off the banked signatures). Flag any step where you're inferring vs. relying on a stated fact.
Do not invent Mathlib lemma names; if you reference one, mark it "(verify exists)".
</grounding_rules>

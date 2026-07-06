<task>
Lean 4 + Mathlib v4.29 formalisation. DE-RISK GATE decision. A prior multi-tide thread named a WALL
("hDtot") for identifying the layer-0 block of `fderiv BparamsLeaf y₀` with `schurFrameDeriv`. I must
decide, BEFORE building, whether a specific CLEANER factorization route dodges that wall or re-imports it.

SETTING (all banked, sorry-free):
- `BparamsLeaf ha y : Params M = (s : Fin (L+1)) → Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ`,
  L=2. Its layer-0 component is
  `(BparamsLeaf ha y) ⟨0,_⟩ = reindex (finCongr _) (finCongr _) (Agen 1 M (tach M) (genBlkFlatLive … (rfinDirect y) y) hle 0)`.
- At the `tach` path, the residual width at boundary 0 is `c0 = Wext M 0 − Text M (tach M) 1 = M0 − M0 = 0`
  (structAdm identity boundary). So `chainA`'s lift block is empty and
  `Agen 1 … 0 = Cgen 1 … 1` EXACTLY (banked pattern Agen0_222_eq/Agen0_3333_eq via `chainA_apply_castAdd` + N0·W0=0).
- `Cgen_live_interior_eq_schurFrameProd` (banked): `Cgen 1 … 1 = schurFrameProd M (tach M) 1 h1 h2 1 (readK)(readX)(readN)(readE)`,
  a SINGLE block matrix `Matrix (Fin (Text M (tach M) 1)) (Fin (Wext M 1)) ℝ` (= the 2×2 frame at (3,3,4)).
- `schurFrameProd` block-entry lemmas (banked): its (castAdd a, castAdd b) entry = K a b; (castAdd,natAdd)=K·N;
  (natAdd,castAdd)=X·K; (natAdd,natAdd)=X·K·N+1·E. Row split = `Fin t ⊕ Fin (Ts−Ts1)`, col split = `Fin t ⊕ Fin (Ws−Ts1)`,
  glued by `Fin.cast (castAdd/natAdd)`. (t=Text(s+1), r=Text s−Text(s+1), c=Wext s−Text(s+1).)
- `schurFrameMap (z : SchurInc t r c) = (z.K, z.K*z.N, (z.X*z.K, z.X*z.K*z.N + z.E))` where
  `SchurInc t r c = Matrix(t,t) × Matrix(t,c) × Matrix(r,t) × Matrix(r,c)` is a TUPLE OF 4 MATRICES (NOT a block matrix).
  Banked: `schurFrameMap_hasFDerivAt z : HasFDerivAt schurFrameMap (schurFrameD z) z`, and
  `schurFrameD z = LinearMap.toContinuousLinearMap (schurFrameDeriv z.X z.K z.N)`, with
  `schurFrameDeriv_det : det (schurFrameDeriv X K N) = K.det^(r+c)`.
- Readers `readK/X/N/E y i j = y (someFixedIndex i j)` are LINEAR coordinate reads (`y ↦ y (idx)`),
  fderiv atom = `hasFDerivAt_apply`.
- NO `SchurInc ≃ (block matrix)` flattening equiv exists yet (checked by rg). It would have to be built.

THE PROPOSED CLEANER ROUTE (the brief's recommendation):
1. Build `slotReaderV0 : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] SchurInc t r c` = the LINEAR map reading
   (readK, readN, readX, readE) into the SchurInc tuple (NOT a full ambient partition — a one-sided read).
2. Build a `reindex`/flatten CLE `flat : SchurInc t r c ≃ₗ Matrix (Fin (Text M (tach M) 1)) (Fin (Wext M 1))`
   sending the tuple `(A,B,C,D)` to the block matrix `[[A,B],[C,D]]` over the opaque `castAdd/natAdd` Fin splits.
3. Prove `(fun y => Agen 1 … 0)  =  reindex_layer0 ∘ flat ∘ schurFrameMap ∘ slotReaderV0` as functions of y
   (using the banked Agen0-collapse + Cgen=schurFrameProd + the block-entry lemmas to identify
   `flat (schurFrameMap (K,N,X,E)) = schurFrameProd … 1 K X N E`).
4. Chain rule: `fderiv (layer-0) y₀ = reindex_layer0 ∘L schurFrameD(slotReaderV0 y₀) ∘L slotReaderV0`
   (slotReaderV0 linear → own fderiv; schurFrameMap_hasFDerivAt; reindex/flat linear).
5. The V0→V0 sense of this fderiv is `schurFrameDeriv X K N` (det `|det K|^{r+c}`). GATE PASSES.

THE NAMED PRIOR WALL (route C, which this is meant to dodge):
`slotEquiv_BparamsLeaf_twoBlock` — a FULL ambient partition `(Fin N → ℝ) ≃ₗ V0 × V1` over opaque Text/Wext
widths through `chartIdxEquiv.symm` — green-but-WRONG reindex (N,E, or layer slice misordered) hides there.
Prior verdict: multi-tide wall. Codex (decorrelated) had said "I agree with the wall UNLESS
`projV0 ∘ fderiv BparamsLeaf y₀ ∘ inclV0 = schurFrameDeriv X K N` closes cleanly first."

THE DECISION I NEED: Does the cleaner route's `flat` CLE (step 2) — the `SchurInc tuple ≃ block matrix`
flatten over opaque `castAdd/natAdd` Fin splits — re-import the SAME opaque-Fin-reindex difficulty as the
named wall's `slotEquiv_BparamsLeaf_twoBlock`, or is it GENUINELY EASIER because:
  (a) it is a ONE-SIDED read (slotReaderV0) + a flatten of a 4-tuple into ONE block matrix, NOT a full
      ambient input/output partition equiv;
  (b) the four block-entry lemmas `schurFrameProd_block_K/KN/XK/XKNuE` ALREADY give the entrywise identity
      `flat(tuple) = schurFrameProd` at the explicit `Fin.cast(castAdd/natAdd)` indices — so `flat` need not
      be a free-standing equiv; I can define `flat` directly via `fromBlocks`/`Sum.elim` and prove the entry
      match by the banked block lemmas;
  (c) crucially, step 5 only needs the V0→V0 block; `schurFrameD z = schurFrameDeriv z.X z.K z.N` IS the
      target already, so NO V1 partition, NO J01/J10/J11 blocks, NO lowerTri — the gate is JUST the
      composite `reindex ∘L schurFrameD ∘L slotReaderV0` having the right form.
</task>

<output_contract>
1. VERDICT (one line): does the cleaner route dodge the wall (TRACTABLE) or re-import it (WALL)?
2. The SINGLE riskiest sub-goal in the cleaner route, named precisely, with WHY it is/ isn't the same
   opaque-Fin difficulty as `slotEquiv_BparamsLeaf_twoBlock`.
3. Is building `flat` as a free-standing `≃ₗ` over opaque Fin REQUIRED, or can step 3's identity
   `flat(schurFrameMap(K,N,X,E)) = schurFrameProd … 1 K X N E` be proven entrywise via the banked block
   lemmas WITHOUT a free equiv (i.e. define flat by fromBlocks/reindex and discharge by Matrix.ext + the 4
   block lemmas + the row/col castAdd/natAdd case split)? Which is cheaper for the GATE specifically.
4. The cheapest concrete sub-goal ordering (≤6 steps) to either PASS the gate or hit the wall fast.
5. Where a green-but-WRONG proof could hide (the slot-order / cast trap) and the one check that catches it.
Be concrete about Lean v4.29 Matrix/Fin idioms. Flag inference vs. fact.
</output_contract>

<grounding_rules>
You have only the description above (no repo access). State which claims you take as given vs. infer.
Do not invent Mathlib lemma names; if you reference one, mark it as "verify-exists". The decision (dodge vs.
re-import) is what I am buying — be decisive and give the reason.
</grounding_rules>

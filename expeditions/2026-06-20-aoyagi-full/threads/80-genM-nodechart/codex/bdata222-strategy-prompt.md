<task>
Lean 4 + Mathlib v4.29 formalisation. I must construct a `BData M222 tach222 ...` term (an interface
structure) for the concrete (2,2,2) DLN node, whose key field `hmap` is the MAP IDENTITY:

  phiFlatLiveR1 M222 tach222 ha hN 1 hp1 hp2 rfin = B ∘ pivotBlowupOn active (structPivot)

where:
- `structPivot M hN = ⟨0, hN⟩ : Fin 8` (slot 0; routeMAmbient M222 = flatDim M222 = 8).
- `phiFlatLiveR1 ... rfin x = phiGen (x 0) M222 tach222 (genBlkFlatLiveR1 M222 tach222 ha 1 hp1 hp2 (rfin x) x) hle`
  and `phiGen u M t B hle = paramsEquivFlat M (chartParamsGen u M t B hle)`, where
  `chartParamsGen u M t B hle s = reindex (Agen u M t B hle s.val)` (the chain layers).
- `genBlkFlatLiveR1` is the structured decoder. Its block data is read from DISJOINT flat slots via
  the readers `readK ⟨0,_⟩ i j = x ((chartIdxEquiv M222 (tDesc) h0 hc hL).symm ⟨0, Sum.inl (...frameSplit... (i,j))⟩)`,
  similarly `readX`, `readN`, `readW` (lift slot Sum.inr). The pivot Rmat block is OVERRIDDEN to the
  FIXED `pivotEIndicator` (literal 1 at (0,0)), via `Function.update`. The leaf `Rfin L := rfin`.
- Codex (sympy-verified earlier) gives the explicit blocks for genBlkFlatLiveR1 M222 with coords
  (u=pivot, a=readK, b=readX, n=readN, w0,w1=readW, lf0,lf1=leaf):
    Agen0 = [[a, a·n],[a·b, a·b·n + u]]
    Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]
  and the FAITHFUL decomposition φ = B ∘ π with π = pivotBlowupOn({pivot,lf0,lf1})(pivot)
  scaling L0=u·lf0, L1=u·lf1; B reads pivot as ordinary coord; det Dπ = u², det DB = a².

THE OBSTACLE: `chartIdxEquiv` is defined as `(finCongr ...).trans (Fintype.equivFin (ChartIdx M t)).symm`
— i.e. via `Fintype.equivFin`, which is `Classical.choice`-based and NONCOMPUTABLE/OPAQUE. So
`(chartIdxEquiv M222 ...).symm ⟨0, Sum.inl ...⟩` does NOT reduce by `decide`/`rfl` to a concrete `Fin 8`
slot number. I cannot pin which `x`-slots `a,b,n,w0,w1` live in.

So `pivotBlowupOn active 0` (which is `fun i => if i = 0 then x 0 else if i ∈ active then x 0 * x i else x i`)
acting on the chart — I cannot show by concrete slot numbers that it leaves the a,b,n,w0,w1 reader slots
fixed. I CAN choose `rfin` and `active` freely (they're parameters of BData / phiFlatLiveR1).

I have full template machinery banked for the FREE-pivot (different) decoder `B_det222`/`phi222`:
`Agen0_222_eq`, `Agen1_222_eq` (explicit 2×2 layer matrices), `chartParamsGen_eq_chartParams222`,
`pack222`/`T222`/`pb222`/`shear222`/`bsubst222`, `T222_hasFDerivAt`, `T222Deriv_abs_det = |u0|²·|u4|`,
`Q222CLM_abs_det = 1` (paramsEquivFlat∘pack measure-preserving). But that decoder reads slots
via explicit `!![x 4; x 5]` etc — NOT through the opaque chartIdxEquiv readers.
</task>

<output_contract>
Rank the candidate Lean strategies for discharging `hmap` (the map identity) for the OPAQUE-reader
decoder genBlkFlatLiveR1 M222, cheapest-first. For the top recommendation, give the precise proof
skeleton (named Mathlib/lemma steps), and the single biggest risk. Specifically address:

1. Can I AVOID needing concrete reader-slot numbers entirely? E.g. define `active` and `rfin` in terms
   of the readers' OWN slots: active = {structPivot, (leaf slot 0), (leaf slot 1)} where the two leaf
   slots are `(chartIdxEquiv...).symm ⟨0, Sum.inl (leaf-role entry)⟩` (the same opaque map), and prove
   `pivotBlowupOn active 0` leaves the a/b/n/w slots fixed via INJECTIVITY of chartIdxEquiv.symm
   (reader-slot ≠ active-slot because the ChartIdx indices differ), without ever computing the Fin 8 value?

2. Is it cleaner to NOT factor through pivotBlowupOn at the flat level, but instead define B as
   `paramsEquivFlat ∘ chartParamsGen 1 (decoder-reading-pre-scaled-leaf)` and prove the chart-param
   equality `chartParamsGen (x 0) (LiveR1 leaf=rfin x) = chartParamsGen 1 (LiveR1 leaf=u·rfin)` PER-LAYER
   via Agen, i.e. show the two explicit Agen0/Agen1 matrices coincide after substituting the pbo-scaled
   coords — treating the reader values a,b,n,w0,w1 as opaque scalars `s_k := readK ⟨0,_⟩ 0 0` etc.?
   (Note: the SUPERSEDED RouteMBData B = phiGen 1 (genBlkFlatLiveR1) is the WRONG B — it reads E(0,0) as
   constant 1, not the pivot coord. The faithful B reads the pivot additively. So `chartParamsGen 1
   (genBlkFlatLiveR1)` is NOT my B.)

3. Given the additive `+u` (pivot coord) in Agen0[1,1] vs the multiplicative pivotBlowupOn: the
   decomposition has B reading the pivot slot 0 DIRECTLY (B(y)[Agen0 1 1] = a·b·n + y_0, since pbo leaves
   slot 0 = the pivot itself, y_0 = x_0). Confirm this is consistent and the cleanest B is just
   "chartParamsGen built from the SAME readers but with leaf read post-pbo and pivot read as ordinary
   coord y_0" — i.e. is B literally `fun y => paramsEquivFlat (explicit chartParams from readers-of-y +
   y_0 pivot + (y at leaf slots) leaf)`?
</output_contract>

<grounding_rules>
Flag clearly which steps are standard Lean idioms you are confident exist in Mathlib v4.29 vs which are
inferences about this specific (opaque-equiv) setup that I must verify by building. Do NOT assume the
reader slots are concrete. The deliverable is the (2,2,2) concrete BData term, sorry-free.
</grounding_rules>

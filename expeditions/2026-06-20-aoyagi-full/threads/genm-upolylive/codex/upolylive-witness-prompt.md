<task>
Lean 4 + Mathlib (v4.29) formalisation. I need the cleanest proof of a NONZERO-polynomial
witness `UPolyLive ≠ 0`, where `eval u UPolyLive = interiorLiveUnit u` (already proven) and
`interiorLiveUnit u = sqSumHmat0 (chainOfMt (u leafPivot) (genBlkFlatLive ha (rfinFixedPivot ha (kLDU u)) (kLDU u)) hle)`.

To get `UPolyLive ≠ 0` it SUFFICES to exhibit ONE point `w` with `interiorLiveUnit w ≠ 0`
(since `eval w UPolyLive = interiorLiveUnit w`).

CANDIDATE WITNESS: `w := wInt M ha p` (the banked interior-drop witness at an interior pivot `p`,
1 ≤ p < L, from `InteriorDrop M`).

KEY FACTS I have established / can use:
1. `readK (wInt) k = I` (identity matrix) — banked `readK_wInt` gives `readK (wInt) k i j = if i=j then 1 else 0`.
2. `kLens 1 = 1` (I proved `kLens_one`). Hence `kLDU (wInt) = wInt` should hold (kLDU only touches K-slots
   via `kLens (readK · k)`, and `kLens (readK wInt k) = kLens 1 = 1 = readK wInt k`; off K it is identity).
   I can prove `kLDU_wInt : kLDU M (tach M) ha (wInt M ha p) = wInt M ha p` from `readK_wInt` + `kLens_one`
   + the existing `kLDU_eq_on_activeM`/`kLDU_leafPivot` style pointwise reasoning.
3. So `interiorLiveUnit (wInt) = sqSumHmat0 (chainOfMt (wInt leafPivot) (genBlkFlatLive ha (rfinFixedPivot ha (wInt)) (wInt)) hle)`.
4. The DEAD-LEAF survival `achieverUfun_wInt_ne_zero` proves `achieverUfun (wInt) ≠ 0`, where
   `achieverUfun (wInt) = sqSumHmat0 (chainOfMt (wInt structPivot) (genBlkFlatStruct ha (wInt)) hle)`.
   Its proof builds a surviving entry `Hmat 0 (ρ, 0) = 1` via GENERIC lemmas `Hmat_pivot` / `Hmat_row_thread`
   / `suffix_carrier` (stated over an ARBITRARY `B : GenBlk M t`), reading ONLY the fields
   `Bmat` / `Nblk` / `Wblk` / `Rmat` (the surviving row of `A s` reads `Wblk`, NOT `C(s+1)`/`Rfin`).
   Then `sqSumHmat0_ne_zero_of_entry`.
5. CRUCIAL: `genBlkFlatLive ha rfin x` is DEFINITIONALLY `genBlkFlatStruct ha x` on `Bmat/Nblk/Wblk/Rmat`
   (only the `Rfin` field differs: `genBlkFlatStruct.Rfin = fun _ => 0`, `genBlkFlatLive.Rfin = leaf-override`).
   So at the SAME `x = wInt`, the two decoders share all 4 fields the survival entry reads.

THE TWO PIVOT/DECODER DIFFERENCES between `interiorLiveUnit (wInt)` and `achieverUfun (wInt)`:
   (A) pivot scalar: `wInt leafPivot` (a leaf slot, val 1 since rfinFixedPivot (0,0)=1... actually it is x at leafPivot)
       vs `wInt structPivot` (slot ⟨0⟩). The radial scalar enters the chain as `u • Rmat` / `u • Rfin`.
   (B) decoder: `genBlkFlatLive ha (rfinFixedPivot ha wInt) wInt` vs `genBlkFlatStruct ha wInt` — differ only at `Rfin L`.

QUESTION: What is the CLEANEST Lean route to `interiorLiveUnit (wInt p) ≠ 0`? Options I see:
   (a) Re-run the generic `Hmat_pivot`/`Hmat_row_thread`/`suffix_carrier`/`sqSumHmat0_ne_zero_of_entry`
       machinery DIRECTLY on `B := genBlkFlatLive ha (rfinFixedPivot ha wInt) wInt` and pivot `wInt leafPivot`,
       supplying the block hypotheses from the shared-field equality with `genBlkFlatStruct ha wInt`
       (the hypotheses `genBlk_Bmat_*`/`genBlk_Rmat_pivot`/`readW_wInt` transfer by `rfl`/`Function`-field-eq).
       Concern: the pivot scalar is now `wInt leafPivot` not `wInt structPivot` — does the survival entry
       depend on the radial scalar value? In `Hmat_pivot` the surviving entry is `Rmat_p ρ = colP-indicator`
       (a LITERAL, scalar-independent) and `suffix` (carrier, scalar-independent). The radial `u` only scales
       `C = Bmat·chainQ(N) + u•Rmat`; but the surviving entry's `B_p ρ`-row is 0 and `Rmat_p ρ` is the
       indicator, so `C_p ρ = u • indicator` — does the survival `Hmat 0 (ρ,0)=1` actually need `u`?
       Look at whether `Hmat_pivot`/`Hmat_row_thread` are scalar-`u`-agnostic (they take `u` as a free var).
   (b) Show `interiorLiveUnit (wInt) = achieverUfun (wInt)` directly? They differ at pivot AND Rfin L, so
       likely NOT equal — but maybe the `Hmat 0` surviving entry is identical even if other entries differ,
       so `sqSumHmat0` of both is ≥ 1. Probably (a) is cleaner.

Tell me: which option, and the precise Lean skeleton. In particular: is the surviving-entry construction
(`Hmat_pivot` + `Hmat_row_thread` + `suffix_carrier`) genuinely INDEPENDENT of (A) the radial scalar value
and (B) the `Rfin L` field — so that I can apply it verbatim to the live decoder + leaf pivot? If there is a
hidden dependence, name it precisely.
</task>

<output_contract>
1. VERDICT: option (a) or (b), one line.
2. The radial-scalar-independence + Rfin-L-independence question: ANSWERED precisely (yes/no + why,
   citing which lemma reads what). This is the load-bearing soundness check.
3. A concrete Lean proof skeleton (~15-30 lines) for `UPolyLive_ne_zero` / `exists_interiorLiveUnit_ne_zero`,
   naming the lemmas to reuse and the field-equality bridges. Pseudo-Lean is fine; flag any step you're unsure of.
4. Any TRAP: a place where the live decoder / leaf pivot breaks the dead-leaf survival argument.
</output_contract>

<grounding_rules>
You do NOT have the source files. Reason from the structural facts I gave. Where you must assume a
lemma's behavior, FLAG it as an assumption ("ASSUMING Hmat_pivot takes u as a free variable..."), so I
can verify against the source. Do not claim a lemma exists that I did not name.
</grounding_rules>

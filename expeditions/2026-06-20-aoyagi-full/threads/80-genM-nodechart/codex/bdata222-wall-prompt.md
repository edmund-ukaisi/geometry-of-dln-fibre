<task>
Lean 4 / Mathlib v4.29. Constructing BData M222 (concrete (2,2,2) DLN node). The map identity field
`hmap : phiFlatLiveR1 M222 tach222 ha hN 1 hp1 hp2 rfin = B ∘ pivotBlowupOn active (structPivot)`.

EMPIRICALLY CONFIRMED (I just built probes):
- `chartIdxEquiv M222 ... := (finCongr ...).trans (Fintype.equivFin (ChartIdx)).symm` is OPAQUE:
  `decide`/`rfl` CANNOT reduce `(chartIdxEquiv...).symm ⟨tag⟩` to a concrete Fin 8 value, and CANNOT
  decide `structPivot (=⟨0,_⟩) = chartIdxEquiv.symm ⟨K-tag⟩` (stuck at Fintype.equivFin).
- BUT reader-vs-reader injectivity WORKS: `(chartIdxEquiv...).symm.injective h` + `decide` on the
  ChartIdx tag inequality closes `χ.symm ⟨tagA⟩ ≠ χ.symm ⟨tagB⟩` for distinct tags A,B.
- The 8 flat slots' ChartIdx tags (verified by decide): bdy0-schur = 4 (K,X,N,E each 1×1), bdy0-lift = 2
  (W=w0,w1), bdy1-schur = 2 (the leaf-residual region). `genBlkFlatLiveR1 M222` reads via readers
  K,X,N (3 bdy0-schur), W (2 bdy0-lift) = 5 reader slots; the E reader-slot is NOT read (Rmat pivot
  overridden by the fixed pivotEIndicator); the 2 bdy1-schur slots are not read by the readers either.
  The leaf `Rfin 2 = rfin x` is MY free choice. The radial `u = x (structPivot) = x ⟨0,_⟩`.

THE WALL: For `φ = B ∘ pivotBlowupOn active 0` with active = {0, lf0, lf1} card 3 = minAdm:
- pivotBlowupOn scales x at the 2 NON-pivot active slots (lf0,lf1) by x_0, fixes everything else
  (incl slot 0). For the leaf to scale correctly I need lf0,lf1 ∈ active, lf0≠0, lf1≠0, lf0≠lf1.
- The 5 reader slots (a,b,n,w0,w1) must be FIXED by pbo ⟹ must be ∉ {lf0,lf1} (pbo fixes q unless
  q∈{lf0,lf1}; q=0 is also fixed). reader∉{lf0,lf1} is provable by injectivity IF lf0,lf1 chosen as
  χ.symm of tags ≠ the reader tags.
- THE STUCK PART: `lf0 ≠ structPivot=⟨0,_⟩` and `lf1 ≠ ⟨0,_⟩`. structPivot is slot 0, NOT given as a
  ChartIdx tag. `⟨0,_⟩ = χ.symm (χ ⟨0,_⟩)` but `χ ⟨0,_⟩` is OPAQUE — can't decide a tag ≠ it.
  So I cannot prove `χ.symm ⟨leaf-tag⟩ ≠ ⟨0,_⟩` by the injectivity trick.

I can CHOOSE: rfin (the leaf reader), active, B, and lf0,lf1. The interface fixes structPivot=⟨0,_⟩ and
needs active.card = minAdm = 3, structPivot ∈ active.
</task>

<output_contract>
Give the SINGLE cleanest resolution to the `lf ≠ structPivot` wall (slot 0 vs opaque-equiv leaf slots),
as a precise Lean route. Rank-order any alternatives. Specifically evaluate these candidate routes:

(R1) CARDINALITY route: choose active = insert structPivot S where S = 2-element finset of χ.symm-leaf
   slots; get active.card=3 via `Finset.card_insert_of_not_mem` needing `structPivot ∉ S`. Same wall —
   unless I argue `structPivot ∉ S` by a pigeonhole: S ⊆ {χ.symm of bdy1-schur tags}, and structPivot=0
   ... does this dodge it? Be concrete about whether `structPivot ∉ S` is reachable.

(R2) Pick lf0,lf1 from the COMPLEMENT: `obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq` over
   `(univ \ {structPivot} \ {reader slots})` to get 2 slots auto-distinct from structPivot AND readers,
   then define rfin/B to read THOSE (existentially-given, opaque) slots. Does this let hmap go through
   even though lf0,lf1 are now opaque (defined by the obtain, not concrete)? The catch: rfin and B are
   BData FIELDS — can they depend on an `obtain`-given S (i.e. define them AFTER obtaining S, inside a
   `let`/term)? Is that clean in Lean?

(R3) Establish `χ ⟨0,_⟩ = <specific tag>` as a LEMMA. Is there any non-decide way? E.g. is there a
   Mathlib characterization of `Fintype.equivFin` at a specific point, or must I treat it as fully
   opaque? (I suspect fully opaque — confirm.)

(R4) AVOID pbo-on-leaf entirely: is there a DIFFERENT active set of card 3 (e.g. {structPivot} ∪ {2
   slots that the pbo can scale that are NOT the leaf}) such that the det is still u² and the map
   identity still holds with a different B? I.e. does the factorization REQUIRE the 2 scaled slots to be
   the leaf slots, or could they be e.g. 2 reader slots, with B compensating? (Recall: the explicit
   Agen0/Agen1 have the leaf entering as u·lf0,u·lf1 and the readers a,b,n,w entering UN-scaled, so the
   2 slots pbo scales MUST be the leaf — confirm or refute.)

For the winning route, give the precise lemma sequence (Mathlib names) and flag the one biggest risk.
If NONE of R1-R4 works and the (2,2,2) faithful hmap is genuinely blocked by the opaque equiv, say so
plainly and state what minimal banked lemma (e.g. a computable model of chartIdxEquiv, or a
`structPivot`-tag lemma) would unblock it.
</output_contract>

<grounding_rules>
Distinguish Lean idioms you're confident exist in v4.29 from inferences about this opaque-equiv setup I
must verify by building. The empirical facts above are CONFIRMED by my builds — trust them. Do not
propose computing χ.symm by decide (confirmed impossible).
</grounding_rules>

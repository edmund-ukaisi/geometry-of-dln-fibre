# Statement cards — `genm-glinterior` entry tide (general-L R1-LOWER interior de-risk)

The de-risk-first entry tide of the general-`L` R1-LOWER interior leg. Two bricks that retire the
staircase-indexing labour-risk `genm-l3interior` flagged: the general-`L` active-set cardinality and
the general-`n` per-boundary Schur-frame staircase determinant. Both sorry-free, clean-three.

Branch `expedition/genm-glinterior` @ `5c22bffd`.

---

> **Claim (task b).** The general-`L` structured residual active set — the flat coordinates the radial
> achiever pivot scales (per interior boundary `k` the E-block, plus the leaf residual) — has
> cardinality `minAdm M` for every depth `L`, generalizing the `Fin (2+1)`-pinned
> `RouteMLeafSlot.activeM_card`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.activeMGen_card`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLeafSlotGen.lean` @ `5c22bffd`)
> - **Gloss.** For `M : Fin (L+1) → ℕ` and the achiever admissibility bundle `ha : StructAdm M (tach M)`,
>   the Finset `activeMGen M ha` (the disjoint `Finset.univ.biUnion` over `k : Fin L` of the per-boundary
>   active image `activeImgGen`: the `activeSlotE` E-block image at interior boundaries `k ≠ L−1`, the
>   `leafSlot` leaf image at `k = L−1`) has `card = minAdm M`.
> - **Proved.** `activeMGen.card = minAdm M`, ∀L, via `Finset.card_biUnion` (pairwise disjoint by the
>   distinct ChartIdx boundary tag, `activeImgGen_pairwiseDisjoint`) = `∑_k rBlock_k · cBlock_k` (each
>   per-boundary card = `rBlock_k · cBlock_k` by `activeImgGen_card`, the leaf via `Text(L+1) = 0`)
>   = `minAdm M` (the Aoyagi bridge `sum_rBlock_cBlock_eq_minAdm`, already ∀L). Instance:
>   `activeMGen_card_2432 : (activeMGen ![2,4,3,2] …).card = 4` (the L=3 interior-deepest anchor, drop
>   split boundary-1 `= 2` + leaf `= 2`).
> - **Assumed.** `ha : StructAdm M (tach M)` (the achiever-path admissibility — the same bundle the L=2
>   `activeM_card` carries; discharged for any concrete `M` with `0 < L` by `structAdm_tach`).
> - **Cited.** none.
> - **Deferred.** The active set is a *cardinality* here; it is NOT yet tied to the radial-blow-up
>   Jacobian exponent `minAdm − 1` for general `L` (that tie is the ∀L interior-chart lift, the follow-on
>   tide — the card supplies the `pivotBlowupOn active.card = minAdm` count that lift consumes).
> - **Status.** sorry-free + reviewed (fidelity PASS, reviewer, `genm-glinterior` audit).

---

> **Claim (task a spine).** The general-`n` per-boundary Schur-frame staircase determinant is
> `∏_{s} |det (K s)|^{r_s + c_s}` — the staircase-length lift of the `StairProd (eihdV M) 2`-pinned
> `RouteMEihdFreePoint.Dtot_abs_det_free`, at the linear-map level, WITHOUT re-plumbing the concrete
> `eihd`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.schurStairMap_abs_det`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurStairDet.lean` @ `5c22bffd`)
> - **Gloss.** For per-boundary block widths `t, r, c : ℕ → ℕ` and block data `X s, K s, N s`, the
>   length-`n` staircase endomorphism `schurStairMap` of `StairProd (fun s => SchurInc (t s) (r s) (c s)) n`
>   — diagonal blocks the per-boundary Schur frames `schurFrameDeriv (X s) (K s) (N s)`, arbitrary
>   head-into-tail couplings `co` — has `|det| = ∏_{s : Fin n} |det (K s)|^{r_s + c_s}`.
> - **Proved.** `|det (schurStairMap …)| = ∏_s |det (K s)|^{r_s + c_s}` (∀n), via the ∀n staircase det
>   `stairMap_det` (couplings drop out) + the generic `schurFrame_abs_det` per diagonal block. Plus the
>   conjugate forms `schurStairMap_abs_det_conj` (single-`e`) and `schurStairMap_abs_det_twoConj` (the
>   two-sided `eIn`/`eOut` regauge shape the ∀L `Dtot` lift consumes, gated on the regauge abs-det-`1`).
>   `n = 2` recovers the `Dtot_abs_det_free` block structure (`schurStairMap_abs_det_two`; the boundary-0
>   Schur factor `|det K|^{(Text1−Text2)+(Wext1−Text2)}` is the SAME `schurFrameDeriv` exponent).
>   (2,4,3,2) instance `schurStairMap_abs_det_2432` (K-blocks `2×2/1×1/0×0`, exponents `(2,3,3)`) +
>   the `0×0` leaf collapse `_2432_leaf_trivial`. Non-vacuity `schurStairMap_det_n3_example`.
> - **Assumed.** none beyond the block data being genuine matrices (the staircase is fully parametric).
> - **Cited.** none.
> - **Deferred.** This is the abstract linear-map det SPINE. The concrete per-`L` conjugacy
>   (`eOut ∘ Dtot ∘ eIn.symm = schurStairMap` for general `L`, the ∀L `eihd_hreg` regauge, the
>   multi-boundary `kLDU_ambient_det_pbo` ∀L, the ∀L `BdetMonomial` decode) is NOT built here — it is the
>   follow-on ∀L interior-chart lift. Docstring keeps this caveat co-located.
> - **Status.** sorry-free + reviewed (fidelity PASS, reviewer, `genm-glinterior` audit).

---

**Axiom footprint (both, force-recompiled `#print axioms`):** exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `monomial_rlct` (pure finite combinatorics
+ linear-map determinant; no analysis, no cited axiom).

**Scope / what this de-risks.** The staircase-indexing labour-risk (`genm-l3interior`: "the multi-boundary
staircase det + activeM bookkeeping; the RouteMBdetMonomial decode fragility multiplies"). Both the
general-`n` det and the general-`L` card formalize with NO math wall. The full ∀L interior chart
(`interiorLiveNodeChart` ∀L) is the labour-bounded follow-on tide, consuming these two bricks + the
concrete per-`L` conjugacy/regauge/decode.

# #3 INTERIOR `cov`/det — the item-3 SPEC + the wall-check (spec-first gate)

Branch `genm-interior` off `origin/agent-genM-r1lower @5a123775`. Base builds green (8305 jobs).
This is the spec-first report BEFORE deep-filling, with the load-bearing wall-check.

## THE WALL-CHECK (load-bearing — surfaces a contract defect, Codex-corroborated xhigh)

**The landed `routeMCore_box_diverges_interiorContract`'s `cov` field is UNSATISFIABLE as written.**
It hard-wires `phi := achieverPhi M = phiFlatStructV M (tach M) ha hN`, and demands
`|det Dφ(u)| = ∏_j |u_j|^{leafH j}` (a MONOMIAL — the `monomialIntegrand` divergence needs it).

But `phiFlatStructV`'s decoder `genBlkFlatStruct` reads each per-boundary Schur K-core block as a
**FREE matrix coordinate** (`readK … i j = x[slot(i,j)]`, RouteMGenFlatStruct.lean:90). The frame
Jacobian per boundary is `|det K_s|^{r_s+c_s}` (`schurFrame_abs_det`), and for a `t×t` K-core with
`t ≥ 2`, `det K_s` is a degree-`t` POLYNOMIAL in the free coords (e.g. the `(3,3,3,3)` 2×2 core gives
`det = z1·z4 − z2·z3`), NOT a monomial. So the free-K chart's total Jacobian is
`(radial)^a · ∏_s |det K_s|^{r_s+c_s}` — a polynomial, never `∏_j|u_j|^{leafH j}`.

Verified structurally: the only worked monomial-det instance with a `t≥2` K-core is the HAND-BUILT
`(3,3,3,3)` chart `phi3333 = paramsEquivFlat ∘ Frame3333 ∘ Kparam3333`. `Kparam3333` is an explicit LDU
lens: free coords `(x1,x2,x3,x4) ↦ [x1, x1·x2, x1·x3, x1·x2·x3+x4]`, whose det is the MONOMIAL `(x1)^2`.
So `phi3333` reads K through an LDU lens and is NOT `genBlkFlatStruct` (free-K) — it is a DIFFERENT
decoder. At `(2,2,2)` the K-cores are 1×1 so det is trivially a monomial; LDU is never exercised there.
The `(4,4,2,2)` instance is a pure radial blow-up (no Schur/LDU). Hence NO landed instance shows the
free-K `phiFlatStructV` having a monomial Jacobian, and it provably cannot for `t≥2`.

## DESIGN CHOICE (Route A, Codex-ranked A > B > C; my call: A with the "define-as-fold" twist)

The rate identity `routeMCore(phiGen(u)(B)…) = u²·VvalGen(…)` is **decoder-agnostic** (consumes only
`hC0 : C 0 · suffix = suffix`, RouteMGenChartId `routeMCore_phiGen`). So a NEW decoder reading K through
an LDU lens still satisfies the rate. The clean architecture:

  **DEFINE the interior chart AS `phiFlatLDU := composeFold fs`** (a `List (ChartFactor N)`), so the
  monomial `cov`/det is FREE from the banked telescope (`phiTarget_abs_det_of_factored` /
  `composeFold_abs_det`). Transfer the RATE by a SEPARATE map equality `composeFold fs = phiGen(u)(B_LDU)`
  ONLY where the rate engine consumes it (rate equalities are local/algebraic and robust; det equalities
  are brittle under dependent-Fin casts — Codex's key point).

This requires a NEW contract `routeMCore_box_diverges_interiorContractLDU` (the landed free-K one cannot
be discharged with a monomial). The dispatch's `hInterior` rewires to it. I do NOT rewrite the leg-owner's
banked file — I add the LDU chart + the new contract as new modules and tell the controller to rewire.

## ITEM-3 (the bottleneck): the opaque-width composeFold + the dependent-Fin casts

`fs` factor order (foldr ∘, so list head applied LAST = the outer reshape):
  `[ linearFactor (paramsEquivFlat ∘ pack reshape), radialFactor active p,
     <per boundary s = L−1 … 1, descending>: schurChartFactor E_s, lduChartFactor E'_s, chainChartFactor … ]`
(exact order TBD against how `phiGen`/`genBlk` consumes boundaries — Codex flag: list order is OPPOSITE
execution order under foldr).

THE HARDEST CAST (where the (3,3,3,3) pattern fails to generalize): each `schurChartFactor`/`lduChartFactor`
takes an ABSTRACT CLE `E : (Fin N → ℝ) ≃L[ℝ] Block × R` splitting the ambient into that boundary's block
space (`SchurInc t r c` / `LDUParam t`) and the rest. At `(3,3,3,3)` these slots are DEFINITIONAL (`Fin 27`
literal indices). At opaque `Wext/Text` widths the split-CLE must be built from `chartIdxEquiv`'s role slots
(`frameSplitEquiv`/`liftSlotEquiv`), and the map equality `composeFold fs = phiGen(B_LDU)` holds only
PROPOSITIONALLY after heterogeneous `Fin.cast` rewrites through boundary-dependent block sizes — NOT by an
`rfl`-chain. This is the genuine multi-tide design dimension (the same dependent-Fin fight the 222/3333 det
bridges paid for, now ∀ boundary at opaque width).

## PER-FIELD DISCHARGE MAP (the NEW LDU contract's 4 open fields)
- `leafH` + `leafH_pivot`: the multi-axis exponent = radial `minAdm−1` on pivot + per-boundary LDU-pivot
  exponents `2(t_s−1−i)` + frame `r_s+c_s` on the LDU diagonal axes; pivot is spectator-free.
  Brick: `radialFactor_abs_det`, `lduChartFactor_abs_det`, `schurChartFactor_abs_det` + a `leafH_prod_eq`
  bookkeeping lemma (the opaque-width generalization of `leafH3333_prod_eq`).
- `Umeas`: `achieverUfun` (= `UvalStructV` = `VvalGen∘decoder`) is a polynomial ⟹ measurable. BUT the new
  chart uses `B_LDU` not `genBlkFlatStruct`, so the rate-side `achieverUfun`/witness must be re-stated for
  the LDU decoder (the witness `exists_achieverUfun_ne_zero_interior` is currently free-K specific). This
  is the moderate re-derivation cost (re-run the witness inductions on the LDU reader `readK = LDU lens`).
- `cov`: the monomial Jacobian — FREE from `composeFold_abs_det` + det bookkeeping (item-4) + the n-fold
  null-slice add-back (generalize `phi3333_cov`'s 4-slice to the variable weighted-axis count) + `injOn`
  off the weighted-axis planes.
- `image_subset`: continuity + `phi 0 = 0` (banked-pattern; `composeFold` of continuous factors).

## SUB-TIDE BREAKDOWN (the genuine interior build, each a substantial tide)
1. **LDU lens decoder `genBlkFlatLDU` ∀M** — reader `readKLDU` = the LDU param map (generalize Kparam3333);
   its rate via the decoder-agnostic engine [cheap once the lens is defined].
2. **Item-3 map equality** `composeFold fs = phiGen(B_LDU)` over opaque widths [THE bottleneck — the
   per-boundary split-CLE construction + the dependent-Fin cast chain].
3. **n-fold null-slice cov** — generalize `phi3333_cov` (4 fixed slices) to the variable weighted-axis count
   (`injOn` off `⋃ weighted-axis planes` + two-sided null add-back).
4. **The 4 fields + the NEW contract** + rewire `hInterior`.

## RECOMMENDATION TO CONTROLLER (scope call needed)
The landed free-K `cov` field cannot be discharged with a monomial; the interior branch genuinely needs the
LDU-coordinatized chart + a NEW contract. This is a 3-4-tide build, not one. Smallest de-risking increment I
can land first: **sub-tide 1 (the `genBlkFlatLDU` LDU-lens decoder + its decoder-agnostic rate)** — banks the
LDU chart skeleton + confirms the rate transfers, isolating item-3 (the map equality) as the precise remaining
obligation. Confirm scope before I open the multi-tide build.

## VALIDATED (against the elaborator, not recalled): the brick-wiring fires
A general-width `composeFold [radialFactor active p, schurChartFactor Esch, lduChartFactor Eldu]` telescopes
via `composeFold_abs_det` + `radialFactor_abs_det`/`schurChartFactor_abs_det`/`lduChartFactor_abs_det` to
`|·_p|^{card−1} · |det K|^{r+c} · ∏_i |q_i|^{2(t−1−i)}` (scratch elaborated clean, EXIT 0). Two confirmed
subtleties for item-3:
- **foldr prefix-evaluation**: the list HEAD is applied LAST. The radial factor (head) has its derivative
  evaluated at the PREFIX `composeFold [schur, ldu] u`, NOT at `u` — so the radial pivot reads the
  Schur∘LDU output. The LDU factor (tail) reads `composeFold [] u = u`. This dictates the factor ORDER:
  the chart applies LDU-core first (innermost), then Schur-frame, then chain, then radial blow-up, then the
  outer linear reshape (head). Getting `leafH_prod_eq` right requires the prefix points to collapse — the
  per-factor det must be PROVABLY a function of `u`'s own coords at the prefix (true because each factor's
  det reads only its own block's coords, which the upstream factors don't touch — needs a per-factor
  "det reads only own-block coords, untouched by prefix" lemma; this is the opaque-width generalization work).
- the `composeFold_abs_det` simp-discharge needs `composeFold_nil, id_eq` in the simp set.

## SUB-TIDE 1 — LANDED (RouteMFlatLDU.lean, branch genm-interior)
`phiFlatLDU reparam x := phiGen (x p) M t (genBlkFlatStruct M t ha (reparam x)) hle` + the decoder-agnostic
rate `routeMCore_phiFlatLDU : routeMCore (phiFlatLDU reparam x) = (x p)²·UvalLDU reparam x` for ANY
`reparam`. Plus `UvalLDU_nonneg`, `phiFlatLDU_id` (`reparam=id` recovers `phiFlatStructV`), and a
non-vacuity `example` reproducing the banked free-K rate. Build green (2716 jobs), sorry-free,
axiom-clean `[propext, Classical.choice, Quot.sound]`. Aggregator NOT edited (single-writer) —
controller wires `import DLNFibre.DLN.RLCT.Validate.RouteMFlatLDU`.

Banks: the LDU-chart skeleton + the rate-robustness-to-K-lens claim. Isolates the remaining obligations:
- item-1: the specific LDU `reparam` on the K-slots (the K-slot LDU surgery via `frameSplitEquiv`'s K
  sub-block; generalize `Kparam3333`).
- item-3: `composeFold fs = phiFlatLDU` map equality over opaque widths (THE det-side bottleneck).
- item-4: the monomial `cov` (free from `composeFold_abs_det`) + the n-fold null-slice add-back.
- the LDU-decoder interior witness (re-derive `exists_achieverUfun_ne_zero_interior` for the LDU reader).

## DIRECTED-SUSPICION CHECK (smeared contract `cov` t≥2) — CLEAN, no analogous gap
`RouteMSmearedContract.routeMCore_box_diverges_smearedContract`'s cov-analogue is
`hRdet : |(D u).det| = |u p| ^ h` — a SINGLE-PIVOT radial monomial, NOT a Schur-frame K-product. Satisfiable
for any t: the smeared branch routes through `of_RadialMPChart`, where the non-radial `ψ` is
measure-preserving (det 1, a `MeasurePreserving`+`MeasurableEmbedding`), so the radial `R = pivotBlowupOn` is
the SOLE Jacobian carrier (`pivotBlowupOnDeriv_det = |u_p|^{card−1}`, always a monomial). NO `det K_s` factor
appears in the smeared branch (the structural reason interior is NOT single-pivot-reducible but smeared IS,
per the scope doc). So the t≥2 unsatisfiability is INTERIOR-SPECIFIC; the smeared contract is sound.

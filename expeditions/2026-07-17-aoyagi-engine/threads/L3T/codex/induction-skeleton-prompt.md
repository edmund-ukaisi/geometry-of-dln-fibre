# Consult: raw TreePath induction skeleton (Lean 4 / Mathlib v4.29)

I need to prove `foldResid_layerHomogeneous'` by RAW `TreePath` induction. The recoord-linearity step-1
lemma + the comp atoms are PROVEN. I need the cleanest induction SKELETON + the per-case dispatch, in
particular how to re-derive the pivot/center facts from the RAW `IsRealBranch` unfold (no `TreeEdge`
available in a raw induction).

## Target
```lean
theorem foldResid_layerHomogeneous' (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (p : TreePath d) (hnonterm : ¬ N ≤ p.conState.layer)
    (hbranch : p.IsRealBranch (canonFlatten d))
    (j : Fin (foldNR d p)) (ℓ : ℕ)
    (hℓsup : supportLayerOf p.conState ≤ ℓ) (hℓN : ℓ < N) :
    HomogeneousDeg1On (foldResid d (canonFlatten d) p j) (layerCoords d ℓ)
      (foldRegion d (canonFlatten d) p)
```
`foldRegion … p = Set.univ` always (`foldRegion_eq_univ`).

## Recursion facts (all PROVEN, defeq/rfl-class)
- `TreePath.conState (.step p' c pv cse ns φ) = ns`.
- `IsRealBranch (.step p' c pv cse ns φ) e` unfolds to
  `p'.IsRealBranch e ∧ (∃ sc ∈ (conOracle d p'.conState).stepChildren, sc.ecase = cse ∧ sc.child = ns ∧ c = canonCenterOf d p'.conState sc ∧ (match cse with | case12|case2 => pv ∈ canonCenterOf d p'.conState sc | _ => ∀ piv, canonPivotOf d p'.conState sc = some piv → piv = pv)) ∧ ShearWithinCarveRaw d e (.step …) φ ∧ φ = canonNormalizationOf d p'.conState pv`.
- For a NON-terminal child (`¬ N ≤ ns.layer`): `foldResid d e (.step p' c pv cse ns φ) j u = foldResid d e p' (Fin.cast _ j) (σ u)` where
  - δ0 (`edgeδ d p' = false`): `σ = stepMapRaw d cse c pv φ = blockBlowupMap c pv ∘ edgeShearRaw d cse φ`.
  - δ1 (`edgeδ d p' = true`): `σ u = fun k => blockBlowupCoordQuot pv k (edgeShearRaw d cse φ u)`.
  (unfold via `foldResid`'s defining eq: `rw [foldResid, dif_neg …, if_pos/if_neg …]`.)
- `edgeShearRaw d cse φ = id` for case11/rollover; `= blockShear φ` for case12/case2.
- `blockBlowupMap ∅ pv = id` (rollover has `canonCenterOf = ∅`).
- transition `conOracle_child_transition p'.conState sc hsc`: rollover→(layer+1,cleared 0); case2/case12→(layer,cleared+1); case11→(layer,cleared).
- `supportLayerOf s = if s.cleared = 0 then s.layer else s.layer+1`.

## Comp atoms (PROVEN — feed these)
```lean
homogeneousDeg1On_comp_of_fixing (g X σ) (hfix : ∀ x ∈ X, ∀ u, σ u x = u x)
  (hagree : ∀ u v, (∀ s∉X, u s=v s) → ∀ s∉X, σ u s=σ v s) (hg : HomogeneousDeg1On g X univ) : HomogeneousDeg1On (g∘σ) X univ
homogeneousDeg1On_comp_of_linear (g X σ C) (hagree) (hlin : ∀u,∀x∈X, σ u x = ∑ j∈X, C u x j*u j)
  (hC : ∀x∈X,∀j∈X, IgnoresCoords (C·x j) X univ) (hg) : HomogeneousDeg1On (g∘σ) X univ
```
Step-1 recoord lemma: `canonNorm_blockShear_linear_on_succLayer d s pv (hSN: s.layer+1<N) : (∀u,∀x∈layerCoords d (s.layer+1), blockShear (canonNormalizationOf d s pv) u x = ∑ j∈…, recoordCoeff … u x j*u j) ∧ (hC)` + `canonNormalizationOf_agree_off_succLayer` (the hagree at ℓ=s.layer+1).

## The dispatch (child support layer `sl` = `supportLayerOf ns`; `hℓsup : sl ≤ ℓ`)
At the given `ℓ ≥ sl`, compose IH `HomogeneousDeg1On (foldResid p' (cast j)) (layerCoords d ℓ) univ`:
- ℓ > sl: σ FIXES layerCoords ℓ (shear vanishes via ShearWithinCarveRaw clause-I `sl<ℓ`; blowup off center; quot off pivot) → `comp_of_fixing`.
- ℓ = sl AND case12/case2: σ = recoord X-linear (step-1 lemma) → `comp_of_linear`.
- ℓ = sl AND case11/rollover: σ FIXES (edgeShear=id; pivot below via case11 birth-corner-freshness / rollover σ=id) → `comp_of_fixing`.
- δ1 rollover: unreachable (`widthMinUpto_pos hpos`).

## Questions
1. **Induction setup**: `revert hnonterm hbranch j hℓsup; induction p with | root => … | step p' c pv cse ns φ ih => …`? Any issue with `j : Fin (foldNR d p)` depending on p, or the motive? Best incantation so `ih` is the parent statement (same `ℓ`).
2. **Parent hyps for IH**: I need `¬ N ≤ p'.conState.layer` (from child non-terminal + transition: layer only advances) and `supportLayerOf p'.conState ≤ ℓ` (parent_sl ≤ child_sl ≤ ℓ). Cleanest way to get parent non-terminal from `conOracle_child_transition` + `¬ N ≤ ns.layer`?
3. **case11 pivot-below fact** (δ1 case11, need `(decode pv).1.1 < p'.layer` for `k ≠ pv` at ℓ ≥ p'.layer): the PROVEN `case11_pivot_decode_lt` takes a `TreeEdge` I don't have. Should I (a) copy its ~30-line proof inline from the raw `hpivpin` (which is the case11 `∀`-pin after `simp only [hc11] at hpivpin`), or (b) is there a slicker route? The birth-corner is `canonPivotOf`, valid via `DivBirthInv` (`PivotPres.divBirthInv_of_isRealBranch d p' hrec`), fresh at `cleared=0` ⟹ born `< p'.layer`.
4. **root case**: `foldResid d e .root = coreGen d e`; base = `coreGen_layerHomogeneous' d j ℓ hℓN` (PROVEN, gives HomogeneousDeg1On on univ). `foldRegion .root = univ`. Straightforward?
5. Any trap making `revert … ; induction` fail (e.g. `ih` not general enough, or the `Fin (foldNR d p')` cast)?

Yes—the `revert …; induction p` approach is correct. Two refinements make it clean:

1. Rewrite `foldRegion` to `univ` before induction.
2. Factor the case11 birth-corner argument into a raw/state-level lemma; do not copy it inline or attempt to synthesize a `TreeEdge`.

One repository mismatch: the checked declaration of [`foldResid_layerHomogeneous'`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L3T3/lean/DLNFibre/DLN/Aoyagi/MultiAffineHomogWire.lean:221) currently lacks `hpos`. Your proposed target needs it for rollover support monotonicity and δ1-rollover impossibility.

## Induction skeleton

This common prelude elaborates with the present definitions:

```lean
  classical
  rw [foldRegion_eq_univ]
  revert hnonterm hbranch j hℓsup
  induction p with
  | root =>
      intro _ _ j _
      simpa only [foldResid] using
        coreGen_layerHomogeneous' d j ℓ hℓN

  | step p c pv cse ns phi ih =>
      intro hnonterm hbranch j hℓsup
      change ¬ N ≤ ns.layer at hnonterm
      change supportLayerOf ns ≤ ℓ at hℓsup

      obtain ⟨hrec,
        ⟨sc, hsc, hecase, hchild, hcenter, hpivpin⟩,
        hwc, hvpin⟩ := hbranch

      have hnr :
          foldNR d (.step p c pv cse ns phi) = foldNR d p := by
        simp only [foldNR]
        rw [if_neg hnonterm]

      let jp : Fin (foldNR d p) := Fin.cast hnr j

      have hlayerMono : p.conState.layer ≤ ns.layer := by
        rw [← hchild]
        rcases conOracle_child_transition p.conState sc hsc with h | h | h <;>
          omega

      have hparNonterm : ¬ N ≤ p.conState.layer := by
        omega

      have hsupportMono :
          supportLayerOf p.conState ≤ supportLayerOf ns := by
        rw [← hchild]
        rcases conOracle_child_transition p.conState sc hsc with h | h | h
        · obtain ⟨_, hge, hL, hC⟩ := h
          have hwidth :=
            DLNFibre.DLN.RLCT.Engine.widthMinUpto_pos
              hpos (p.conState.layer + 1)
          simp only [supportLayerOf]
          rw [if_neg (by omega : p.conState.cleared ≠ 0),
            hC, if_pos rfl, hL]
        · obtain ⟨_, hL, hC⟩ := h
          simp only [supportLayerOf]
          by_cases hc : p.conState.cleared = 0
          · rw [if_pos hc, hC, if_neg (by omega), hL]
            omega
          · rw [if_neg hc, hC, if_neg (by omega), hL]
        · obtain ⟨_, hL, hC⟩ := h
          simp only [supportLayerOf]
          rw [hC, hL]

      have hparSupport : supportLayerOf p.conState ≤ ℓ :=
        hsupportMono.trans hℓsup

      have hg := ih hparNonterm hrec jp hparSupport
```

Thus `ih` is exactly the parent theorem at the same fixed `ℓ`. Generalizing `j` handles its dependent `Fin` type correctly.

The raw residual equations are:

```lean
      by_cases hδ : edgeδ d p = true
      · have hfun :
            foldResid d (canonFlatten d) (.step p c pv cse ns phi) j =
              fun u => foldResid d (canonFlatten d) p jp
                (fun k =>
                  blockBlowupCoordQuot pv k
                    (edgeShearRaw d cse phi u)) := by
          funext u
          rw [foldResid, dif_neg hnonterm, if_pos hδ]
          rfl
        -- δ1 dispatch

      · have hδ0 : edgeδ d p = false := by
          cases h' : edgeδ d p with
          | false => rfl
          | true  => exact absurd h' hδ

        have hfun :
            foldResid d (canonFlatten d) (.step p c pv cse ns phi) j =
              fun u => foldResid d (canonFlatten d) p jp
                (stepMapRaw d cse c pv phi u) := by
          funext u
          rw [foldResid, dif_neg hnonterm,
            if_neg (by simp [hδ0])]
          rfl
        -- δ0 dispatch
```

The final `rfl` is useful: it unfolds `jp` and eliminates the difference between the two proofs of the `foldNR` equality by proof irrelevance.

## Raw center and shear facts

These replace the `TreeEdge` projections:

```lean
      have hinv : DivBirthInv d p.conState :=
        PivotPres.divBirthInv_of_isRealBranch
          (canonFlatten d) p hrec

      have hcenterLayer :
          ∀ y ∈ c,
            (((tupIdxEquiv d).symm y).1.1 : ℕ) ≤
              p.conState.layer := by
        intro y hy
        exact canonCenterOf_decode_layer_le
          p.conState sc hinv y (hcenter ▸ hy)

      rw [ShearWithinCarveRaw] at hwc
      obtain ⟨hwc_write, hwc_read, _⟩ := hwc
```

For case12/case2, `hpivpin` reduces to membership in the canonical center, so:

```lean
have hpvCenter : pv ∈ c := by
  rw [hcenter]
  exact hpivpin

have hpvLayer :
    (((tupIdxEquiv d).symm pv).1.1 : ℕ) ≤ p.conState.layer :=
  hcenterLayer pv hpvCenter
```

For rollover, `hcenter` and `hecase` reduce `c` to `∅`, hence `stepMapRaw = id`.

## Factor the case11 birth-corner proof

Do not copy the existing 30-line proof into the induction. Raw `IsRealBranch` does not provide the `TreeEdge` fields `hpivot`, `hshear`, `hshear0`, etc., so constructing a temporary `TreeEdge` is not generally available.

Instead, extract this state-level helper next to the existing [`case11_pivot_decode_lt`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L3T3/lean/DLNFibre/DLN/Aoyagi/MultiAffineStepWire.lean:502):

```lean
theorem case11_pivot_decode_le_and_lt_of_clear_raw
    {d : Fin (N + 1) → ℕ}
    (s : ConState N) (sc : StepChild d s)
    (pv : Fin (flatDim d))
    (hsc : sc ∈ (conOracle d s).stepChildren)
    (hc11 : sc.ecase = StepCase.case11)
    (hinv : DivBirthInv d s)
    (hpivpin :
      ∀ q, canonPivotOf d s sc = some q → q = pv) :
    (((tupIdxEquiv d).symm pv).1.1 : ℕ) ≤ s.layer ∧
      (s.cleared = 0 →
        (((tupIdxEquiv d).symm pv).1.1 : ℕ) < s.layer) := by
  have hmi : sc.esubst.mergeIdx < s.numDiv :=
    conOracle_case11_mergeIdx_lt s sc hsc hc11
  obtain ⟨hval, hlayerLE, hfresh, -⟩ := hinv
  set bc := s.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩ with hbc
  have hcv := hval ⟨sc.esubst.mergeIdx, hmi⟩
  have hS : bc.1 < N := hcv.1
  have hrr : bc.2 < d (⟨bc.1, hS⟩ : Fin N).succ :=
    hcv.2.2 _ rfl
  have hcc : bc.2 < d (⟨bc.1, hS⟩ : Fin N).castSucc :=
    hcv.2.1 _ rfl

  have hcp1 :
      canonPivotOf d s sc = cornerToFlat d bc.1 bc.2 := by
    simp only [canonPivotOf, hc11]
    rw [dif_pos hmi, ← hbc]

  have hcp2 :
      cornerToFlat d bc.1 bc.2 =
        some (tupIdxEquiv d
          ⟨⟨⟨bc.1, hS⟩, ⟨bc.2, hrr⟩⟩, ⟨bc.2, hcc⟩⟩) := by
    simp only [cornerToFlat]
    rw [dif_pos hS, dif_pos hrr, dif_pos hcc]

  have hpiv :
      pv = tupIdxEquiv d
        ⟨⟨⟨bc.1, hS⟩, ⟨bc.2, hrr⟩⟩, ⟨bc.2, hcc⟩⟩ :=
    (hpivpin _ (hcp1.trans hcp2)).symm

  have hdecode :
      (((tupIdxEquiv d).symm pv).1.1 : ℕ) = bc.1 := by
    rw [hpiv, Equiv.symm_apply_apply]

  constructor
  · rw [hdecode]
    exact hlayerLE ⟨sc.esubst.mergeIdx, hmi⟩
  · intro hclear
    rw [hdecode]
    rcases eq_or_lt_of_le
      (hlayerLE ⟨sc.esubst.mergeIdx, hmi⟩) with heq | hlt
    · exact absurd
        (hfresh ⟨sc.esubst.mergeIdx, hmi⟩ heq)
        (by rw [hclear]; exact Nat.not_lt_zero _)
    · exact hlt
```

This gives both facts needed by the raw induction:

- δ0 case11: use `.1`, the weak `pivotLayer ≤ parentLayer`.
- δ1 case11: use `.2 (of_decide_eq_true hδ)`, the strict birth-before-current-layer fact.

The existing `TreeEdge` theorem can then become a short wrapper around this helper.

## Dispatch

| δ | case | child support layer | action |
|---|---|---:|---|
| 0 | case12/case2 | `S+1` | equality: `comp_of_linear`; above: `comp_of_fixing` |
| 0 | case11 | `S+1` | `comp_of_fixing`; use raw pivot `.1` |
| 0 | rollover | `S+1` | `σ = id`, hence `comp_of_fixing` |
| 1 | case12/case2 | `S+1` | equality: `comp_of_linear`; above: `comp_of_fixing` |
| 1 | case11 | `S` | `comp_of_fixing`; use raw pivot `.2 hclear` |
| 1 | rollover | — | contradiction from `widthMinUpto_pos hpos` |

For active case12/case2, derive

```lean
have hSN : p.conState.layer + 1 < N := by
  -- child support = S+1, hℓsup, hℓN
  omega
```

Then split `S + 1 ≤ ℓ` using `eq_or_lt_of_le`. At equality use:

```lean
canonNorm_blockShear_linear_on_succLayer
  d p.conState pv hSN
```

and `homogeneousDeg1On_comp_of_linear`. Strictly above, `hwc_write` supplies fixing and `hwc_read` supplies agreement.

At equality, remember that `ShearWithinCarveRaw` is deliberately strict (`sl < ℓ`), so `hagree` must come from `hvpin` plus `canonNormalizationOf_agree_off_succLayer`.

The root case is therefore exactly as expected, and there is no dependent-`Fin` obstruction once `j` is reverted.
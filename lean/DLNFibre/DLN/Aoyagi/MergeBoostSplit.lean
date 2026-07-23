import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.SourceClearedResid

/-!
# `DLNFibre.DLN.Aoyagi.MergeBoostSplit` — the case-1(1) merge boost-split (WALL #38, L2)

The wall `realBranch_boostReady_case11` produces `Deg1SupportedOn … ed.center` (property (D)). At a merge
the center is `{reused pivot e₂} ∪ partialBlock`, and the residual's dependence on the *extra* block
(supportAt ∖ center) factors through the single reused-pivot coordinate `e₂` — the b-ledger content, in
the render carried by the concrete residual (Codex route (b), `codex/l2-mergeboostsplit-route.md`).

OBJECT RE-SHAPE (elder ruling §7/§7.8, Option 2′): property (D) is FALSE on the raw shears-only
`foldResid` and TRUE on the **source-cleared** chart residual `sourceClearedResid` (`SourceClearedResid.lean`).
So the content lemma + the wall now target `sourceClearedResid`; the recursion `foldResid` is UNCHANGED.

Split into two: `MergeBoostSplit` (the predicate) + `MergeBoostSplit.deg1SupportedOn` (the purely
algebraic assembly, PROVEN here, REUSABLE UNCHANGED on any residual) + the concrete content lemma
`foldResid_case11_mergeBoostSplit_sourceCleared` (the canonFlatten boost-split OF `sourceClearedResid` —
the capstone, LIVE frontier; certificate §4 b-ledger induction). The content lemma is canonFlatten-stated
(idiom-independent): the ∀e form is FALSE (route-β / KILLED-BY-e); it consumes the concrete `coreGen`
at `e = canonFlatten d`, not `hslot`. -/

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

variable {N : ℕ}

/-- **The merge boost-split** (Codex route (b) predicate). Each residual entry `resid j` splits as a
partial-block degree-1 form `∑_{i∈part} αᵢ·uᵢ` PLUS `u_{e₂} · (∑_{i∈extra} βᵢ·uᵢ)` — the extra block
enters ONLY through the reused-pivot coordinate `e₂`. All coefficients continuous on `V` and ignoring
the `center` coordinates. This is the b-ledger factoring made pointwise on the concrete residual. -/
def MergeBoostSplit {nR : ℕ} (d : Fin (N + 1) → ℕ)
    (resid : Fin nR → (Fin (flatDim d) → ℝ) → ℝ) (e₂ : Fin (flatDim d))
    (part extra center : Finset (Fin (flatDim d))) (V : Set (Fin (flatDim d) → ℝ)) : Prop :=
  ∀ j, ∃ α β : Fin (flatDim d) → (Fin (flatDim d) → ℝ) → ℝ,
    (∀ i, ContinuousOn (α i) V) ∧ (∀ i, ContinuousOn (β i) V) ∧
    (∀ i, IgnoresCoords (α i) center V) ∧ (∀ i, IgnoresCoords (β i) center V) ∧
    (∀ u ∈ V, resid j u = (∑ i ∈ part, α i u * u i) + u e₂ * (∑ i ∈ extra, β i u * u i))

/-- **Algebraic assembly** — `MergeBoostSplit ⟹ Deg1SupportedOn center`. The `Deg1SupportedOn` witness:
`c i := α i` on the partial block, `c e₂ := ∑_{i∈extra} βᵢ·uᵢ` at the reused pivot (continuous, ignores
center), `0` elsewhere. Needs `e₂ ∈ center`, `part ⊆ center`, and `e₂ ∉ part` (so the pivot slot does not
collide with a partial slot). Pure algebra — no fold, no `e`, idiom-independent. -/
theorem MergeBoostSplit.deg1SupportedOn {nR : ℕ} (d : Fin (N + 1) → ℕ)
    (resid : Fin nR → (Fin (flatDim d) → ℝ) → ℝ) (e₂ : Fin (flatDim d))
    (part extra center : Finset (Fin (flatDim d))) (V : Set (Fin (flatDim d) → ℝ))
    (he₂ : e₂ ∈ center) (hpart : part ⊆ center) (hep : e₂ ∉ part)
    (hex : ∀ k ∈ extra, k ∉ center)
    (h : MergeBoostSplit d resid e₂ part extra center V) :
    Deg1SupportedOn resid center V := by
  -- c-witness: `α i` on the partial block, `∑_{extra} β·u` at the reused pivot `e₂`, `0` elsewhere.
  classical
  intro j
  obtain ⟨α, β, hαc, hβc, hαi, hβi, hrepr⟩ := h j
  refine ⟨fun i u ↦ if i = e₂ then (∑ k ∈ extra, β k u * u k) else if i ∈ part then α i u else 0,
    ?_, ?_, ?_⟩
  · -- CONTINUITY
    intro i
    by_cases hie : i = e₂
    · simp only [if_pos hie]
      exact continuousOn_finset_sum _ (fun k _ ↦ (hβc k).mul ((continuous_apply k).continuousOn))
    · simp only [if_neg hie]
      by_cases hip : i ∈ part
      · simp only [if_pos hip]; exact hαc i
      · simp only [if_neg hip]; exact continuousOn_const
  · -- SUM over the center
    intro u hu
    have hsub : part ⊆ center.erase e₂ :=
      fun i hi ↦ Finset.mem_erase.mpr ⟨fun h ↦ hep (h ▸ hi), hpart hi⟩
    have herase : (∑ i ∈ center.erase e₂,
        (if i = e₂ then (∑ k ∈ extra, β k u * u k) else if i ∈ part then α i u else 0) * u i)
        = ∑ i ∈ part, α i u * u i := by
      rw [← Finset.sum_subset hsub (fun i hi hni ↦ by
        rw [if_neg (Finset.mem_erase.mp hi).1, if_neg hni, zero_mul])]
      refine Finset.sum_congr rfl (fun i hi ↦ ?_)
      have hine : i ≠ e₂ := fun h ↦ hep (h ▸ hi)
      rw [if_neg hine, if_pos hi]
    rw [hrepr u hu, ← Finset.insert_erase he₂,
      Finset.sum_insert (Finset.notMem_erase e₂ center)]
    dsimp only
    rw [if_pos rfl, herase]
    ring
  · -- IGNORESCOORDS center
    intro i w hw m hm t
    by_cases hie : i = e₂
    · simp only [if_pos hie]
      refine Finset.sum_congr rfl (fun k hk ↦ ?_)
      have hkm : k ≠ m := fun h ↦ (hex k hk) (h.symm ▸ hm)
      rw [hβi k w hw m hm t, Function.update_of_ne hkm t w]
    · by_cases hip : i ∈ part
      · simp only [if_neg hie, if_pos hip]; exact hαi i w hw m hm t
      · simp only [if_neg hie, if_neg hip]

/-- **The case11 read-off** (certificate §4 iv) — `SourceClearedInv p` + a real case11 extension ⟹ the
`MergeBoostSplit` of `sourceClearedResid d p` over `ed.center`. Witnesses: `e₂ = ed.pivot` (= `canonPivotOf`
for a case11 real branch, `IsRealBranch`-pinned), `part = supportAt ∩ ed.center`, `extra = supportAt ∖
ed.center`. The INV's boost conjunct gives the `u_{e₂}`-divisibility of the extra block; the target
containment `case11_center_subset_ledgerTarget` + `ignoresCoords_of_subset` give IgnoresCoords-`ed.center`
(the raw-c_i trap: `c_i = u_{e₂}·β_i` does NOT ignore `ed.center`, only `β_i` + the clean `q` do). STATE-ONLY
(tracked LIVE-frontier). -/
-- map: B-wall-mergeBoostSplit-of-sourceClearedInv (the §4 iv read-off assembly)
theorem mergeBoostSplit_of_sourceClearedInv (d : Fin (N + 1) → ℕ)
    {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d))
    (hinv : SourceClearedInv d p) :
    ∃ e₂ ∈ ed.center, ∃ part extra : Finset (Fin (flatDim d)),
      part ⊆ ed.center ∧ e₂ ∉ part ∧ (∀ k ∈ extra, k ∉ ed.center) ∧
      MergeBoostSplit d (sourceClearedResid d p) e₂ part extra ed.center
        (foldRegion d (canonFlatten d) p) := by
  -- map: B-wall-mergeBoostSplit-of-sourceClearedInv
  sorry

/-- **The content lemma** (LIVE frontier, the capstone) — the SOURCE-CLEARED chart residual
`sourceClearedResid d p` at a real case-1(1) merge branch satisfies `MergeBoostSplit` with
`e₂ = canonPivotOf` (the reused divisor's birth corner), `part = supportAt ∩ ed.center`,
`extra = supportAt ∖ ed.center`. Certificate §4 b-ledger induction on the concrete `foldResid` recursion
carried on `sourceClearedResid`: ROOT = `coreGen` (`∏A` entries, `coreGen_layerHomogeneous'`), δ=1
strict-transform transport (a fresh exceptional born), δ=0 pullback transport, case11 read-off. NOT from
`hslot`, NOT ∀e (canonFlatten-pinned). Property (D) is FALSE on the raw `foldResid` (the (2,2,2,2) `u₀₁₀`
obstruction) and TRUE here — the ancestor coupling is cleared, so the `extra` block factors through the
single `e₂`. Wires DIRECTLY into `MergeBoostSplit.deg1SupportedOn` (`∀ k ∈ extra, k ∉ ed.center`
automatic). case11-only (the case12/case2 born-unit is a sibling fact, Consumer 4). -/
theorem foldResid_case11_mergeBoostSplit_sourceCleared (d : Fin (N + 1) → ℕ)
    {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∃ e₂ ∈ ed.center, ∃ part extra : Finset (Fin (flatDim d)),
      part ⊆ ed.center ∧ e₂ ∉ part ∧ (∀ k ∈ extra, k ∉ ed.center) ∧
      MergeBoostSplit d (sourceClearedResid d p) e₂ part extra ed.center
        (foldRegion d (canonFlatten d) p) := by
  -- map: B-wall-mergeboostsplit-content-sourceCleared — the §4 decomposition: read-off ∘ INV-holds
  -- `0 < N` is forced by the case11 edge: a live oracle step (its `∃ sc ∈ stepChildren`) needs
  -- `p.conState.layer < N` (a terminal state emits no children), so `0 ≤ layer < N`.
  have hN : 0 < N := by
    obtain ⟨sc, hsc, _⟩ := hbranch.2.1
    have hlive : ¬ N ≤ p.conState.layer := by
      intro hle
      have hterm : conOracle d p.conState = oracleTerminal d p.conState := by
        unfold conOracle; rw [dif_pos hle]
      rw [hterm] at hsc
      simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
    exact lt_of_le_of_lt (Nat.zero_le _) (not_le.mp hlive)
  exact mergeBoostSplit_of_sourceClearedInv d ed hδ hc11 hbranch
    (sourceClearedInv_holds d hN p hbranch.1)

/-- **[FOSSIL — SUPERSEDED-BY `foldResid_case11_mergeBoostSplit_sourceCleared`; retained for statement
provenance]** The OLD raw-object content lemma (REFUTED-AS-STATED — see the banner below; consumer-less
after the wall re-point). Was: the actual `foldResid` at `e = canonFlatten d`,
a real case-1(1) merge branch, satisfies `MergeBoostSplit` with `e₂ = canonPivotOf`,
`part = supportAt ∩ ed.center`, `extra = supportAt ∖ ed.center`. Concrete `coreGen`-at-merge induction
(birth introduces e₂ / suffix transport preserves / threshold split); NOT from `hslot`, NOT ∀e.

SHAPING (L4D's call, ruling contract split-consumers-needed-facts.md): **case11-only**. Consumers 1,2
(case1_conjA + LL case11 S=L) route through the wall, which is case11-specific — so the content lemma is
scoped to match. The case12/case2 born-unit (Consumer 4, child.cleared=1) is a DIFFERENT fact
(pivot-coeff `∃ j, c_{e₂}(j) 0 ≠ 0`, supportAt(child)=∅) and gets its own sibling — folding it in as a
degenerate `extra=∅` split would mix two distinct situations under one name (anti-bedrock). The
conclusion carries `∀ k ∈ extra, k ∉ ed.center` (automatic since `extra = supportAt ∖ ed.center`) so it
wires DIRECTLY into `MergeBoostSplit.deg1SupportedOn` (which needs that disjointness `hex`). -/
-- REFUTED-AS-STATED (pnp #68, obstruction b31a3cc8c + repair 672007eb8; L4D independently
-- re-derived): FALSE on the RAW foldResid — on real case11 branches the E_J col-0 input coupling
-- survives the shears-only recursion (slot0|_{center=0} ≠ 0 on (2,2,2,2)); Deg1SupportedOn is
-- STRICTLY STRONGER than the ideal-equality F₂ closed. TRUE on the SOURCE-COLUMN-CLEARED residual
-- (each ancestor clear's below-pivot input entries zeroed BEFORE that edge's shear). Do NOT
-- attempt this proof as stated — #69 RULED (sourceClearedResid = the (D)-carrier); the global move
-- (§8/#74) is rendered by seat-GM. The predicate + the assembly implication above SURVIVE the re-shape.
theorem foldResid_case11_mergeBoostSplit_canon (d : Fin (N + 1) → ℕ)
    {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∃ e₂ ∈ ed.center, ∃ part extra : Finset (Fin (flatDim d)),
      part ⊆ ed.center ∧ e₂ ∉ part ∧ (∀ k ∈ extra, k ∉ ed.center) ∧
      MergeBoostSplit d (foldResid d (canonFlatten d) p) e₂ part extra ed.center (foldRegion d (canonFlatten d) p) := by
  -- map: B-wall-mergeboostsplit-content (concrete canonFlatten coreGen-at-merge; the capstone)
  sorry

/-- **The wall, wired (primed variant) — RE-POINTED to `sourceClearedResid` (Option 2′, ruling §7.8).**
Concludes `Deg1SupportedOn (sourceClearedResid d p) ed.center` (property (D) on the source-cleared chart
residual — FALSE on the raw `foldResid`), PROVEN via the new content lemma + the algebraic assembly. The
signature is otherwise the OLD primed's (`hslot` retained, unused). COUPLED INTEGRATION: `Case1Wire`'s
unprimed `realBranch_boostReady_case11` + the δ=1 append (`stepInv_child_delta1_append`) [L4D] and
`LastLayerWire`'s use [LL] migrate their consumed object from `foldResid` to `sourceClearedResid` to match;
the controller sequences the three re-points together (the full build is red until they land — this
module's own import closure is green). -/
theorem realBranch_boostReady_case11' (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he : e = canonFlatten d) {p : TreePath d}
    (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared)
      (supportLayerOf p.conState) (foldRegion d e p)) :
    Deg1SupportedOn (sourceClearedResid d p) ed.center (foldRegion d e p) := by
  subst he
  obtain ⟨e₂, he₂, part, extra, hpart, hep, hex, hsplit⟩ :=
    foldResid_case11_mergeBoostSplit_sourceCleared d ed hδ hc11 hbranch
  exact MergeBoostSplit.deg1SupportedOn d (sourceClearedResid d p) e₂ part extra ed.center
    (foldRegion d (canonFlatten d) p) he₂ hpart hep hex hsplit

end DLNFibre.DLN.Aoyagi

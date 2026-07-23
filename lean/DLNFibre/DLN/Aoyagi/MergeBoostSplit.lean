import DLNFibre.DLN.Aoyagi.Case1Wire

/-!
# `DLNFibre.DLN.Aoyagi.MergeBoostSplit` — the case-1(1) merge boost-split (WALL #38, L2)

The wall `realBranch_boostReady_case11` produces `Deg1SupportedOn (foldResid p) ed.center`. At a merge
the center is `{reused pivot e₂} ∪ partialBlock`, and the residual's dependence on the *extra* block
(supportAt ∖ center) factors through the single reused-pivot coordinate `e₂` — the b-ledger content, in
the render carried by the concrete residual (Codex route (b), `codex/l2-mergeboostsplit-route.md`).

Split into two: `MergeBoostSplit` (the predicate) + `MergeBoostSplit.deg1SupportedOn` (the purely
algebraic assembly, PROVEN here) + the concrete content lemma `foldResid_case11_mergeBoostSplit_canon`
(the canonFlatten boost-split — the capstone, LIVE frontier). The content lemma is canonFlatten-stated
(idiom-independent): the ∀e form is FALSE (route-β / KILLED-BY-e); it consumes the concrete `coreGen`
at `e = n d`, not `hslot`. -/

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT.Engine

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
  -- map: B-wall-mergeboostsplit-assembly (algebraic; c-witness = α on part, ∑_{extra} β·u at e₂, 0 else)
  -- ROUTE (structure verified; Finset-mechanics grind, next cycle): per `j`, obtain `α β … hrepr` from
  -- `h j`; the Deg1SupportedOn witness is `c i u := if i = e₂ then ∑_{k∈extra} β k u·u k else
  -- if i ∈ part then α i u else 0`. (1) CONTINUITY: e₂-branch = `continuousOn_finset_sum` of
  -- `(hβc k).mul (continuous_apply k).continuousOn`; part = `hαc i`; else `continuousOn_const`.
  -- (2) SUM: `rw [hrepr, ← Finset.insert_erase he₂, Finset.sum_insert (not_mem_erase …)]`; the erase-sum
  -- collapses to `∑_{part} α·u` (part ⊆ center.erase e₂ via hep+hpart; off-part terms `zero_mul`, i≠e₂ on
  -- the erase); then `mul_comm (u e₂)` + `add_comm` matches hrepr. (3) IGNORESCOORDS center: e₂-branch —
  -- `hβi k` (β ignores center) AND `u k` unchanged since `hex k hk : k ∉ center ⟹ k ≠ m` (use
  -- `Function.update_of_ne`); part = `hαi i`; else const. `hex` (extra ∩ center = ∅) is Codex's
  -- necessary disjointness — a `literal e₂-factor is not enough` guard (e₂·(e₂+u_i) would fail IgnoresCoords).
  sorry

/-- **The content lemma** (LIVE frontier, the capstone) — the actual `foldResid` at `e = n d`
(canonFlatten), a real case-1(1) merge branch, satisfies `MergeBoostSplit` with `e₂ = canonPivotOf`,
`part = supportAt ∩ ed.center`, `extra = supportAt ∖ ed.center`. Concrete `coreGen`-at-merge induction
(birth introduces e₂ / suffix transport preserves / threshold split); NOT from `hslot`, NOT ∀e. -/
theorem foldResid_case11_mergeBoostSplit_canon (d : Fin (N + 1) → ℕ)
    {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∃ e₂ ∈ ed.center, ∃ part extra : Finset (Fin (flatDim d)),
      part ⊆ ed.center ∧ e₂ ∉ part ∧
      MergeBoostSplit d (foldResid d (canonFlatten d) p) e₂ part extra ed.center (foldRegion d (canonFlatten d) p) := by
  -- map: B-wall-mergeboostsplit-content (concrete canonFlatten coreGen-at-merge; the capstone)
  sorry

end DLNFibre.DLN.Aoyagi

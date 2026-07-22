import DLNFibre.DLN.Aoyagi.OrderRealize
import DLNFibre.DLN.Aoyagi.OrderRealizeSwap
import Mathlib.GroupTheory.Perm.Sign

/-!
# `DLN.Aoyagi.OrderRealizeAssembly` — P6.2 Tier-3 (3a): the realization iso + θ-count (TERMINAL)

The terminal module of the (3a) realization order-iso. It composes the two factor isos into the
headline and the θ-count corollary:

* **swap factor** `OrderRealizeSwap.swapBinding_orderIso_impl` — one adjacent width-swap is an
  order-iso of the binding poset (seat-Eswap);
* **sorted-box factor** `OrderRealize.bindingSet_sorted_orderIso_boxPart` — on sorted widths the
  binding poset realises `BoxPart(ℓ,a)` (seat-Ecore, via `SortedBox.sortedBox_orderIso`).

The swap-dependent cluster (`swapBinding_orderIso`, `transportSubmonoid`, `bindingSet_transport_
sorted`, `bindingSet_orderIso_boxPart`, `bindingSet_chainHeight`) lives here rather than in
`OrderRealize` because `OrderRealizeSwap` imports `OrderRealize` (for the `swapR`/`swapProfile`
floor), so the swap discharge cannot close in `OrderRealize` without an import cycle. `OrderRealize`
stays the pure floor + the (upstream-safe) sorted-box factor.

**(c) transport** is the submonoid-closure route: the adjacent generators `swapBinding_orderIso`
span `Perm (Fin (L+1))` (`Equiv.Perm.mclosure_swap_castSucc_succ`), so `Tuple.sort M` transports the
binding poset from `M` to `sortedWidths M`; composed with the sorted-box factor this gives the
realization iso, hence `chainHeight(bindingSet M) = a(ℓ−a)+1 = aoyagiTheta`.
-/

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.DLN.RLCT DLNFibre.Core.Aoyagi.OrderChain

variable {L : ℕ}

/-- **(a)+(b) ONE-SWAP ORDER-ISO** (DISCHARGED = `OrderRealizeSwap.swapBinding_orderIso_impl`,
seat-Eswap): one adjacent width-swap induces an order-isomorphism of the binding poset, via the
`swapR` transport. Bundled ("swap preserves `bindingSet`" + "local coupled monotonicity of `R`")
because the monotonicity couples three profile coords — the honest statement is the iso, not an
atomic `swapR`-in-`X` fact (which is false). -/
theorem swapBinding_orderIso (M : Fin (L + 1) → ℕ) (k : Fin L) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (swapWidths k M))) :=
  swapBinding_orderIso_impl M k hpos

/-- The **transport submonoid**: permutations `σ` of the width indices under which the binding poset
transports (for every positive `M`). A submonoid via `OrderIso.refl` / `.trans`; the adjacent
generators come from `swapBinding_orderIso`; the closure is `⊤` (`mclosure_swap_castSucc_succ`), so
every permutation — in particular `Tuple.sort M` — transports. This is the (c) design (submonoid
route); see `transport-c-design.md`. -/
def transportSubmonoid : Submonoid (Equiv.Perm (Fin (L + 1))) where
  carrier := {σ | ∀ M : Fin (L + 1) → ℕ, (∀ s, 0 < M s) →
    Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (M ∘ ⇑σ)))}
  mul_mem' := by
    intro a b ha hb M hpos
    obtain ⟨ea⟩ := ha M hpos
    obtain ⟨eb⟩ := hb (M ∘ ⇑a) (fun s => hpos (a s))
    have hw : M ∘ ⇑(a * b) = (M ∘ ⇑a) ∘ ⇑b := by rw [Equiv.Perm.coe_mul]; rfl
    rw [hw]; exact ⟨ea.trans eb⟩
  one_mem' := by
    intro M _
    rw [Equiv.Perm.coe_one, Function.comp_id]; exact ⟨OrderIso.refl _⟩

/-- **(c) THE TRANSPORT** — discharged via the submonoid-closure route: adjacent generators
(`swapBinding_orderIso`) span `Perm (Fin (L+1))` (`mclosure_swap_castSucc_succ`), so
`Tuple.sort M ∈ transportSubmonoid`, giving `bindingSet M ≃o bindingSet (M ∘ Tuple.sort M) =
bindingSet (sortedWidths M)`. -/
theorem bindingSet_transport_sorted (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (sortedWidths M))) := by
  have hgen : ∀ i : Fin L, Equiv.swap i.castSucc i.succ ∈ transportSubmonoid :=
    fun i M' hpos' => swapBinding_orderIso M' i hpos'
  have hsub : (⊤ : Submonoid (Equiv.Perm (Fin (L + 1)))) ≤ transportSubmonoid := by
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ L]
    exact Submonoid.closure_le.mpr (by rintro _ ⟨i, rfl⟩; exact hgen i)
  exact hsub (Submonoid.mem_top _) M hpos

/-- **(3a) THE REALIZATION ISO** — discharged from the transport (c) + the sorted-case box iso, by
composition. -/
theorem bindingSet_orderIso_boxPart (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet M) ≃o ↥(BoxPart (ell M 0) ((residueA M 0).toNat))) := by
  obtain ⟨e1⟩ := bindingSet_transport_sorted M hpos
  obtain ⟨e2⟩ := bindingSet_sorted_orderIso_boxPart M hpos
  exact ⟨e1.trans e2⟩

/-- **The Tier-3 count corollary**: `chainHeight(bindingSet) = a(ℓ−a)+1 = aoyagiTheta`, via the
realization iso + the banked subtype-`≃o` transport + `chainHeight_boxPart`. -/
theorem bindingSet_chainHeight (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    (bindingSet M).chainHeight (· < ·)
      = ((((residueA M 0).toNat) * (ell M 0 - (residueA M 0).toNat) + 1 : ℕ) : ℕ∞) := by
  obtain ⟨e⟩ := bindingSet_orderIso_boxPart M hpos
  rw [chainHeight_eq_of_orderIso _ _ e, chainHeight_boxPart]

end DLNFibre.DLN.Aoyagi

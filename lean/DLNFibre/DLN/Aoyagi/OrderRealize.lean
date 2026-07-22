import DLNFibre.Core.Aoyagi.OrderChain
import DLNFibre.DLN.RLCT.Foundations.AdmTight
import DLNFibre.DLN.Aoyagi.ClosedForm

/-!
# `DLN.Aoyagi.OrderRealize` — P6.2 Tier-3 (3a): the binding poset realises `BoxPart` (SPECIFY)

The realization order-isomorphism (pnp thread-42 cert, part (3a), genuine order-iso verified on 993
cores + trap kill-set): the poset of `Mval`-minimising admissible profiles is order-isomorphic to
the box-partition lattice `BoxPart(ℓ,a)`, so its `chainHeight` is `a(ℓ−a)+1 = aoyagiTheta` (via the
LANDED `Core.Aoyagi.OrderChain.chainHeight_boxPart`).

**SPECIFY STATE (frontier, awaiting elder scaffold-pass then prove).**
* `bindingSet M` — the domain: admissible profiles at the minimum `Mval`. REAL def.
* `bindingSet_orderIso_boxPart` — the (3a) headline as a `Nonempty` order-iso. Stated as `Nonempty`
  deliberately: an `≃o` is data (the Birkhoff encoding `enc T = {j ∈ J(P) : j ≤ T}` ≅ `a×(ℓ−a)`-cell
  ideals — cert part (i)), which the elder pass ratifies before the prove phase constructs it. The
  `Nonempty` Prop is all the `chainHeight` transport needs. **SORRIED — frontier.**
* `bindingSet_chainHeight` — the count corollary: `chainHeight(bindingSet) = a(ℓ−a)+1`, via the
  banked subtype-`≃o` chainHeight transport + `chainHeight_boxPart`. Proved MODULO the headline.

**Prove-phase construction plan (Codex design-check, thread-41/codex/enc-map-answer.md; verified on
both worked cores M=[1,1,2,1], [2,2,2,2,2] + Codex's own 1360-vector sweep).** The explicit iso is a
composite of THREE order-isos (`OrderIso.ofHomInv` or `toEquiv`+`map_rel_iff'`, then `.trans`):
1. `swapBindingOrderIso` — one adjacent width-swap, transporting the profile by the value-preserving
   map `R_{A,B}(P,X,Q) = X+(B−A)` (translation, `A≤B∧B−A≤P−X`) / `X−(A−B)` (`B<A∧A−B≤X−Q`) / `P+Q−X`
   (reflection); locally minimises `(P−X+A)²+(X−Q+B)²`.
2. `sortBindingOrderIso` — compose the bubble-sort swaps until widths are ascending `D₀≤…≤D_L`.
3. `sortedBindingOrderIsoBoxPart` — on sorted widths: active steps `xᵢ = eᵢ↑+D_{i+1} ∈ {C−1,C}`
   (`C=⌈ΣD/ℓ⌉`), a-subset `A={i<ℓ:xᵢ=C}`, box via reversed gaps (`Fin.rev`; see the codex answer).
   Hazard: the reverse `enc T ≤ enc T' ⟹ T ≤ T'` — prove `map_rel_iff` directly.

**NOVELTY + SCOPE FLAG.** The adjacent-swap transport is a NEW derived construction (not in Aoyagi,
not the cert's Lemma-4-step recipe — an equivalent explicit map Codex found). It is a genuine
multi-lemma build (~200+ LoC), NOT a one-lemma fill. The four painful new lemmas: (a) the swap
preserves `bindingSet`; (b) its local monotonicity on binding profiles; (c) bubble-sort transport
agrees with `shiftedSorted`; (d) the `qip*`→`ceilingM/residueA` bridge. Route decision (cert's
Lemma-4 map vs Codex's swap map) + the effort are surfaced to the controller before the build.

**Elder scaffold-pass questions (carried, per controller):**
1. RESOLVED by the Codex check: the sorted-`ell`/unsorted-`Adm` coupling is LOAD-BEARING (the
   adjacent-swap transport is exactly what bridges it) — it cannot be dropped. Ratify keeping
   `ℓ := ell M 0`, `a := (residueA M 0).toNat`, with the transport carrying the sort.
2. Domain hypotheses: `hpos : ∀ s, 0 < M s` (non-degenerate, `minMval ≥ 1`; the DLN destination
   supplies it). Confirm this is the weakest sufficient form.
3. Whether `bindingSet` belongs in `Core` (network-free combinatorics) or stays `DLN` (uses `ell`).
-/

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.DLN.RLCT DLNFibre.Core.Aoyagi.OrderChain

variable {L : ℕ}

/-- **The binding-profile domain**: admissible profiles achieving the `Mval`-minimum `minAdm`, i.e.
`{T ∈ Adm M : Mval M T = minAdm M}` (= the same set over `admTight`, by `adm_eq_admTight`). -/
def bindingSet (M : Fin (L + 1) → ℕ) : Set (Fin L → ℕ) :=
  {T | T ∈ Adm M ∧ Mval M T = (Adm M).inf' (Adm_nonempty M) (Mval M)}

/-- Subtype `≃o` transports strict-order `chainHeight` (banked contract, thread-41):
`Set.chainHeight_coe_univ` + `OrderIso.toRelIsoLT` + `Set.chainHeight_eq_of_relIso`. -/
theorem chainHeight_eq_of_orderIso {α β : Type*} [PartialOrder α] [PartialOrder β]
    (S : Set α) (T : Set β) (e : ↥S ≃o ↥T) :
    S.chainHeight (· < ·) = T.chainHeight (· < ·) := by
  rw [← Set.chainHeight_coe_univ S (· < ·), ← Set.chainHeight_coe_univ T (· < ·)]
  have himg : e.toRelIsoLT '' (Set.univ : Set ↥S) = Set.univ := by
    rw [Set.image_univ]; exact e.toEquiv.surjective.range_eq
  have h := Set.chainHeight_eq_of_relIso (Set.univ : Set ↥S) e.toRelIsoLT
  rw [himg] at h
  exact h.symm

/-- **(3a) THE REALIZATION ISO** (SORRIED — frontier): the binding-profile poset is order-isomorphic
to `BoxPart(ℓ,a)` (`ℓ = ell M 0`, `a = residueA M 0`), via the Birkhoff/box-cell encoding. Stated as
`Nonempty` — the explicit encoding is the prove-phase content the elder pass ratifies. -/
theorem bindingSet_orderIso_boxPart (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet M) ≃o ↥(BoxPart (ell M 0) ((residueA M 0).toNat))) := by
  sorry

/-- **The Tier-3 count corollary**: `chainHeight(bindingSet) = a(ℓ−a)+1 = aoyagiTheta`, via the
realization iso + the banked subtype-`≃o` transport + `chainHeight_boxPart`. Proved MODULO the
headline `bindingSet_orderIso_boxPart`. -/
theorem bindingSet_chainHeight (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    (bindingSet M).chainHeight (· < ·)
      = ((((residueA M 0).toNat) * (ell M 0 - (residueA M 0).toNat) + 1 : ℕ) : ℕ∞) := by
  obtain ⟨e⟩ := bindingSet_orderIso_boxPart M hpos
  rw [chainHeight_eq_of_orderIso _ _ e, chainHeight_boxPart]

end DLNFibre.DLN.Aoyagi

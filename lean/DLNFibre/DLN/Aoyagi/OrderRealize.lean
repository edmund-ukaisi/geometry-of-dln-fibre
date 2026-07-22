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

**NOVELTY + SCOPE (name-for-content).** This module records Codex's adjacent-swap map, NOT the
cert's Lemma-4-step recipe. Both were verified (cert via a backtracker; Codex's by hand on the
worked cores + `g-enc-adjacent-swap.py`); the two are DIFFERENT constructions and their equivalence
is NOT needed — any valid order-iso discharges the `Nonempty` headline. The thread-42 cert is the
adjudication record; this module is the construction record. A multi-lemma build (~200+ LoC), not a
one-lemma fill. Four frontier obligations: (a)+(b) `swapBinding_orderIso` (one swap is an order-iso;
preserve + coupled monotonicity are bundled, since atomic `swapR`-in-`X` monotonicity is FALSE);
(c) `bindingSet_transport_sorted`; (d) `residueA_le_ell` + the sorted-box iso. Route (a) = the
controller's BUILD ruling.

**Elder full-pass rulings (scaffold RATIFIED, statement-honest):**
1. Coupling: the sorted-`ell`/unsorted-`Adm` coupling is LOAD-BEARING and ratified — keep
   `ℓ := ell M 0`, `a := (residueA M 0).toNat`; the adjacent-swap transport carries the sort (it IS
   permutation-invariance made explicit). Do NOT restate over a fixed `(ℓ,a)`.
2. Domain hyp `hpos : ∀ s, 0 < M s` is weakest-sufficient on statements 1, 2, 4 (`BoxPart` is
   ill-defined at zero width). For `residueA_le_ell` (statement 3), `hpos` may not fire (`a ≤ ℓ` may
   be definitional / need only `ell > 0`) — DROP it there if the proof does not use it.
3. Home: `bindingSet` + the iso are general combinatorics that belong in `Core` — BUT the import
   direction blocks the move now (`Core` must never import `DLN`, and this consumes `Adm`/`Mval`
   which live `DLN`-side). The whole `Adm`/`Mval`/`bindingSet` cluster migrates together in the
   post-monument upstreaming unit (controller-scheduled with M4/M9); stays `DLN` until then.

**`r = 0` scope (statement 2, elder-noted CORRECT).** `ell M 0` / `residueA M 0` use `r = 0`: `M` is
the *reduced core* width vector, on which the Def-3 selectors are read directly. This is NOT lost
generality — general-`r` arrives upstream via the R0/R1 rank reduction (`M^(s) = H^(s) − r`); the
reduced core is the object the count is stated on. -/

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.DLN.RLCT DLNFibre.Core.Aoyagi.OrderChain

variable {L : ℕ}

/-- **The binding-profile domain**: admissible profiles achieving the `Mval`-minimum `minAdm`, i.e.
`{T ∈ Adm M : Mval M T = minAdm M}`. (`Adm` already carries the run-min bound — `Adm_le_runMin` —
so no separate "tight cone" is needed; the former `admTight` collapsed to `Adm`.) -/
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

/-- Sorted reduced widths: `M` composed with the ascending sort (`shiftedSorted _ 0`, `r = 0` so
`dminus = M`). The realization iso factors through the sorted widths (elder Q1: the sort is
load-bearing, carried by the adjacent-swap transport). -/
noncomputable def sortedWidths (M : Fin (L + 1) → ℕ) : Fin (L + 1) → ℕ := shiftedSorted M 0

/-- Swap two adjacent width entries `k, k+1` of `M`. The bubble-sort transport composes these. -/
def swapWidths (k : Fin L) (M : Fin (L + 1) → ℕ) : Fin (L + 1) → ℕ :=
  M ∘ Equiv.swap k.castSucc k.succ

/-- Codex's atomic value-preserving adjacent-swap on the middle profile coordinate (the construction
witness for `swapBinding_orderIso`): `X ↦ X+(B−A)` (translation) / `X−(A−B)` / `P+Q−X` (reflection),
minimising `(P−X+A)²+(X−Q+B)²`. NOT monotone in `X` alone — the transport's monotonicity is a
*coupled* profile property (`P = t⁽ᵏ⁻²⁾`, `X = t⁽ᵏ⁻¹⁾`, `Q = t⁽ᵏ⁾` move together), which is why the
obligation is bundled as the one-swap order-iso below, not an atomic `swapR`-in-`X` lemma. -/
def swapR (P X Q A B : ℕ) : ℕ :=
  if A ≤ B ∧ B - A ≤ P - X then X + (B - A)
  else if B < A ∧ A - B ≤ X - Q then X - (A - B)
  else P + Q - X

/-- The adjacent width-swap is an involution (`Equiv.swap` applied twice is the identity) — the
foundation for the reverse direction of `swapBinding_orderIso`. -/
theorem swapWidths_swapWidths (k : Fin L) (M : Fin (L + 1) → ℕ) :
    swapWidths k (swapWidths k M) = M := by
  funext i
  simp only [swapWidths, Function.comp_apply, Equiv.swap_apply_self]

/-- `swapR` is a self-inverse on the middle coordinate under the width-swap `A ↔ B`, on the range
`Q ≤ X ≤ P` (Codex swap-iso design §1): `swapR P (swapR P X Q A B) Q B A = X`. Pure ℕ; the reverse
transport reuses this + `swapWidths_swapWidths`. -/
theorem swapR_swapR (P X Q A B : ℕ) (hQX : Q ≤ X) (hXP : X ≤ P) :
    swapR P (swapR P X Q A B) Q B A = X := by
  unfold swapR
  split_ifs <;> omega

/-- **`Mval`-invariance heart** (Codex swap-iso design §2): the two `Mval` summands that change
under the swap are equal — `F_{A,B}(P,X,Q) = F_{B,A}(P, swapR P X Q A B, Q)` over `ℤ`, where
`F_{A,B}(P,X,Q) = (P−X)(A−X) + (X−Q)(B−Q)`. Each `swapR` branch is a genuine polynomial identity
(translation preserves the two squares of `(P−X+A)²+(X−Q+B)²`, reflection exchanges them); the range
hyps only interpret the truncated `ℕ` subtractions as `ℤ`. -/
theorem swapR_F_invariant (P X Q A B : ℕ) (hQX : Q ≤ X) (hXP : X ≤ P) :
    ((P : ℤ) - X) * ((A : ℤ) - X) + ((X : ℤ) - Q) * ((B : ℤ) - Q)
      = ((P : ℤ) - swapR P X Q A B) * ((B : ℤ) - swapR P X Q A B)
        + ((swapR P X Q A B : ℤ) - Q) * ((A : ℤ) - Q) := by
  unfold swapR
  split_ifs with h1 h2
  · have hY : ((X + (B - A) : ℕ) : ℤ) = (X : ℤ) + B - A := by omega
    rw [hY]; ring
  · have hY : ((X - (A - B) : ℕ) : ℤ) = (X : ℤ) - A + B := by omega
    rw [hY]; ring
  · have hY : ((P + Q - X : ℕ) : ℤ) = (P : ℤ) + Q - X := by omega
    rw [hY]; ring

/-- The profile transport for one adjacent width-swap at `k` (Codex swap-iso design §1): for `k > 0`
update the coordinate `k−1` by `swapR P X Q A B` (`P = t⁽ᵏ⁻²⁾` or `M⁰` at `k=1`, `X = t⁽ᵏ⁻¹⁾`,
`Q = t⁽ᵏ⁾`, `A = M_k`, `B = M_{k+1}`); for `k = 0` the identity (the swapped pair is `M⁰,M¹`, no
profile coordinate moves). -/
def swapProfile (M : Fin (L + 1) → ℕ) (k : Fin L) (T : Fin L → ℕ) : Fin L → ℕ :=
  if _ : 0 < k.val then
    Function.update T ⟨k.val - 1, by have := k.isLt; omega⟩
      (swapR (if k.val = 1 then M 0 else T ⟨k.val - 2, by have := k.isLt; omega⟩)
        (T ⟨k.val - 1, by have := k.isLt; omega⟩) (T k) (M k.castSucc) (M k.succ))
  else T

/-- **(a)+(b) ONE-SWAP ORDER-ISO** (SORRIED — frontier; bundles "swap preserves `bindingSet`" +
"local coupled monotonicity of `R`"): one adjacent width-swap induces an order-isomorphism of the
binding poset, via the `swapR` transport. Bundled because the monotonicity couples three profile
coords, so the honest statement is the iso, not an atomic `swapR`-in-`X` fact (which is false). -/
theorem swapBinding_orderIso (M : Fin (L + 1) → ℕ) (k : Fin L) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (swapWidths k M))) := by
  sorry -- map: enc-swap (a)+(b)

/-- **(c) THE BUBBLE-SORT TRANSPORT** (SORRIED — frontier): composing the adjacent-swap isos
transports the binding poset to the sorted-width binding poset (`sortedWidths = shiftedSorted _ 0`;
"bubble-sort transport agrees with `shiftedSorted`"). -/
theorem bindingSet_transport_sorted (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (sortedWidths M))) := by
  sorry -- map: enc-transport (c)

/-- **(d) WELL-FORMEDNESS of `(ℓ,a)`** (PROVED): `a = residueA ≤ ℓ = ell`, so `BoxPart(ℓ,a)`'s bound
`ℓ−a` is meaningful. Hypothesis is `0 < ell M 0` — the elder's Q2 hpos-check FIRES negative here:
`hpos` (positive widths) does NOT enter; only `ell > 0` is needed (the ceiling arithmetic divides by
`ℓ`). Proof: `residueA = S − (⌈S/ℓ⌉−1)·ℓ ∈ {S mod ℓ, ℓ}` (both `≤ ℓ`), reusing the `ClosedForm`
`hresval` reasoning at `r = 0`; then `Int.toNat_le`. -/
theorem residueA_le_ell (M : Fin (L + 1) → ℕ) (hℓ : 0 < ell M 0) :
    (residueA M 0).toNat ≤ ell M 0 := by
  rw [Int.toNat_le]
  set ℓ : ℤ := (ell M 0 : ℤ) with hℓdef
  set S : ℤ := activeSum M 0 with hSdef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact_mod_cast hℓ
  have hρ0 : 0 ≤ S % ℓ := Int.emod_nonneg S (by omega)
  have hρlt : S % ℓ < ℓ := Int.emod_lt_of_pos S hℓpos
  have hdm : ℓ * (S / ℓ) + S % ℓ = S := Int.mul_ediv_add_emod S ℓ
  have hreseq : residueA M 0 = S - (((S + ℓ - 1) / ℓ) - 1) * ℓ := rfl
  rcases eq_or_lt_of_le hρ0 with hρeq | hρpos
  · -- `S % ℓ = 0`: `residueA = ℓ`
    have hdiv : (S + ℓ - 1) / ℓ = S / ℓ :=
      (Int.ediv_emod_unique hℓpos (r := ℓ - 1) (q := S / ℓ)).mpr
        ⟨by linarith [hdm], by omega, by omega⟩ |>.1
    rw [hreseq, hdiv]
    have hmul : ℓ * (S / ℓ) = S := by linarith [hdm]
    nlinarith [hmul]
  · -- `S % ℓ ≥ 1`: `residueA = S % ℓ < ℓ`
    have hdiv : (S + ℓ - 1) / ℓ = S / ℓ + 1 :=
      (Int.ediv_emod_unique hℓpos (r := S % ℓ - 1) (q := S / ℓ + 1)).mpr
        ⟨by nlinarith [hdm], by omega, by omega⟩ |>.1
    rw [hreseq, hdiv]
    have hmul : ℓ * (S / ℓ) = S - S % ℓ := by linarith [hdm]
    nlinarith [hmul]

/-- Descent increment `eᵢ↑` of a profile on widths `D` (Codex step 3; `t⁰ := D 0`):
`e₀ = D₀ − T₀`, `eᵢ = Tᵢ₋₁ − Tᵢ`. Over `ℤ` (a difference); `≥ 0` on admissible profiles. -/
def sIncr (D : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (i : Fin L) : ℤ :=
  if i.val = 0 then (D 0 : ℤ) - (T i : ℤ) else (T ⟨i.val - 1, by omega⟩ : ℤ) - (T i : ℤ)

/-- Active step `xᵢ = eᵢ↑ + D_{i+1}` (Codex step 3); on a binding profile `xᵢ ∈ {C−1, C}`. -/
def sStep (D : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (i : Fin L) : ℤ :=
  sIncr D T i + (D i.succ : ℤ)

/-- Each descent increment is nonnegative on an admissible profile: `e₀ = D₀ − T₀ ≥ 0`
(`T₀ ≤ admBound = min(D₀,D₁) ≤ D₀`) and `eᵢ = Tᵢ₋₁ − Tᵢ ≥ 0` (weak-decrease). -/
theorem sIncr_nonneg (D : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm D) (i : Fin L) :
    0 ≤ sIncr D T i := by
  rw [Adm, Finset.mem_filter] at hT
  obtain ⟨-, hbound, hdec, -⟩ := hT
  unfold sIncr
  split
  · next h =>
    rw [sub_nonneg]
    have hb := hbound i
    unfold admBound at hb
    rw [if_pos h] at hb
    exact_mod_cast le_trans hb (min_le_left _ _)
  · next h =>
    rw [sub_nonneg]
    have hidx : i.val - 1 < L := by have := i.isLt; omega
    have hle : T i ≤ T ⟨i.val - 1, hidx⟩ :=
      hdec ⟨i.val - 1, hidx⟩ i (Fin.le_def.mpr (show i.val - 1 ≤ i.val by omega))
    exact_mod_cast hle

/-- The a-subset `A(T) ⊆ [ℓ]`: profile indices `i < ℓ` whose active step equals `C = ceilingM`
(the "M-steps", Codex step 3). Kept as a `Finset (Fin L)` (filtered by `i < ℓ`) to avoid `Fin ℓ`
casts; `boxSubset_card` pins `|A| = a`. -/
noncomputable def boxSubset (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Finset (Fin L) :=
  Finset.univ.filter (fun i => i.val < ell M 0 ∧ sStep (sortedWidths M) T i = ceilingM M 0)

/-- **THE SORTED-CASE BOX ISO** (SORRIED — frontier; OWNED BY seat-Ecore, branch
`expedition/aoyagi-engine-Ecore`, module `OrderRealizeSortedBox.lean`): on sorted widths, the
binding poset is order-isomorphic to `BoxPart(ℓ,a)` via the active-step a-subset + reversed-gap
encoding (Codex part 1, step 3). The pivotal sub-lemmas (`sStep ∈ {C−1,C}` on binding profiles
[Aoyagi Lemma 4-5], `|A| = residueA`, enc/dec, both-direction `map_rel_iff`) are seat-Ecore's; the
controller wires the discharge at integration. `sIncr`/`sStep`/`boxSubset`/`sIncr_nonneg` here are
its shared floor. -/
theorem bindingSet_sorted_orderIso_boxPart (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet (sortedWidths M)) ≃o ↥(BoxPart (ell M 0) ((residueA M 0).toNat))) := by
  sorry -- map: enc-sorted-box

/-- **(3a) THE REALIZATION ISO** — discharged from the transport (c) + the sorted-case box iso, by
composition. NON-sorried: the frontier is the four obligations above. -/
theorem bindingSet_orderIso_boxPart (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    Nonempty (↥(bindingSet M) ≃o ↥(BoxPart (ell M 0) ((residueA M 0).toNat))) := by
  obtain ⟨e1⟩ := bindingSet_transport_sorted M hpos
  obtain ⟨e2⟩ := bindingSet_sorted_orderIso_boxPart M hpos
  exact ⟨e1.trans e2⟩

/-- **The Tier-3 count corollary**: `chainHeight(bindingSet) = a(ℓ−a)+1 = aoyagiTheta`, via the
realization iso + the banked subtype-`≃o` transport + `chainHeight_boxPart`. Proved MODULO the
headline `bindingSet_orderIso_boxPart`. -/
theorem bindingSet_chainHeight (M : Fin (L + 1) → ℕ) (hpos : ∀ s, 0 < M s) :
    (bindingSet M).chainHeight (· < ·)
      = ((((residueA M 0).toNat) * (ell M 0 - (residueA M 0).toNat) + 1 : ℕ) : ℕ∞) := by
  obtain ⟨e⟩ := bindingSet_orderIso_boxPart M hpos
  rw [chainHeight_eq_of_orderIso _ _ e, chainHeight_boxPart]

end DLNFibre.DLN.Aoyagi

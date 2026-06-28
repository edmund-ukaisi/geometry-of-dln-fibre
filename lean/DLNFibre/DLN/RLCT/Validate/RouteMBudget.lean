import DLNFibre.DLN.RLCT.Validate.RouteMAchieverStructAdm
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverPath

/-!
# `RouteMBudget` — the budget identity `#angular = minAdm − 1` (∀M, sub-tide 2)

The radial blow-up of the interior achiever chart has exactly `minAdm` free `R`-block angular directions
(one of which is fixed to `1` as the pivot — a free gauge — leaving `minAdm − 1` genuine angular coords,
the codim of the achiever center). The budget identity in CHAIN widths:

  **`∑_{k:Fin L} (Text(k) − Text(k+1))·(Wext(k) − Text(k+1)) + Text(L)·Wext(L) = minAdm M`**  (at `tach M`)

The interior E-block at boundary `k` has dimension `r_k·c_k = (Text k − Text(k+1))(Wext k − Text(k+1))`;
the boundary `k = 0` term vanishes (`r_0 = M_0 − M_0 = 0`); the leaf residual `Rfin` block is
`Text(L)·Wext(L)`. genm-budget's cert: this is a ONE-LINE REINDEX of the banked Aoyagi
`sum_rBlock_cBlock_eq_minAdm : ∑_{j:Fin L} rBlock·cBlock = minAdm`, the only difference being the `j = L−1`
Aoyagi term `(tStar_{L−2} − tStar_{L−1})(M_L − tStar_{L−1})` which, by the leaf admissibility
`tStar_{L−1} = 0`, equals `tStar_{L−2}·M_L = Text(L)·Wext(L)` — the leaf term. The chain interior sum
(`k = 1..L−1`) matches the Aoyagi `j = 0..L−2` terms (shift `k ↔ j+1`); the boundary `0` chain term is `0`.

Over ℤ (the Aoyagi blocks are signed differences); the `Text`/`Wext` are ℕ so cast.

Axiom-clean modulo `Classical.choice` (the `tStar` minimiser): `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The per-boundary chain E-block dimension over ℤ, matched to the Aoyagi `rBlock·cBlock` -/

/-- The chain E-block dimension at boundary `k` (over ℤ): `(Text k − Text(k+1))·(Wext k − Text(k+1))`,
at the achiever path `tach M`. -/
noncomputable def chainEdimZ (M : Fin (L + 1) → ℕ) (k : ℕ) : ℤ :=
  ((Text M (tach M) k : ℤ) - (Text M (tach M) (k + 1) : ℤ))
    * ((Wext M k : ℤ) - (Text M (tach M) (k + 1) : ℤ))

/-- **The predecessor `tPrev (tStar) j` is `tach M ⟨j,_⟩`** (over ℤ): both are `M 0` at `j = 0` and
`tStar_{j−1}` for `j ≥ 1`. The width bridge for `rBlock`. -/
theorem tPrev_tStar_eq_tach (M : Fin (L + 1) → ℕ) (j : Fin L) :
    tPrev M (tStar M) j = (tach M ⟨j.val, by omega⟩ : ℤ) := by
  simp only [tPrev]
  by_cases hj : j.val = 0
  · rw [if_pos hj]
    rw [show (⟨j.val, by omega⟩ : Fin (L + 1)) = 0 from by apply Fin.ext; simp [hj], tach_zero]
  · rw [if_neg hj]
    have : tach M ⟨j.val, by omega⟩ = tStar M ⟨j.val - 1, by omega⟩ := by
      rw [← tach_succ M ⟨j.val - 1, by omega⟩]
      congr 1; apply Fin.ext; simp [Fin.succ]; omega
    rw [this]

/-- **The chain E-block at boundary `j.succ` equals the Aoyagi `rBlock·cBlock` at `j`** (`j : Fin L`).
The width bridge: `Text (tach) (j+1) = tach j = tPrev (tStar) j`, `Text (tach) (j+2) = tach (j+1) =
tStar_j`, `Wext (j+1) = M_{j+1}`. -/
theorem chainEdimZ_succ_eq_rBlock_cBlock (M : Fin (L + 1) → ℕ) (j : Fin L) :
    chainEdimZ M (j.val + 1) = rBlock M j * cBlock M j := by
  -- the three chain widths, as ℕ, via the achiever-path readers
  have hT1 : Text M (tach M) (j.val + 1) = tach M ⟨j.val, by omega⟩ :=
    Text_tach_succ M j.val (by omega)
  have hT2 : Text M (tach M) (j.val + 1 + 1) = tStar M j := by
    rw [Text_tach_succ M (j.val + 1) (by omega), tach_mk_succ M j.val (by omega)]
  have hW : Wext M (j.val + 1) = M j.succ := by
    rw [Wext_apply M (j.val + 1) (by omega)]; congr 1
  -- the predecessor bridge `tach ⟨j,_⟩ = tPrev (tStar) j`
  have hP : (tach M ⟨j.val, by omega⟩ : ℤ) = tPrev M (tStar M) j := (tPrev_tStar_eq_tach M j).symm
  rw [chainEdimZ, rBlock, cBlock, hT1, hT2, hW, hP]

/-! ## The leaf term equals the last Aoyagi block -/

/-- **The leaf residual block `Text(L)·Wext(L)` is the last Aoyagi block `rBlock·cBlock` at `⟨L−1,_⟩`**
(over ℤ). By the leaf admissibility `tStar_{L−1} = 0` (`admPred`'s leaf clause), `rBlock_{L−1} =
tPrev_{L−1} − 0 = tach(L−1) = Text(L)` and `cBlock_{L−1} = M_L − 0 = Wext(L)`. -/
theorem leafTerm_eq_rBlock_cBlock (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    (Text M (tach M) L : ℤ) * (Wext M L : ℤ)
      = rBlock M ⟨L - 1, by omega⟩ * cBlock M ⟨L - 1, by omega⟩ := by
  -- The leaf index `jL = ⟨L−1, _⟩ : Fin L`.
  set jL : Fin L := ⟨L - 1, by omega⟩ with hjL
  -- Leaf admissibility (`admPred`'s third clause): `tStar M jL = 0` since `jL.val = L − 1`.
  have hzero : tStar M jL = 0 :=
    (Finset.mem_filter.1 (tStar_mem M)).2.2.2 jL (by simp [hjL])
  -- RHS, with `tStar M jL = 0`:  rBlock = tPrev, cBlock = M jL.succ.
  rw [rBlock, cBlock, hzero, Nat.cast_zero, sub_zero, sub_zero]
  -- The successor `jL.succ : Fin (L+1)` is the in-range index `⟨L, _⟩`, so `M jL.succ = Wext M L`.
  have hsucc : M jL.succ = Wext M L := by
    rw [Wext_apply M L (by omega)]; congr 1
    apply Fin.ext; rw [Fin.val_succ, hjL]; simp; omega
  -- The compressed leaf width `Text M (tach M) L = tach M ⟨L−1, _⟩ = tPrev M (tStar M) jL`.
  have hT : (Text M (tach M) L : ℤ) = tPrev M (tStar M) jL := by
    rw [tPrev_tStar_eq_tach M jL]
    have hidx : (⟨jL.val, by omega⟩ : Fin (L + 1)) = ⟨L - 1, by omega⟩ := by
      apply Fin.ext; simp [hjL]
    rw [hidx, ← Text_tach_succ M (L - 1) (by omega), Nat.sub_add_cancel hL]
  rw [hT, hsucc]

/-- **THE BUDGET IDENTITY (★)** over ℤ: `∑_{k:Fin L} (Text k − Text(k+1))(Wext k − Text(k+1)) +
Text(L)·Wext(L) = minAdm M` (at the achiever path). The interior chain E-blocks (`k = 1..L−1`; the
`k = 0` term vanishes, `r_0 = M_0 − M_0 = 0`) plus the leaf residual block sum to the codim `minAdm`.
A one-line REINDEX of the banked Aoyagi `sum_rBlock_cBlock_eq_minAdm`: the chain sum (boundary `0` zero,
`k = j+1` matched to Aoyagi `j`) covers Aoyagi `j = 0..L−2`; the leaf term is the missing Aoyagi `j = L−1`
block (`leafTerm_eq_rBlock_cBlock`). -/
theorem budget_identity (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    (∑ k : Fin L, chainEdimZ M k.val) + (Text M (tach M) L : ℤ) * (Wext M L : ℤ)
      = (minAdm M : ℤ) := by
  -- Make `L` syntactically `L' + 1` everywhere (motive-stable; no dependent-`Fin` rewrite).
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  -- Aoyagi side: `∑_{j:Fin (L'+1)} rBlock·cBlock = minAdm`.
  rw [← sum_rBlock_cBlock_eq_minAdm M]
  -- Peel the leaf (last) Aoyagi term; the leaf-block bridge identifies it with the leaf residual.
  rw [Fin.sum_univ_castSucc (f := fun j => rBlock M j * cBlock M j)]
  have hleaf : (Text M (tach M) (L' + 1) : ℤ) * (Wext M (L' + 1) : ℤ)
      = rBlock M (Fin.last L') * cBlock M (Fin.last L') := by
    have := leafTerm_eq_rBlock_cBlock M hL
    rwa [show (⟨L' + 1 - 1, by omega⟩ : Fin (L' + 1)) = Fin.last L' from by
      apply Fin.ext; simp] at this
  rw [hleaf]
  -- Peel the chain `k = 0` term (`= 0`, since `Text 0 = Text 1 = M 0`).
  rw [Fin.sum_univ_succ (f := fun k => chainEdimZ M k.val)]
  have hchain0 : chainEdimZ M (0 : Fin (L' + 1)).val = 0 := by
    simp only [Fin.val_zero, chainEdimZ]
    rw [Text_zero, Text_tach_succ M 0 (by omega), tach_mk_zero M (by omega)]
    ring
  rw [hchain0, zero_add]
  -- Match the interior chain terms to the Aoyagi `castSucc` terms via the proven width bridge.
  rw [add_left_inj]
  apply Finset.sum_congr rfl
  intro i _
  have h := chainEdimZ_succ_eq_rBlock_cBlock M i.castSucc
  rw [Fin.val_castSucc] at h
  rw [Fin.val_succ]
  exact h

end DLNFibre.DLN.RLCT

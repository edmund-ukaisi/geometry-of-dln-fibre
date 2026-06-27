import DLNFibre.DLN.RLCT.Validate.RouteMAchieverPath
import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatStruct

/-!
# `RouteMAchieverStructAdm` — the shifted achiever path `tach M` + `StructAdm M (tach M)`

The structured decoder (`genBlkFlatStruct`) and its rate consume a descent path `t : Fin (L+1) → ℕ`
through `StructAdm M t`. The achiever minimiser `tStar M : Fin L → ℕ` (`RouteMAchieverPath`, the
`Mval`-argmin with `Mval M (tStar M) = minAdm M`) must be SHIFTED into the chain's `Fin (L+1) → ℕ`
descent-path convention:

  **`tach M := Fin.cons (M 0) (tStar M)`** — `tach 0 = M 0` (the identity-boundary convention,
  `Text 0 = Text 1`), `tach (k+1) = tStar M k` (the genuine descent ranks).

Per the chain↔Aoyagi bridge (`certificate-genM-Bdet §1`): `Text M tach 0 = M 0`,
`Text M tach (k+1) = tach k`, so Aoyagi block `j` realises at chain boundary `k = j+1`.

* `tach` — the shifted achiever path.
* `tach_zero` / `tach_succ` — `tach 0 = M 0`, `tach (k+1) = tStar M k`.
* `structAdm_tach` — **`StructAdm M (tach M)`** for `0 < L`: the structured-decoder admissibility,
  from `tStar ∈ Adm M` (weak-decrease + the per-layer bounds, banked `tStar_le_tPrev`/`tStar_le_Msucc`).

Specialization: `tach M222 = (2, tStar M222 0, tStar M222 1)`; what matters is the INVARIANTS
(`Mval (tStar) = minAdm`, the admissibility), not the literal minimiser.

Axiom-clean modulo `Classical.choice` (the `tStar` minimiser choice) `[propext, Classical.choice,
Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The shifted achiever path `tach M` -/

/-- **The shifted achiever path** `tach M : Fin (L+1) → ℕ` — `Fin.cons (M 0) (tStar M)`. `tach 0 = M 0`
(the identity boundary), `tach (k+1) = tStar M k` (the achiever descent ranks). -/
noncomputable def tach (M : Fin (L + 1) → ℕ) : Fin (L + 1) → ℕ :=
  Fin.cons (M 0) (tStar M)

@[simp] theorem tach_zero (M : Fin (L + 1) → ℕ) : tach M 0 = M 0 := by
  simp [tach]

@[simp] theorem tach_succ (M : Fin (L + 1) → ℕ) (k : Fin L) : tach M k.succ = tStar M k := by
  simp [tach]

/-- `Text M (tach M) (k+1) = tach M ⟨k, _⟩` for `k < L+1` (the descent reader). -/
theorem Text_tach_succ (M : Fin (L + 1) → ℕ) (k : ℕ) (h : k < L + 1) :
    Text M (tach M) (k + 1) = tach M ⟨k, h⟩ := Text_succ M (tach M) k h

/-- `tach M ⟨0, _⟩ = M 0` (the identity-boundary value, at any in-range `Fin` index). -/
theorem tach_mk_zero (M : Fin (L + 1) → ℕ) (h : 0 < L + 1) : tach M ⟨0, h⟩ = M 0 := by
  have : (⟨0, h⟩ : Fin (L + 1)) = 0 := rfl
  rw [this, tach_zero]

/-- `tach M ⟨k+1, _⟩ = tStar M ⟨k, _⟩` (the descent value, at an in-range `Fin` index). -/
theorem tach_mk_succ (M : Fin (L + 1) → ℕ) (k : ℕ) (h : k + 1 < L + 1) :
    tach M ⟨k + 1, h⟩ = tStar M ⟨k, by omega⟩ := by
  have : (⟨k + 1, h⟩ : Fin (L + 1)) = (⟨k, by omega⟩ : Fin L).succ := by apply Fin.ext; simp
  rw [this, tach_succ]

/-! ## `StructAdm M (tach M)` (the achiever-path admissibility) -/

/-- **`StructAdm M (tach M)`** (for `0 < L`) — the structured decoder's admissibility for the shifted
achiever path. The boundary `h0` is the identity convention (`tach 0 = M 0`); the per-layer bounds and
the descent come from `tStar ∈ Adm M` (`tStar_le_tPrev` for the weak decrease, `tStar_le_Msucc` for the
residual-column bound). Out-of-range `k ≥ L` is the `Text`/`Wext` saturation to `1`. -/
theorem structAdm_tach (M : Fin (L + 1) → ℕ) (hL : 0 < L) : StructAdm M (tach M) := by
  refine ⟨?_, ?_, hL, ?_, ?_⟩
  · -- h0 : tDesc M (tach M) 0 = M 0, i.e. Text M (tach M) 1 = M 0
    rw [tDesc_apply, Text_tach_succ M 0 (by omega), tach_mk_zero M (by omega)]
  · -- hc p : tDesc M (tach M) (p+1) ≤ Wext M (p+1)
    intro p
    rw [tDesc_apply]
    rcases lt_or_ge (p + 1) (L + 1) with h | h
    · -- in range: tach ⟨p+1,_⟩ = tStar M ⟨p,_⟩ ≤ M (p+1).succ-ish; use tStar_le_Msucc
      rw [Text_tach_succ M (p + 1) h, tach_mk_succ M p h, Wext_apply M (p + 1) h]
      have hlt : p < L := by omega
      have := tStar_le_Msucc M (tStar M) (tStar_mem M) ⟨p, hlt⟩
      have hcast : (tStar M ⟨p, hlt⟩ : ℤ) ≤ (M (⟨p, hlt⟩ : Fin L).succ : ℤ) := this
      have hsucc : (⟨p, hlt⟩ : Fin L).succ = (⟨p + 1, by omega⟩ : Fin (L + 1)) := by
        apply Fin.ext; simp
      rw [hsucc] at hcast
      exact_mod_cast hcast
    · -- out of range: both sides saturate to 1 (`Text (p+2) = 1`, `Wext (p+1) = 1`)
      rw [show Text M (tach M) (p + 2) = 1 from by simp only [Text]; rw [dif_neg (by omega)],
          show Wext M (p + 1) = 1 from by rw [Wext]; rw [dif_neg (by omega)]]
  · -- hdesc k (k < L) : Text M (tach M) (k+2) ≤ Text M (tach M) (k+1), i.e. tach (k+1) ≤ tach k
    intro k hk
    have h1 : k + 1 < L + 1 := by omega
    rw [Text_tach_succ M (k + 1) h1, Text_tach_succ M k (by omega)]
    rw [tach_mk_succ M k h1]
    -- need tStar M ⟨k,_⟩ ≤ tach M ⟨k,_⟩
    match k, hk, h1 with
    | 0, hk, _ =>
      -- k = 0: tStar M ⟨0,_⟩ ≤ tach M ⟨0,_⟩ = M 0; from tStar_le_tPrev at j=0 (tPrev = M 0)
      rw [tach_mk_zero M (by omega)]
      have htp := tStar_le_tPrev M (tStar M) (tStar_mem M) ⟨0, hk⟩
      rw [tPrev, if_pos rfl] at htp
      exact_mod_cast htp
    | (k' + 1), hk, h1 =>
      -- k = k'+1: tStar M ⟨k'+1,_⟩ ≤ tach M ⟨k'+1,_⟩ = tStar M ⟨k',_⟩ (weak decrease)
      rw [tach_mk_succ M k' (by omega)]
      have htp := tStar_le_tPrev M (tStar M) (tStar_mem M) ⟨k' + 1, hk⟩
      have htPrev : tPrev M (tStar M) ⟨k' + 1, hk⟩ = (tStar M ⟨k', by omega⟩ : ℤ) := by
        simp only [tPrev, Nat.add_one_ne_zero, if_false]
        norm_num
      rw [htPrev] at htp
      exact_mod_cast htp
  · -- hub k : Text M (tach M) (k+2) ≤ Wext M (k+1) — same bound as hc shifted
    intro k
    rcases lt_or_ge (k + 1) (L + 1) with h1 | h1
    · rw [Text_tach_succ M (k + 1) h1, tach_mk_succ M k h1, Wext_apply M (k + 1) (by omega)]
      have hkL : k < L := by omega
      have := tStar_le_Msucc M (tStar M) (tStar_mem M) ⟨k, hkL⟩
      have hcast : (tStar M ⟨k, hkL⟩ : ℤ) ≤ (M (⟨k, hkL⟩ : Fin L).succ : ℤ) := this
      have hsucc : (⟨k, hkL⟩ : Fin L).succ = (⟨k + 1, by omega⟩ : Fin (L + 1)) := by
        apply Fin.ext; simp
      rw [hsucc] at hcast
      exact_mod_cast hcast
    · rw [show Text M (tach M) (k + 2) = 1 from by simp only [Text]; rw [dif_neg (by omega)],
          show Wext M (k + 1) = 1 from by rw [Wext]; rw [dif_neg (by omega)]]

end DLNFibre.DLN.RLCT

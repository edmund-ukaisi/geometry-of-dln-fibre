import DLNFibre.Core.Aoyagi.PrincipalInv
import DLNFibre.Core.Aoyagi.BlockBlowup
import DLNFibre.Core.Aoyagi.MonomialRLCT

/-!
# `Core.Aoyagi.Corank2TerminalProto` — GATE-3: the TERMINAL two-sided `hideal`, reverse-cheapness

The go/no-go measurement for **route P** (the two-sided normal-crossing lower bound). It builds the
**terminal monomialisation of a corank-2 residual block, BOTH directions**, end-to-end and sorry-free,
and pins down THE gate question: does the reverse `⟨diag b⟩ ⊆ ⟨(∏C)∘g⟩` (the exceptional monomial
recovered from the loss) close CHEAPLY at coupled corank-2, or hit a wall?

## The measured object

A corank-2 residual block (`Fin 4`, the 2×2 residual `Δ`'s slots in post-shear coordinates), blown up by
the banked `blockBlowupMap` (center = the block, pivot = slot 0). The pulled-back entries become
`(w₀, w₀·w₁, w₀·w₂, w₀·w₃) = w₀·(1, w₁, w₂, w₃)` — the terminal normal crossing with dominant monomial
`b = w₀ = E` and the **cleared pivot ≡ w₀** (strict transform `1`, nonvanishing incl. the origin). Feeding
this to the PROVEN `terminal_bezout` yields the terminal `PrincipalInv` (both divisibility `q` AND Bézout
`r`), and `principalInv_regionRepresents` (L1) packages it as the two `Chart.hideal` fields.

## The gate reading (see `gate3-tax-report.md`)

- **`hideal_bwd` (reverse) closes CHEAPLY.** `terminal_bezout` supplies the Bézout cofactor
  `r = 1/unit = 1` at the pivot (the exceptional monomial `E` is recovered from the cleared-pivot entry,
  `E = (resid 0 ∘ g)`). Continuity is `ContinuousOn.inv₀` on `{unit ≠ 0}`, never a `1/(vanishing)` — so
  the render's "the b-chain absorbs the reverse" is confirmed, and in fact the terminal reverse is even
  simpler than the maintenance-step `diag(b')⁻¹·P·diag(b')` conjugation: it is `1/unit` at the dominant
  pivot, INDEPENDENT of the coupling (the coupling lives in the dominated higher monomials `b₂,b₃ ∈ ⟨b₁⟩`).
- **`hideal_fwd` (forward) is the divisibility** `q = (1, w₁, w₂, w₃)`, polynomial. The remaining labour
  for the full `(3,3,4)` end-to-end is the explicit 21-variable composed chart `g` (block-elim shear +
  the radial T/ΔS blow-ups + the join) making `E ∣ every` pulled-back product entry — bounded
  detail-at-scale (per the render + Gröbner-banked normal crossing), NOT a wall, and NOT the reverse.

**Verdict basis:** the reverse (route P's specific risk — never before built two-sided) is GREEN. The
coupled corank-2 block monomialises to `⟨E⟩` with both inclusions holding on the region, the reverse
cofactor a continuous unit. The coupling enters upstream (the block-elim, `Corank2HidealProto`/
`Corank2Proto`, both directions PROVEN over the genuinely coupled `Δ`); it does not obstruct this terminal.
-/

open Matrix Set
open DLNFibre.Core.Aoyagi

namespace DLNFibre.Core.Aoyagi.Corank2TerminalProto

/-- The corank-2 residual block as a generator family: the four slots `w₀,w₁,w₂,w₃` (the `Δ`-block
entries in the post-shear chart, where the block-elim has placed the coupled residual). -/
def resid : Fin 4 → (Fin 4 → ℝ) → ℝ := fun i u ↦ u i

/-- The block-center blow-up of the residual block (center = whole block, pivot = slot 0): the banked
`blockBlowupMap`. Pulls the block back to `w₀·(1,w₁,w₂,w₃)`. -/
def gBlk : (Fin 4 → ℝ) → (Fin 4 → ℝ) := blockBlowupMap Finset.univ 0

/-- The dominant exceptional monomial `b = E = w₀`. -/
def bE : (Fin 4 → ℝ) → ℝ := fun u ↦ u 0

/-- The divisibility quotients `q = (1, w₁, w₂, w₃)` (`Fin 1`-indexed residual, terminal `resid ≡ 1`). -/
def qBlk : Fin 4 → Fin 1 → (Fin 4 → ℝ) → ℝ := fun i _ u ↦ if i = 0 then 1 else u i

/-- The pulled-back block entry: `(resid i ∘ gBlk) u = if i = 0 then w₀ else w₀·wᵢ`. -/
theorem resid_comp_gBlk (i : Fin 4) (u : Fin 4 → ℝ) :
    (resid i ∘ gBlk) u = if i = 0 then u 0 else u 0 * u i := by
  simp only [resid, gBlk, Function.comp_apply, blockBlowupMap, Finset.mem_univ, if_true]

/-- **The terminal `StepInv`** (forward divisibility): `(resid ∘ gBlk) = q · b`, residual `≡ 1`,
vanishing at `0`, quotients continuous. -/
theorem stepInv_blk : StepInv resid gBlk bE (fun _ : Fin 1 ↦ 1) qBlk Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · -- quotient continuity: `1` or a coordinate projection
    intro i _
    apply Continuous.continuousOn
    unfold qBlk
    split_ifs with h
    · exact continuous_const
    · exact continuous_apply i
  · -- `(resid i ∘ gBlk) 0 = 0`
    intro i
    rw [resid_comp_gBlk]
    split_ifs <;> simp
  · -- divisibility `(resid i ∘ gBlk) u = ∑ j, q i j u · (b u · 1)`
    intro u _ i
    rw [resid_comp_gBlk, Fin.sum_univ_one]
    simp only [qBlk, bE, Pi.one_apply, mul_one]
    split_ifs with h
    · simp
    · ring

/-- The cleared-pivot entry factors as `(resid 0 ∘ gBlk) = bE · 1` — the strict transform (`unit ≡ 1`)
is a nonvanishing unit (value `1` at the origin). This is what `terminal_bezout` inverts. -/
theorem pivot_entry : ∀ u ∈ (Set.univ : Set (Fin 4 → ℝ)),
    (resid 0 ∘ gBlk) u = bE u * 1 := by
  intro u _
  rw [resid_comp_gBlk, if_pos rfl]
  simp [bE]

/-! ## GATE-3: the terminal two-sided `hideal` closes — reverse via `terminal_bezout` -/

/-- **The terminal `PrincipalInv`** (BOTH directions) on an open `V' ∋ 0`, from the PROVEN Core theorem
`terminal_bezout`: the forward divisibility (`stepInv_blk`) + the nonvanishing cleared-pivot entry
(`pivot_entry`) give the Bézout `b = ∑ᵢ rᵢ·(residᵢ∘gBlk)` — the REVERSE — with cofactor `r = 1/unit`,
continuous on `V' = univ ∩ {unit ≠ 0}` (here `unit ≡ 1`, so `r` is the pivot indicator, trivially
continuous). This is the gate's measured object: the reverse closes CHEAPLY. -/
theorem principalInv_blk :
    ∃ (V' : Set (Fin 4 → ℝ)) (r : Fin 4 → (Fin 4 → ℝ) → ℝ),
      IsOpen V' ∧ (0 : Fin 4 → ℝ) ∈ V' ∧ V' ⊆ Set.univ ∧
      PrincipalInv resid gBlk bE (fun i ↦ qBlk i 0) r V' :=
  terminal_bezout isOpen_univ (Set.mem_univ 0) stepInv_blk 0 (fun _ ↦ 1)
    continuousOn_const one_ne_zero pivot_entry

/-- The dominant monomial `bE = w₀` in `monomialFam` form (exponent vector `[1,0,0,0]`), so the
statements below are literally the `Chart.hideal` shape `monomialFam bexp`. -/
theorem bE_eq_monomialFam :
    (fun _ : Fin 1 ↦ bE) = monomialFam (fun _ : Fin 1 ↦ ![1, 0, 0, 0]) := by
  funext k u
  simp only [bE, monomialFam, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, pow_one,
    pow_zero, mul_one]

/-- **GATE-3 GREEN — the terminal two-sided `hideal` for the corank-2 residual block.** On the open
region `V' ∋ 0`, BOTH `Chart.hideal` inclusions hold (in `monomialFam` form):
- `hideal_fwd` : `⟨(resid)∘gBlk⟩ ⊆ ⟨monomialFam [1,0,0,0]⟩` — forward divisibility, cofactor `q`.
- `hideal_bwd` : `⟨monomialFam [1,0,0,0]⟩ ⊆ ⟨(resid)∘gBlk⟩` — the REVERSE, cofactor the Bézout `r`
  (`= 1/unit`, a continuous unit). This is the reverse the gate measures — it closes cheaply. -/
theorem hideal_terminal_both :
    ∃ V' : Set (Fin 4 → ℝ),
      IsOpen V' ∧ (0 : Fin 4 → ℝ) ∈ V' ∧
      RegionRepresents (fun i ↦ resid i ∘ gBlk)
        (monomialFam (fun _ : Fin 1 ↦ ![1, 0, 0, 0])) V' ∧
      RegionRepresents (monomialFam (fun _ : Fin 1 ↦ ![1, 0, 0, 0]))
        (fun i ↦ resid i ∘ gBlk) V' := by
  obtain ⟨V', r, hopen, hzero, _, hP⟩ := principalInv_blk
  obtain ⟨hfwd, hbwd⟩ := principalInv_regionRepresents resid gBlk bE (fun i ↦ qBlk i 0) r V' hP
  rw [bE_eq_monomialFam] at hfwd hbwd
  exact ⟨V', hopen, hzero, hfwd, hbwd⟩

end DLNFibre.Core.Aoyagi.Corank2TerminalProto

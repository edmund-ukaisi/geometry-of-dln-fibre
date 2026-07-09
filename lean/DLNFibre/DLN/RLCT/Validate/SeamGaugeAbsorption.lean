import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# `DLNFibre.DLN.RLCT.Validate.SeamGaugeAbsorption` — the §2 seam GAUGE-ABSORPTION lemma

The one genuinely-new brick of the §2 sub-generic seam chart (expedition `aoyagi-full`, thread
`genm-seam`, discuss-at-close #80 §2). **Ext-free, no `Core` import** — pure `Matrix`/`Ring`
algebra.

## The setup (block-normalized corank-`q` point)

At a corank-`q` point of the product rank-drop locus, banked pivot/corner elimination puts each
layer map into block-normal form: a `q`-dimensional identity **thread** (present at *every* node
of the chain) plus the **shifted complement** `Ĉ_s`. In coordinates the layer is
`blockLayer Ĉ s = fromBlocks 1 0 0 (Ĉ s) : Matrix (r ⊕ m s) (r ⊕ m (s+1))`, where the thread index
type `r` is constant along the chain and the complement width `m i` varies per node.

The end-to-end base change acts on the chain by `A_s ↦ g_s⁻¹ A_s g_{s+1}` (conjugating the product,
endpoints free); its first-order (Lie-algebra) linearization at the base point `g_i = 1 + εξ_i` is

  `gaugeDeform Ĉ ξ s = blockLayer Ĉ s * ξ (s+1) - ξ s * blockLayer Ĉ s`.

Writing `ξ_i = fromBlocks α_i β_i γ_i δ_i` in thread ⊕ complement blocks, the four blocks of the
deformation are (see `gaugeDeform_block`, with `δ_i := 0`):

  * **TL (thread)** `= α_{s+1} - α_s`,
  * **TR (thread → complement)** `= β_{s+1} - β_s Ĉ_s`,
  * **BL (complement → thread)** `= Ĉ_s γ_{s+1} - γ_s`,
  * **BR (shifted complement)** `= Ĉ_s δ_{s+1} - δ_s Ĉ_s`.

## The lemma (`gaugeAbsorption`)

**Every** first-order deformation of the thread block (TL) and the two thread↔complement
cross-blocks (TR, BL) lies in the image of the linearized base-change action: for arbitrary targets
`tTL, tTR, tBL` there is a node-indexed gauge deformation `ξ` (with `δ = 0`) realizing all three
(`gaugeAbsorption`). The remaining BR block — the shifted complement `Ĉ` — is left free: it is the
**normal** direction, matching the seam chart's "shifted-chain entries are the normals".

The proof is the promised FORWARD/BACKWARD triangular solve along the chain (the concrete content of
"`M_{0N}` is projective + injective", proved directly, no `Ext`):

  * `gaugeAlpha` (TL): forward accumulate the differences, `α 0 = 0`, `α (i+1) = α i + tTL i`;
  * `gaugeBeta`  (TR): forward accumulate with the `Ĉ` twist, `β (i+1) = tTR i + β i Ĉ i`;
  * `gaugeGamma` (BL): BACKWARD accumulate with the `Ĉ` twist from the sink, `γ L = 0`,
    `γ_s = Ĉ_s γ_{s+1} - tBL_s` (built by a fuel `= L - s` countdown, `gaugeGammaFuel`).

No inverse is ever taken (the three telescopes are exact); the thread's presence at every node
is what lets the accumulators never fall off an end. This is genre-identical to the banked
`psiSplitRawGen` forward/backward chain accumulator (D1).
-/

open Matrix

namespace DLNFibre.DLN.RLCT.SeamGauge

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {α : Type*} [Ring α]
variable {m : ℕ → Type*} [∀ i, Fintype (m i)]

/-! ## Block-matrix subtraction helper -/

/-- Block subtraction: the difference of two block matrices is the blockwise difference. Mirrors
Mathlib's `Matrix.fromBlocks_add`. -/
theorem fromBlocks_sub {n o l p : Type*}
    (A A' : Matrix n l α) (B B' : Matrix n p α) (C C' : Matrix o l α) (D D' : Matrix o p α) :
    fromBlocks A B C D - fromBlocks A' B' C' D'
      = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j; rcases i with ⟨⟩ <;> rcases j with ⟨⟩ <;> rfl

/-! ## The three chain accumulators -/

/-- **TL accumulator** (thread block, forward). `α 0 = 0`, `α (i+1) = α i + tTL i`; the forward
difference telescope solving `α_{s+1} - α_s = tTL_s`. -/
def gaugeAlpha (tTL : ℕ → Matrix r r α) : ℕ → Matrix r r α
  | 0 => 0
  | i + 1 => gaugeAlpha tTL i + tTL i

/-- **TR accumulator** (thread → complement, forward). `β 0 = 0`,
`β (i+1) = tTR i + β i Ĉ i`; solves `β_{s+1} - β_s Ĉ_s = tTR_s`. -/
def gaugeBeta (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (tTR : (s : ℕ) → Matrix r (m (s + 1)) α) : (i : ℕ) → Matrix r (m i) α
  | 0 => 0
  | i + 1 => tTR i + gaugeBeta Chat tTR i * Chat i

/-- **BL accumulator, fuel countdown** (complement → thread, backward). At fuel `0` it is `0` (the
sink boundary `γ = 0`); at fuel `f+1` it prepends one twisted step `Ĉ_s · (next) - tBL_s`. -/
def gaugeGammaFuel (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (tBL : (s : ℕ) → Matrix (m s) r α) : (fuel : ℕ) → (s : ℕ) → Matrix (m s) r α
  | 0, _ => 0
  | fuel + 1, s => Chat s * gaugeGammaFuel Chat tBL fuel (s + 1) - tBL s

/-- **BL accumulator** (complement → thread, backward). `γ_s := gaugeGammaFuel (L - s) s`, so
`γ L = 0` and, for `s < L`, `Ĉ_s γ_{s+1} - γ_s = tBL_s` (`gaugeGamma_rec`). -/
def gaugeGamma (L : ℕ) (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (tBL : (s : ℕ) → Matrix (m s) r α) (s : ℕ) : Matrix (m s) r α :=
  gaugeGammaFuel Chat tBL (L - s) s

/-! ## The accumulator recurrences -/

/-- The forward TL telescope: `α_{s+1} - α_s = tTL_s`. -/
theorem gaugeAlpha_succ_sub (tTL : ℕ → Matrix r r α) (s : ℕ) :
    gaugeAlpha tTL (s + 1) - gaugeAlpha tTL s = tTL s := by
  simp only [gaugeAlpha]; abel

/-- The forward TR telescope: `β_{s+1} - β_s Ĉ_s = tTR_s`. -/
theorem gaugeBeta_succ_sub (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (tTR : (s : ℕ) → Matrix r (m (s + 1)) α) (s : ℕ) :
    gaugeBeta Chat tTR (s + 1) - gaugeBeta Chat tTR s * Chat s = tTR s := by
  simp only [gaugeBeta]; abel

/-- The backward BL telescope: for `s < L`, `Ĉ_s γ_{s+1} - γ_s = tBL_s`. -/
theorem gaugeGamma_rec (L : ℕ) (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (tBL : (s : ℕ) → Matrix (m s) r α) (s : ℕ) (hs : s < L) :
    Chat s * gaugeGamma L Chat tBL (s + 1) - gaugeGamma L Chat tBL s = tBL s := by
  have hfuel : L - s = (L - (s + 1)) + 1 := by omega
  simp only [gaugeGamma]
  rw [hfuel]
  simp only [gaugeGammaFuel]
  abel

/-! ## The linearized base-change deformation and its blocks -/

/-- The block-normal layer map `fromBlocks 1 0 0 (Ĉ s)` — a `q`-dim identity thread ⊕ shifted
complement `Ĉ s`. -/
def blockLayer (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α) (s : ℕ) :
    Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α :=
  fromBlocks (1 : Matrix r r α) 0 0 (Chat s)

/-- The linearized base-change deformation of layer `s`:
`gaugeDeform Ĉ ξ s = blockLayer Ĉ s * ξ (s+1) - ξ s * blockLayer Ĉ s`. -/
def gaugeDeform (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (xi : (i : ℕ) → Matrix (r ⊕ m i) (r ⊕ m i) α) (s : ℕ) :
    Matrix (r ⊕ m s) (r ⊕ m (s + 1)) α :=
  blockLayer Chat s * xi (s + 1) - xi s * blockLayer Chat s

/-- The gauge witness: `ξ_i = fromBlocks α_i β_i γ_i 0`, the three accumulators in thread ⊕
complement block form with the complement block (`δ`) set to `0`. -/
def gaugeXi (L : ℕ) (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (tTL : ℕ → Matrix r r α) (tTR : (s : ℕ) → Matrix r (m (s + 1)) α)
    (tBL : (s : ℕ) → Matrix (m s) r α) (i : ℕ) : Matrix (r ⊕ m i) (r ⊕ m i) α :=
  fromBlocks (gaugeAlpha tTL i) (gaugeBeta Chat tTR i) (gaugeGamma L Chat tBL i) 0

/-- The four blocks of the linearized base-change deformation on the witness `gaugeXi`: TL, TR, BL
are the three accumulator differences; BR is `0` (the `δ = 0` choice). Pure block algebra
(`fromBlocks_multiply` + `fromBlocks_sub`), no target constraint. -/
theorem gaugeDeform_block (L : ℕ) (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (tTL : ℕ → Matrix r r α) (tTR : (s : ℕ) → Matrix r (m (s + 1)) α)
    (tBL : (s : ℕ) → Matrix (m s) r α) (s : ℕ) :
    gaugeDeform Chat (gaugeXi L Chat tTL tTR tBL) s
      = fromBlocks
          (gaugeAlpha tTL (s + 1) - gaugeAlpha tTL s)
          (gaugeBeta Chat tTR (s + 1) - gaugeBeta Chat tTR s * Chat s)
          (Chat s * gaugeGamma L Chat tBL (s + 1) - gaugeGamma L Chat tBL s)
          0 := by
  simp only [gaugeDeform, gaugeXi, blockLayer, fromBlocks_multiply, fromBlocks_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, sub_zero]

/-! ## The gauge-absorption lemma -/

/-- **Gauge-absorption (§2 seam crux).** At a block-normalized corank-`q` point, every first-order
deformation of the thread block and the two thread↔complement cross-blocks lies in the image of the
linearized base-change action: for arbitrary targets `tTL` (thread), `tTR` (thread → complement) and
`tBL` (complement → thread), there is a node-indexed gauge deformation `ξ` whose induced chain
deformation `gaugeDeform` matches all three on every layer `s < L`. The remaining BR block (the
shifted complement `Ĉ`) is unconstrained — it is the normal direction of the seam chart.

Proved by the exact forward/backward triangular solves `gaugeAlpha`/`gaugeBeta` (forward from the
source) and `gaugeGamma` (backward from the sink); no inverse is taken. -/
theorem gaugeAbsorption (L : ℕ) (Chat : (s : ℕ) → Matrix (m s) (m (s + 1)) α)
    (tTL : ℕ → Matrix r r α) (tTR : (s : ℕ) → Matrix r (m (s + 1)) α)
    (tBL : (s : ℕ) → Matrix (m s) r α) :
    ∃ xi : (i : ℕ) → Matrix (r ⊕ m i) (r ⊕ m i) α,
      ∀ s : ℕ, s < L →
        (gaugeDeform Chat xi s).toBlocks₁₁ = tTL s ∧
        (gaugeDeform Chat xi s).toBlocks₁₂ = tTR s ∧
        (gaugeDeform Chat xi s).toBlocks₂₁ = tBL s := by
  refine ⟨gaugeXi L Chat tTL tTR tBL, fun s hs => ?_⟩
  rw [gaugeDeform_block]
  refine ⟨?_, ?_, ?_⟩
  · rw [toBlocks_fromBlocks₁₁]; exact gaugeAlpha_succ_sub tTL s
  · rw [toBlocks_fromBlocks₁₂]; exact gaugeBeta_succ_sub Chat tTR s
  · rw [toBlocks_fromBlocks₂₁]; exact gaugeGamma_rec L Chat tBL s hs

end

end DLNFibre.DLN.RLCT.SeamGauge

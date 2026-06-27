import DLNFibre.DLN.RLCT.Validate.RouteMAchieverTelescope
import DLNFibre.DLN.RLCT.Validate.RouteMChainFactor

/-!
# `RouteMFactoredChain` — the factored-data → `Chain` builder (general-`M` achiever)

The cert's per-boundary block data is naturally in the `step_of_factor` shape: a compressed transition
`C_s = B_s · Q_s + u·R̄_s`, a unit-triangular chaining `Q_s · A_s = C_{s+1}`, the radial-error
`E_s = R̄_s · A_s` (`RouteMChainFactor`). This module packages that data as a structure `FactoredChain`
and PRODUCES the abstract telescope's `Chain` (`RouteMAchieverTelescope.Chain`), discharging `step` (via
`step_of_factor`) and `base` once, M-agnostically.

The per-`M` achiever construction supplies a `FactoredChain` (the block matrices + the two per-level
identities `hC`, `hQA`); `toChain` hands back a `Chain` whose `chain_telescope_zero` + the suffix bridge
(`RouteMSuffixBridge`) deliver `prod M (φ_M u) = u • H` — the chart identity's rate factor. The genuine
remaining work is the block-matrix SUPPLY (`hC`/`hQA` per level); the telescope wiring is closed here.

* `FactoredChain` — the factored per-level data (widths, `A`/`C`/`B`/`Qmat`/`Rmat`, `hC`, `hQA`, `base`).
* `FactoredChain.toChain` — the produced `Chain` (`E_k := Rmat k · A k`, `step` by `step_of_factor`).
* `FactoredChain.telescope_zero` — the consumer form: `C 0 · suffix 0 = u • Hmat 0`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-- **The factored per-level data** for the general achiever chain. Widths `Wwid k` (ambient `= M k`),
`Twid k` (compressed). Per level: the layer `A k`, the compressed transition `C k`, the kept part
`Bmat k` (`= P_k K_k`), the chaining row `Qmat k` (`= Q_k`), and the residual block `Rmat k` (`= R̄_k`).
The two per-level identities are the cert's: `hC` (`C_k = B_k · Q_k + u·R̄_k`) and `hQA` (`Q_k · A_k =
C_{k+1}`); `base` is the terminal `C_n = u • R`. -/
structure FactoredChain (n : ℕ) {𝕜 : Type*} [CommRing 𝕜] (u : 𝕜) where
  /-- Ambient widths (`= M k`). -/
  Wwid : ℕ → ℕ
  /-- Compressed (kept-rank) widths. -/
  Twid : ℕ → ℕ
  /-- The layer matrices `A_k`. -/
  A : (k : ℕ) → Matrix (Fin (Wwid k)) (Fin (Wwid (k + 1))) 𝕜
  /-- The compressed transitions `C_k`. -/
  C : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Wwid k)) 𝕜
  /-- The kept part `B_k = P_k K_k`. -/
  Bmat : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Twid (k + 1))) 𝕜
  /-- The chaining row `Q_k` (`Q_k A_k = C_{k+1}`). -/
  Qmat : (k : ℕ) → Matrix (Fin (Twid (k + 1))) (Fin (Wwid k)) 𝕜
  /-- The residual block `R̄_k` (the `u`-carrying part of `C_k`). -/
  Rmat : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Wwid k)) 𝕜
  /-- The terminal residual `R`. -/
  R : Matrix (Fin (Twid n)) (Fin (Wwid n)) 𝕜
  /-- **The compressed-transition identity**: `C_k = B_k · Q_k + u • R̄_k`, for `k < n`. -/
  hC : ∀ k, k < n → C k = Bmat k * Qmat k + u • Rmat k
  /-- **The chaining identity**: `Q_k · A_k = C_{k+1}`, for `k < n`. -/
  hQA : ∀ k, k < n → Qmat k * A k = C (k + 1)
  /-- **The terminal condition**: `C_n = u • R`. -/
  base : C n = u • R

namespace FactoredChain

variable {n : ℕ} {𝕜 : Type*} [CommRing 𝕜] {u : 𝕜}

/-- **The produced `Chain`.** `E_k := R̄_k · A_k`; `step` is `step_of_factor` (from `hC`, `hQA`, the
`E_k` def); `base` is carried over. The telescope's `chain_telescope_zero` then fires. -/
def toChain (c : FactoredChain n u) : Chain n u where
  Wwid := c.Wwid
  Twid := c.Twid
  A := c.A
  C := c.C
  B := c.Bmat
  E := fun k => c.Rmat k * c.A k
  R := c.R
  step := by
    intro k hk
    exact step_of_factor u (c.C k) (c.A k) (c.Bmat k) (c.Qmat k) (c.Rmat k) (c.C (k + 1))
      (c.Rmat k * c.A k) (c.hC k hk) (c.hQA k hk) rfl
  base := c.base

@[simp] theorem toChain_Wwid (c : FactoredChain n u) : c.toChain.Wwid = c.Wwid := rfl
@[simp] theorem toChain_C (c : FactoredChain n u) : c.toChain.C = c.C := rfl
@[simp] theorem toChain_A (c : FactoredChain n u) : c.toChain.A = c.A := rfl

/-- **The full-product divisibility** (the chart identity's rate consumer). `C_0 · suffix_0 = u • Hmat_0`
for the produced chain. With `C_0 = 1` this reads `suffix_0 = u • Hmat_0`, the `prod = u•H` shape the
suffix bridge turns into `prod M A = u • H`. -/
theorem telescope_zero (c : FactoredChain n u) :
    c.toChain.C 0 * c.toChain.suffix 0 (Nat.zero_le n) = u • c.toChain.Hmat 0 (Nat.zero_le n) :=
  c.toChain.chain_telescope_zero

end FactoredChain

end DLNFibre.DLN.RLCT

import DLNFibre.Core.EndBaseChangeSweep
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.FibreHeightDirect
import DLNFibre.Core.NullstellensatzCodim

/-!
# `DLNFibre.Core.FibreCodimSweepAssembly` — the route-c assembly `codim F = C + δ` (conditional)

The downstream assembly of the homogeneous-sweep route (thread 27's certificate): from the **sweep
dimension identity** (the one isolated hard rung) and the **reducible catenary** for the fibre, the
fibre codimension is `C + δ`. Both inputs are carried as **explicit named hypotheses** (the
conditional-bank pattern, as for `FibreReducedTrivialization`'s `e`): they are *certified true*
(thread 25/27, exact Singular + sympy on 13/9 cases), and everything *around* them — the `ℕ∞`
arithmetic chaining them, through the LANDED `codim Σ̄^r = C` (`SigmaCodim`) and the H1 retarget —
is machine-checked.

The two named inputs, for a rank-`r` target `B` (`E` the normal form; via G1 any rank-`r` `B`):

* **`hSweepDim`** — `varietyDim (fibre d B) = card − C − δ`. This is thread 27's Step-D fibre dimension,
  bundling the **sweep** `dim Σ^r = δ + dim F` (Step B, the genuinely hard orbit-dimension rung) + the
  **closure** `dim Σ^r = dim Σ̄^r` (Step C, the Cited LR 4.4/4.5 density) + the LANDED `dim Σ̄^r = card −
  C`. It is the single named dimension identity the `+ δ` is isolated to.
* **`hFcat`** — `codimRepCanonical (fibre d B) + varietyDim (fibre d B) = card`. The **reducible
  catenary** for the (reducible) fibre: geometric codimension `+` variety dimension `=` ambient. True
  for any subset of affine space over a field (each irreducible component is catenary; `codim = min`,
  `dim = max`, dual under the per-prime catenary) — a *soft* bookkeeping fact, named here rather than
  ground out (the engine's catenary `codimRep_add_varietyDim_eq_card` is stated only for the
  *irreducible* case).

When the sweep tide discharges `hSweepDim` (or the reducible catenary `hFcat` is proved as the general
bedrock it is), this assembly closes `codim(fibre B) = C + δ` unconditionally. Nothing here claims the
identity outright; `DLN.BundleShiftInterface.cited_bundle_shift` stays Cited until both inputs land.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **Route-c assembly (conditional): `codim(fibre B) = C + δ`.** From the named sweep dimension
`hSweepDim : varietyDim (fibre d B) = card − C − δ` and the reducible catenary `hFcat :
codimRepCanonical (fibre d B) + varietyDim (fibre d B) = card`, the fibre codimension is `C + δ`. Pure
`ℕ∞` arithmetic: substitute `hSweepDim` into `hFcat` and cancel the `card − C − δ` summand (lossless,
`C + δ ≤ card`). The two hypotheses are certified true (thread 25/27); this is the machine-checked
chaining. -/
theorem codimRepCanonical_fibre_eq_of_sweepDim_of_catenary
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (v : ℕ∞)
    (hCδ : v ≤ (Nat.card (RepCoord d) : ℕ∞))
    (hSweepDim : varietyDim (canonicalCoord d '' fibre d B)
      = (Nat.card (RepCoord d) : ℕ∞) - v)
    (hFcat : codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B)
      = (Nat.card (RepCoord d) : ℕ∞)) :
    codimRepCanonical (fibre d B) = v := by
  rw [hSweepDim] at hFcat
  -- `codim + (card − v) = card`, with `v ≤ card` ⟹ `codim = v` (ℕ∞, lossless).
  have hcard_ne : (Nat.card (RepCoord d) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
  -- `card − v` is finite (≤ card < ⊤); cancel it.
  have hsub_ne : (Nat.card (RepCoord d) : ℕ∞) - v ≠ ⊤ :=
    ne_top_of_le_ne_top hcard_ne tsub_le_self
  -- `codim = card − (card − v) = v` (lossless, `card − v ≤ card`, `v ≤ card`).
  have hstep : codimRepCanonical (fibre d B)
      = (Nat.card (RepCoord d) : ℕ∞) - ((Nat.card (RepCoord d) : ℕ∞) - v) :=
    (ENat.addLECancellable_of_ne_top hsub_ne).eq_tsub_of_add_eq hFcat
  rw [hstep, ENat.sub_sub_cancel hcard_ne hCδ]

end DLNFibre.Core

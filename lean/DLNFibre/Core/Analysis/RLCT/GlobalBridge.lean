import DLNFibre.Core.Analysis.RLCT.Local
import DLNFibre.Core.Analysis.RLCT.Global

/-!
# `RLCT.GlobalBridge` — B1: the polymorphic-global `rlctAt` equals the zeta-side `rlctAt`

The global-RLCT theory (`RLCT.Global`) redefines `negPow`, `localAdmissibleExponents`, `rlctAt`
**polymorphically** over an arbitrary parameter space `X`, so that `rlctGlobal` applies to the DLN
loss `Rep_d → ℝ`. The local zeta theory (`RLCT.Local`) fixes these to `X = Fin n → ℝ` (for the
archimedean-zeta continuation cite). The two are stated in separate namespaces to avoid a clash.

**B1 (the fork-closing bridge).** Specialised to `X = Fin n → ℝ`, the two are the **same object**:
`RLCT.Global.rlctAt K x = RLCT.rlctAt K x`. The negative powers, admissible sets, and suprema are
term-identical (both `fun x ↦ (K x)^(-c)` / `{c | 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x)}` /
`sSup`), so the bridge is definitional (`rfl`). Stated as a named lemma regardless, so a later
refactor that de-syncs the two definitions is caught here.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Filter Topology

namespace RLCT

variable {n : ℕ}

/-- The polymorphic-global `negPow` at `X = Fin n → ℝ` **is** the zeta-side `negPow` (both are
`fun x ↦ (K x)^(-c)`). -/
lemma global_negPow_eq (K : (Fin n → ℝ) → ℝ) (c : ℝ) :
    RLCT.Global.negPow K c = RLCT.negPow K c := rfl

/-- The polymorphic-global `localAdmissibleExponents` at `X = Fin n → ℝ` **is** the zeta-side one
(both `{c | 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x)}`). -/
lemma global_localAdmissibleExponents_eq (K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    RLCT.Global.localAdmissibleExponents K x = RLCT.localAdmissibleExponents K x := rfl

/-- **B1 — the fork-closing bridge: `RLCT.Global.rlctAt K x = RLCT.rlctAt K x`.** The polymorphic
global-side local RLCT, specialised to the zeta type `Fin n → ℝ`, equals the zeta-side local RLCT.
Definitional: the two admissible sets and their suprema coincide term-for-term. This closes the
"two `rlctAt`s" fork — any result stated with one applies to the other. -/
theorem global_rlctAt_eq (K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    RLCT.Global.rlctAt K x = RLCT.rlctAt K x := rfl

end RLCT

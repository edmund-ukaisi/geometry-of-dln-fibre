import DLNFibre.Core.Aoyagi.OrderCount
import DLNFibre.Core.Aoyagi.OrderChain
import DLNFibre.DLN.RLCT.Foundations.Lambda
import DLNFibre.DLN.Aoyagi.ClosedForm

/-!
# `DLN.Aoyagi.OrderBinding` — Object E / P6, Tier 2: the θ-attachment (arithmetic binding)

**Tier 2** of the E-lane three-tier split (elder-ratified 2026-07-21): the thin DLN binding that
attaches the landed closed-form value `aoyagiTheta` (`Foundations.Lambda`) to the Tier-1 abstract
banded-interval count `bandCount` (`Core.Aoyagi.OrderCount`), and instantiates it at the **certified
Def-3 selector objects** `ell` / `residueA` (`Aoyagi.ClosedForm`) — pin (a): certified objects,
never free naturals.

Everything here is an **arithmetic identity between two in-tree values** — both `bandCount ℓ a` and
`aoyagiTheta ℓ a` are `a(ℓ−a)+1`, unconditionally. So the bindings are stable under any outcome of
the P6.2 pen-and-paper adjudication (task #39: what the count *means* — the RLCT/zeta-pole
multiplicity `ρ`, elder's max-crossing-number hypothesis, worked.tex:182).

## Name/scope discipline (K3, elder-pinned)

The θ-name enters here (Tier 2), attached to the landed `aoyagiTheta` VALUE. The **interpretive**
claim — that `thetaCount` IS Aoyagi's RLCT/zeta-pole multiplicity `ρ` (the number of top-dimensional
components of the exceptional fibre) — is **NOT made** in any name or docstring here; it is DEFERRED
to P6.2 (pnp-gated) and, for the analytic pole order, is monument-class (needs meromorphic
continuation Mathlib lacks). This module claims only: `thetaCount = aoyagiTheta`, a value identity.
-/

open DLNFibre.Core.Aoyagi.OrderCount DLNFibre.Core.Aoyagi.OrderChain DLNFibre.DLN.RLCT

namespace DLNFibre.DLN.Aoyagi

/-- **The θ-attachment.** The Tier-1 banded-interval count equals the landed closed-form value
`aoyagiTheta` — both are `a(ℓ−a)+1`, unconditionally. This is where the θ-name enters the E-lane
(Tier 1 stays name-neutral). -/
theorem bandCount_eq_aoyagiTheta (ℓ a : ℕ) : bandCount ℓ a = aoyagiTheta ℓ a := by
  simp only [bandCount_eq, aoyagiTheta]

/-- **The θ-attachment for the FAITHFUL count (P6.2).** The `Set.chainHeight` of the
binding-minimiser box poset (the pnp-confirmed max-chain object, `Core.Aoyagi.OrderChain`) equals
the landed `aoyagiTheta` value — both `a(ℓ−a)+1`, unconditionally. Ties the chain-height count to θ;
the
interpretive identification with the analytic pole multiplicity `ρ` remains the deferred monument
seam (meromorphic continuation, Mathlib-absent). -/
theorem chainHeight_boxPart_eq_aoyagiTheta (ℓ a : ℕ) :
    (BoxPart ℓ a).chainHeight (· < ·) = ((aoyagiTheta ℓ a : ℕ) : ℕ∞) := by
  rw [chainHeight_boxPart]; simp only [aoyagiTheta]

variable {N : ℕ}

/-- The banded-interval count at the **certified Def-3 selector objects** `(ell d r, residueA d r)`
(pin (a): certified `ClosedForm` objects, not free naturals). `residueA` is `ℤ`-valued and lies in
`[0, ell]` (it is a residue), so `.toNat` is faithful. NOT named/claimed as the multiplicity `ρ` —
that identification is P6.2 (deferred). -/
noncomputable def thetaCount (d : Fin (N + 1) → ℕ) (r : ℕ) : ℕ :=
  bandCount (ell d r) (residueA d r).toNat

/-- **Certified instantiation** (pin (a)): the banded count at the certified selector objects equals
the landed `aoyagiTheta` there. Immediate from the unconditional `bandCount_eq_aoyagiTheta` (no
`residueA ≤ ell` bound needed — the value identity holds for all naturals). -/
theorem thetaCount_eq_aoyagiTheta (d : Fin (N + 1) → ℕ) (r : ℕ) :
    thetaCount d r = aoyagiTheta (ell d r) (residueA d r).toNat :=
  bandCount_eq_aoyagiTheta _ _

/-! ## K1 ground-truth gates (build-enforced; computable `aoyagiTheta` at the certified `(ℓ,a)`)

The certified selectors `ell`/`residueA` are `noncomputable`, so these gate the θ-VALUES at the
Def-3 `(ℓ, a)` of each width vector (RRR table, `verify-repro-s4s5.md`); `thetaCount_eq_aoyagiTheta`
links `thetaCount` to them. Through-the-selector value gates (`thetaCount ![2,2,2] 0 = 1`) need
`ell`/`residueA` instance lemmas — flagged for a follow-on, not built here. -/

-- (2,2,2) → (ℓ,a) = (2,2);  (3,3,4) → (ℓ,a) = (2,2)  [both ρ = 1]
example : aoyagiTheta 2 2 = 1 := by decide
-- (2,1,2) → (ℓ,a) = (2,1)  [ρ = 2]
example : aoyagiTheta 2 1 = 2 := by decide
-- (2,2,2,2) → (ℓ,a) = (3,2)  [ρ = 3]
example : aoyagiTheta 3 2 = 3 := by decide
-- the θ-attachment at each K1 (ℓ,a): bandCount agrees with the closed form
example : bandCount 2 2 = aoyagiTheta 2 2 := bandCount_eq_aoyagiTheta 2 2
example : bandCount 2 1 = aoyagiTheta 2 1 := bandCount_eq_aoyagiTheta 2 1
example : bandCount 3 2 = aoyagiTheta 3 2 := bandCount_eq_aoyagiTheta 3 2

end DLNFibre.DLN.Aoyagi

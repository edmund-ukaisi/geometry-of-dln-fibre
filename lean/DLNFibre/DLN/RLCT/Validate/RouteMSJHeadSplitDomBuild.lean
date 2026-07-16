import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore

set_option linter.style.longLine false

/-!
# `RouteMSJHeadSplitDomBuild` — Brick D (route β): the head-split domination, structured decomposition

**Thread `genm-brickd` (aoyagi-full Stage 2).** Builds `headSplit_domination` (the single remaining `(□)`
sorry of the interior deeper-cut descent, `RouteMSJDeeperFlagCore:550`) as `headSplit_domination_impl`,
via satred's `brickD-pin.md` 6-step decomposition (S-a..S-f) + the two C-integral arms of
`brickD-sublemmas.md` (a<u `corner_C_shift_disposal` / a≥u `corner_C_shift_gammaAtom` on the PIVOT Gram).
The assembly is proven from correctly-typed sub-lemma `sorry`s; each leaf is filled in turn.

## Corrected stub signature (controller-sanctioned, 2026-07-16)

Two hypotheses ADDED vs the canonical `headSplit_domination` stub (both precision fixes; arch1build will
amend the stub + `deeperFlag_spineToCore`/`deeperFlag_shell_le` ripple + wire `headSplit_domination := impl`):
* **`hε'le : ε' ≤ ε/√(M₁M₂)`** — the stub over-generalized `ε'`; the domination is FALSE for large `ε'`
  (the shell⊆good containment `hagree` fires only at the rescaled floor). Holds by `rfl` at the
  `deeperFlag_spineToCore` call site (it sets `ε' = ε/√(M₁M₂)`).
* **`ha1 : 1 ≤ M 0 − (t+j)` (`a ≥ 1`)** — excludes the `a=0` saturated case (satred's 3-descent design routes
  it to `deeperFlag_waist`, a SEPARATE base case). Brick D = the interior corank route.
`0 ≤ c'` is discharged INTERNALLY (the trivial regime outside `ab/2 < c' < carrierThreshold`).

## Route (β — controller/satred `brickD-sublemmas`, NOT the draft's codim-u·ρ bare constant)

S-a row-split · S-b head-split (`Q_b = A_cor·Zf`) · S-c P-radial blow-up (`decLoss` + monomial) · S-d
`B₁₂→Γ'` shear · S-e C-integral → `C_hle < ⊤` via the a<u/a≥u arms (pivot Gram to the reduced-chain IH via
`qbox`) · S-f assemble. Harvests the route-INDEPENDENT pieces from the draft `RouteMSJHeadSplitDom`
(`hsSplit` MP-equiv, `hsSplit_good_of_shell`, `hsQ`) once confirmed.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **Brick D (route β): the head-split domination with a FINITE reorganization constant.** The corrected
stub signature (adds `hε'le` + the `a≥1` guard `ha1`; `0 ≤ c'` discharged internally). arch1build amends the
canonical `headSplit_domination` to match, then wires `headSplit_domination := headSplit_domination_impl`. -/
theorem headSplit_domination_impl (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (ha1 : 1 ≤ M 0 - (t + j))
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    (hcT : c' < carrierThreshold M)
    {ε' : ℝ} (hε' : 0 < ε') (hε'le : ε' ≤ ε / Real.sqrt ((M 1 : ℝ) * M 2))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (U_sf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (min (M 1) (M (Fin.last (L + 1 + 1))) - j)) ℝ)
    (hZfMeas : Measurable Zf) (hUsMeas : Measurable U_sf)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, (min (M 1) (M (Fin.last (L + 1 + 1))) - j) ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z) :
    ∃ (Ccrossf : Params (redChain (t + j) M)
          → Matrix (Fin (M 0 - (t + j))) (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
        (sΓf : Params (redChain (t + j) M)
          → Set (Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ))
        (C_hle : ℝ≥0∞),
      C_hle < ⊤
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C_hle * deeperFlagCoreIntegrand M (t + j) (![1] : Fin 1 → ℕ)
              (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) Zf Ccrossf sΓf c' := by
  sorry

end DLNFibre.DLN.RLCT

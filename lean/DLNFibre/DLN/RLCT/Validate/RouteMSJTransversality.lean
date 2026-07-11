import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJTransversality` — the A2 peel-closure invariant's arithmetic core

**Thread `genm-sj5-descent`, the A2 admissible-family peel-closure invariant (#144 / `transversality-recursion.md`).**
The `p=0` transversality that makes the decorated `(S,J)` recursion (`DecoratedDescent`, `RouteMSJDecoratedRec`)
peel-closed rests on ONE clean `minAdm`-arithmetic fact (cover's #144 (ii), "pure `minAdm` arithmetic,
banked-adjacent"): at a NONDEGENERATE binding cut `t` (`a = M₀−t ≥ 1`, `b = M₁−t ≥ 1`), the reduced-chain
threshold `C_u := minAdm (redChain u M)` jumps by at least `a+b−1`:

    C_t + (a + b − 1) ≤ C_{t+1}.

Geometrically (#144 §1): passing from cut `t` to `t+1` adds one pivot row, which on a top-dim component `X`
of the reduced zero-product locus must lie in `leftker(Z_deep)` — costing `r_X` equations — so
`C_{t+1} ≤ C_t + r_X`; combined with this convexity `a+b−1 ≤ C_{t+1}−C_t`, the deeper generic rank
`r_X ≥ a+b−1 ≥ b`, so the `b` free corank rows survive full-row-rank `b` and the collapsing directions do NOT
vanish (`p = ν_X(H₁) = 0`). This module lands the ARITHMETIC half (the convexity); the geometric incidence
`C_{t+1} ≤ C_t + r_X` and the rank conclusion `rank(A_cor·Z_deep) = b` are the remaining invariant pieces.

Consumes only the banked charge soundness `minAdm_le_peelCharge_add_redChain` (`RouteMSJDecoratedCharge`,
`0/171`) + the `peelCharge` def. Pure `ℕ` order algebra; no measure theory, no `monomial_rlct`. Untracked
(the A2 invariant is being co-audited with cover before wiring). Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The binding-cut convexity (raw form).** At a binding cut `t` (where `minAdm M = peelCharge M t +
minAdm (redChain t M)`) with `t+1` still legal (`t+1 ≤ min(M₀,M₁)`), the `t`-cut value is dominated by the
`(t+1)`-cut value: `peelCharge M t + C_t ≤ peelCharge M (t+1) + C_{t+1}`. Immediate: the LHS IS `minAdm M`
(binding), and `minAdm M ≤` any legal cut's value (`minAdm_le_peelCharge_add_redChain` at `t+1`). -/
theorem minAdm_binding_convexity_le (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht1 : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M)) :
    peelCharge M t + minAdm (redChain t M)
      ≤ peelCharge M (t + 1) + minAdm (redChain (t + 1) M) := by
  rw [← hbind]
  exact minAdm_le_peelCharge_add_redChain M (t + 1) ht1

/-- **The binding-cut convexity (`a+b−1` form, #144 (ii)).** At a NONDEGENERATE binding cut
(`a = M₀−t ≥ 1`, `b = M₁−t ≥ 1`, from `t+1 ≤ min(M₀,M₁)`), the reduced-chain threshold jumps by at least
`a+b−1`: `minAdm (redChain t M) + ((M₀−t) + (M₁−t) − 1) ≤ minAdm (redChain (t+1) M)`. This is the exact
`≥ a+b−1 ≥ b` the `p=0` transversality needs (the `b` corank rows survive full-row-rank `b`). From the raw
convexity `ab + C_t ≤ (a−1)(b−1) + C_{t+1}` and the `ℕ` identity `ab = (a−1)(b−1) + (a+b−1)` (`a,b ≥ 1`). -/
theorem minAdm_redChain_succ_ge (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht1 : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M)) :
    minAdm (redChain t M) + ((M 0 - t) + (M 1 - t) - 1) ≤ minAdm (redChain (t + 1) M) := by
  have hle := minAdm_binding_convexity_le M t ht1 hbind
  unfold peelCharge at hle
  obtain ⟨a, ha⟩ : ∃ a, M 0 - t = a + 1 := ⟨M 0 - t - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, M 1 - t = b + 1 := ⟨M 1 - t - 1, by omega⟩
  have ha1 : M 0 - (t + 1) = a := by omega
  have hb1 : M 1 - (t + 1) = b := by omega
  rw [ha, hb, ha1, hb1] at hle
  rw [ha, hb]
  have hexp : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
  rw [hexp] at hle
  omega

/-- **The `≥ b` corollary (the corank-width survival bound the `p=0` transversality consumes).** At a
nondegenerate binding cut, `minAdm (redChain t M) + (M₁ − t) ≤ minAdm (redChain (t+1) M)` — the jump
dominates the corank width `b = M₁−t` (since `a+b−1 ≥ b` as `a = M₀−t ≥ 1`). This is the form the deeper
generic rank `r_X ≥ b` reads off (`C_{t+1}−C_t ≥ b`), giving the `b` corank rows full-row-rank survival. -/
theorem minAdm_redChain_succ_ge_corankWidth (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht1 : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M)) :
    minAdm (redChain t M) + (M 1 - t) ≤ minAdm (redChain (t + 1) M) := by
  have h := minAdm_redChain_succ_ge M t ht1 hbind
  have ha : 1 ≤ M 0 - t := by omega
  omega

end DLNFibre.DLN.RLCT

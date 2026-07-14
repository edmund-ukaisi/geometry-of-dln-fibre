import DLNFibre.DLN.RLCT.Validate.RouteMSJTransversality
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJShellCharge` — T-charge, the flag-charge arithmetic

**Thread `genm-sj5` off-sector, T-Obl3b build tile #3 (`final-assembly-design-cert.md` §2, §5).** The
exact-`ℕ` charge arithmetic of the singular-value-shell stratification: at a binding cut `t★` (`a =
M₀−t★`, `b = M₁−t★`, `r = min(a,b)`), the flag charge on shell `j`

    C_j := (a−j)(b−j) + minAdm (redChain (t★+j) M)

dominates `minAdm M` for every `j ≤ r`, so the arity-`(L+1)` IH fires on every shell.

## The clean route (design §2, banked)

The design §2 telescopes the convexity `minAdm_redChain_succ_ge`; but the plain domination `C_j ≥
minAdm M` is DIRECTLY the banked cut-soundness `minAdm_le_peelCharge_add_redChain` at the deeper cut
`u = t★+j` — no telescoping. The freed corner `(a−j)(b−j) = (M₀−t★−j)(M₁−t★−j) = peelCharge M (t★+j)`
(`ℕ`-subtraction associativity) makes `C_j` literally the banked cut value `peelCharge M u + minAdm
(redChain u M) ≥ minAdm M`. The "IH fires" step — the shifted comparator exponent `e_j = c′ −
½·(a−j)(b−j)` sits strictly inside the reduced carrier range — is the banked `carrierThreshold_shift`
plus the strict step hypothesis `c′ < carrierThreshold M`.

`deeperCut_le` records that the shell index `j ≤ r = min(a,b)` keeps `t★+j ≤ min(M₀,M₁)` legal
(saturation `t★+r = min(M₀,M₁)`), so the charge fires at every shell down to the saturated one.

S2-FREE: banked `minAdm`/`carrierThreshold` arithmetic; no measure theory, no `monomial_rlct`. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The freed corner at the deeper cut `t★ + j` is `peelCharge M (t★+j)`.** `(a−j)(b−j) =
(M₀−t★−j)(M₁−t★−j) = peelCharge M (t★+j)` (`ℕ`-subtraction associativity). Makes the flag charge
`C_j = (a−j)(b−j) + minAdm (redChain (t★+j) M)` literally the banked cut value. -/
theorem freedCorner_eq_peelCharge (M : Fin (L + 1) → ℕ) (t j : ℕ) :
    (M 0 - t - j) * (M 1 - t - j) = peelCharge M (t + j) := by
  unfold peelCharge
  rw [Nat.sub_sub, Nat.sub_sub]

/-- **The deeper cut `t★ + j` stays legal for `j ≤ r = min(a,b)`.** With `t★ ≤ min(M₀,M₁)` and `j ≤
min(M₀−t★, M₁−t★)` (`j ≤ r`), `t★ + j ≤ min(M₀,M₁)` — the shell index never leaves the legal cut range;
saturation `j = r` is exactly `t★+r = min(M₀,M₁)`. -/
theorem deeperCut_le (M : Fin (L + 1) → ℕ) (t j : ℕ) (ht : t ≤ min (M 0) (M 1))
    (hj : j ≤ min (M 0 - t) (M 1 - t)) : t + j ≤ min (M 0) (M 1) := by
  simp only [le_min_iff] at *
  omega

/-- **The flag charge dominates `minAdm M` (T-charge, tile #3).** At any legal deeper cut `u = t★+j ≤
min(M₀,M₁)`, the flag charge `C_j = (a−j)(b−j) + minAdm (redChain (t★+j) M)` dominates `minAdm M`. This
is the banked cut-soundness `minAdm_le_peelCharge_add_redChain` read as `C_j ≥ minAdm M` (freed corner =
`peelCharge M (t★+j)`), tight at `j = 0` (the binding identity). -/
theorem flagCharge_ge (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (huj : t + j ≤ min (M 0) (M 1)) :
    minAdm M ≤ (M 0 - t - j) * (M 1 - t - j) + minAdm (redChain (t + j) M) := by
  rw [freedCorner_eq_peelCharge]
  exact minAdm_le_peelCharge_add_redChain M (t + j) huj

/-- **The flag charge fires the reduced IH (T-charge, tile #3).** Below the carrier threshold `c′ <
carrierThreshold M = ½·minAdm M`, at any legal deeper cut `u = t★+j ≤ min(M₀,M₁)` the SHIFTED comparator
exponent `e_j = c′ − ½·peelCharge M u` sits STRICTLY inside the reduced carrier range `carrierThreshold
(redChain u M) = ½·minAdm (redChain u M)`. Combines the banked `carrierThreshold_shift` (the `≤` shift)
with the strict step hypothesis `c′ < carrierThreshold M`. -/
theorem flagShift_lt_carrierThreshold (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : u ≤ min (M 0) (M 1)) {c' : ℝ} (hc' : c' < carrierThreshold M) :
    c' - (peelCharge M u : ℝ) / 2 < carrierThreshold (redChain u M) := by
  have hshift := carrierThreshold_shift M u hu
  linarith [hc', hshift]

/-- **The flag charge fires the reduced IH, freed-corner form.** As `flagShift_lt_carrierThreshold` but
with the freed corner written explicitly as `(a−j)(b−j) = (M₀−t★−j)(M₁−t★−j)` (the form the shell-`j`
peel produces): `c′ − ½·(a−j)(b−j) < carrierThreshold (redChain (t★+j) M)`. -/
theorem flagShift_freedCorner_lt_carrierThreshold (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (huj : t + j ≤ min (M 0) (M 1)) {c' : ℝ} (hc' : c' < carrierThreshold M) :
    c' - ((M 0 - t - j) * (M 1 - t - j) : ℕ) / 2 < carrierThreshold (redChain (t + j) M) := by
  rw [freedCorner_eq_peelCharge]
  exact flagShift_lt_carrierThreshold M (t + j) huj hc'

end DLNFibre.DLN.RLCT

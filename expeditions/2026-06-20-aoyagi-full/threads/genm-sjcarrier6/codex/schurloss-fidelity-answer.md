1. FAITHFUL The displayed `schurLoss` matches the banked RHS: the same shear `Qp + P⁻¹ * B₁₂ * Qb` appears in both Frobenius terms, and the second term includes `C * shear + Γ * Qb`. Assuming Lean’s usual left-associative parsing for `*`, `C * P⁻¹ * B₁₂` parses as `(C * P⁻¹) * B₁₂`, exactly like `C * ⅟P * B₁₂`.

2. FAITHFUL Under `hU : IsUnit P`, installing `haveI : Invertible P := hU.invertible` makes the ring inverse `⅟P` available, and the proof’s use of `invOf_eq_nonsing_inv` is precisely the needed bridge to `P⁻¹`. So within the theorem hypotheses, `nonsing_inv` should not differ from `⅟P`; its zero-on-nonunits behavior is irrelevant because `P` is assumed a unit.

3. FAITHFUL I do not see a green-but-wrong issue from the algebra shown: the block names line up, products are on the correct sides, and the corank block multiplies `Qb` after the cross term `C * shear`. The theorem is also not vacuous in the relevant sense; it assumes exactly the unit condition needed to compare `⅟P` and `P⁻¹`.

Overall verdict: FAITHFUL, assuming the cited Mathlib lemmas have the stated meanings.
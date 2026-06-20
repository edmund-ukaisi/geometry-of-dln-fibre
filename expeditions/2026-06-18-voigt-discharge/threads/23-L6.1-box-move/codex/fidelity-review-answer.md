1. **OK** `[Mathlib inference]`: `zeroLocus(vanishingIdeal(orbitSet U))` is the affine `k`-point Zariski closure operator; caveat is value-field=`k`, so this is not a scheme/base-changed `\bar k` closure statement.

2. **OK** `[Lean-definition check]`: `∀ t≠0, ∃P, P•U = F t` says `F t` is in `orbitSet U`; the direction matches the definition `orbitSet U = {canonicalCoord A | ∃P, P•U=A}`.

3. **OK** `[direct computation]`: `P1·[1;0]·1 = [1;0]`, and with `P1⁻¹=[[1,1/t],[0,1]]`, `[t]·[1,0]·P1⁻¹ = [t,1]`; non-vacuous for infinite fields and not same-orbit at `t=0`.

4. **OK** `[direct computation + standard type-A inference]`: upstairs has ranks `(1,1,1)`, downstairs `(1,1,0)`, so only `r02` drops; this is exactly `M_[0,2]⊕M_[1,1] ⇝ M_[0,1]⊕M_[1,2]`.

5. **CONCERN: representative/k-point strength only** `[statement-strength audit]`: the engine proves one representative point lies in the `k`-point closure of one orbit, not the full general box-move theorem, orbit(D) subset, rank-locus equality, or scheme/geometric closure.

OVERALL FIDELITY = PASS-WITH-NOTES; most important caveat: the closure is the `k`-point affine closure, so assume algebraically closed `k` or add base-change language for the paper’s geometric claim.
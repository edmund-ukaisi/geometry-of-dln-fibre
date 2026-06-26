1. **Verdict: yes, there is a simpler outer reduction, but it is not “integrate `A0` first”; it is a 9-chart radial blow-up of `A0`, then one Schur shear.**

For a pivot entry of `A0`, permute rows/columns so it is `(0,0)`. On the chart `|A0₀₀| = max |A0ᵢⱼ|`, write

```text
A0 = a · R,
R = [ 1   β
      γ   Δ + γβ ],
```

where `β : 1×2`, `γ : 2×1`, `Δ : 2×2`, and the ratios are bounded. The radial map has Jacobian `|a|^8`.

Write `A1 = [ y ; S ]` with `y : 1×4`, `S : 2×4`, and shear

```text
T = y + βS        (Jacobian 1).
```

Then

```text
R A1 = [ T
         γT + ΔS ]
      = L_γ · [ T ; ΔS ].
```

Since `γ` is bounded on the chart, `L_γ` and `L_γ⁻¹` are uniformly bounded, hence

```text
frobSq(A0 A1)
= a² · frobSq(R A1)
≥ C · a² · (‖T‖² + frobSq(ΔS)).
```

Thus the chart contribution is bounded by

```text
∫ |a|^(8 - 2c') da · ∫ (‖T‖² + frobSq(ΔS))^(−c') dT dS dΔ,
```

up to bounded spectator factors. The `a`-integral is finite for `c' < 9/2`, hence for `c' < 4`; the remaining integral is exactly `resolved334_lt_top`, after a harmless scaled-box lemma.

2. **Verdict: yes, a non-measure-preserving Jacobian-weighted cover is genuinely forced; pure fibre/MP transport will not reach `c' < 4`.**

The pure fibre bound over fixed `A1` sees the linear map `A0 ↦ A0A1`. If `rank A1 = r`, its effective rank is `3r`, giving the fibre threshold `3r/2`; near rank `1` this caps at `3/2`. That is the obstruction you stated.

A global measure-preserving reparametrization to the resolved form is not a plausible route: the rank of the fibre map jumps along determinantal strata, while the resolved form separates this by an exceptional radial variable. A diffeomorphic MP change cannot create the missing divisor weight. The radial `A0 = aR` chart contributes exactly the needed `|a|^8` divisor; that is the measure-theoretic compensation for projectivising the rank direction.

3. **Verdict: choose a pruned version of (a): 9-entry `A0` argmax radial charts, but no inner recursion.**

Ranking by Lean risk:

```text
(a-lite) 9 A0 radial charts + Schur shear + resolved334: 35–55 lemmas, viable.
(b) A1 rank-2 minor cover: 60–90 lemmas, risky; likely not 6 charts but up to 18 minor choices.
(a-full) full r² atlas + recStep recursion: 80–120 lemmas, viable but overbuilds now.
(c) integrate-A0-first fibre + residual blow-up: 70–110 lemmas, conceptually brittle.
```

I would not key the main proof on `A1` rank-2 minors. It lands naturally in an `A1`-stratified normal form, not immediately in the banked `T ⊕ ΔS` form, so you would spend the savings rebuilding comparability and rank-local pseudoinverse bounds.

The cheapest chart is the `A0` radial chart above. The nine charts cover `A0 ≠ 0`; the slice `A0 = 0` is null. Ties are harmless: use finite subadditivity, not a disjoint partition.

4. **Verdict: expect one hard Lean step: the radial chart change-of-variables on max-entry cells.**

The algebraic heart is short:

```text
A0 = a [1 β; γ Δ+γβ],
A1 = [y; S],
T = y + βS,
A0A1 = a [T; γT+ΔS].
```

The highest-risk Lean step is proving the chart integral bound cleanly over the argmax image: cover up to null, injectivity off `{a = 0}`, Jacobian `|a|^8`, and converting the sheared target boxes to enlarged boxes consumable by a scaled `resolved334_lt_top`.

Everything after that is standard: `∫ |a|^(8-2c') < ∞`, bounded `β,γ` spectators, uniform Frobenius comparability, and the banked resolved integral.
### Q1 — TERMINAL-ENCODING FIDELITY

[PROVEN from the defs] Since `Fin 1` has one element, terminal `StepInv` reduces to
\[
(F_i\circ g)(u)=q_{i0}(u)b(u).
\]
Thus it exactly supplies terminal divisibility; the cleared-pivot hypothesis supplies one generator equal to `b · unit`.

[PROVEN from the defs] It does not encode the indices `S`, `L`, or `J`, nor the pivot’s algorithmic provenance. It is an algebraic terminal certificate applicable anywhere its hypotheses happen to hold. Also, `∀ i₀ unit, …` does not assert that a pivot exists; L5 must provide `i₀` and `unit`.

[PROVEN from the defs] It is stronger than the bare phrase `S=L ∧ J≥1`: it additionally requires openness, origin membership, continuous cofactors, equality on all of `V`, and `(F_i∘g)(0)=0`.

[INFERENCE] It faithfully matches the informal certificate if those conditions are already part of the maintained invariant and “bare diagonal entry” means exactly one generator `(F i₀ ∘ g)`, not merely a linear combination or germ.

### Q2 — SOUNDNESS

[PROVEN from the defs] Theorem 1 is true. On
\[
V'=\{u\in V\mid unit(u)\ne0\},
\]
relative continuity of `unit` makes `V'` open because `V` is open. Define `r i₀=unit⁻¹` and all other `r_i=0`. The singleton StepInv sum gives divisibility, while
\[
unit^{-1}(F_{i₀}\circ g)=unit^{-1}b\,unit=b
\]
on `V'`.

[PROVEN from the defs] At zero,
\[
0=(F_{i₀}\circ g)(0)=b(0)unit(0),
\]
so `unit(0) ≠ 0` forces `b(0)=0`. This is consistent, and indeed necessary for Bézout at zero because all `(F_i∘g)(0)` vanish. It does not make the theorem false.

[PROVEN from the defs] The basepoint-vanishing conjunct of `StepInv` is not needed to prove the conclusion; it is an invariant-strength hypothesis.

[PROVEN from the defs] Global openness of `V` is stronger than necessary, but some neighborhood condition is essential. Without it, take `D=M=1`, `V={0}`, `F₀≡b≡q≡0`, and `unit≡1`. Every other hypothesis holds, but no open `V'⊆{0}` contains zero.

[PROVEN from the defs] Theorem 2 is true: use `a i _ := q i` for the first representation and `a _ j := r j` for the second; both equations follow by collapsing the `Fin 1` sums.

### Q3 — VACUITY / TRIVIAL SATISFIABILITY

[PROVEN from the defs] `PrincipalInv` is vacuous on `V=∅`, since all its conditions are restricted to `V`. Theorem 1 excludes this: its resulting `V'` contains zero.

[PROVEN from the defs] There is a degenerate but sound zero-ideal case. For `D=M=1`, take `V=ℝ`, `F₀≡b≡q≡0`, and `unit≡1`. All Theorem 1 hypotheses hold and `PrincipalInv` expresses equality of two zero ideals.

[PROVEN from the defs] More generally, `b≡0` does not conceal nonzero generators: divisibility forces every `(F_i∘g)` to vanish on `V`.

[PROVEN from the defs] If `M=0`, Theorem 1’s `∀ i₀ : Fin M` branch is vacuous and cannot be consumed. For `PrincipalInv`, Bézout then forces `b=0` on `V` because the sum is empty. `M=1` and `D=1` themselves cause no vacuity.

### Q4 — CIRCULARITY

[PROVEN from the defs] Theorem 2 is not an `rfl` alias. `PrincipalInv` contains explicit `q,r`, while each `RegionRepresents` existentially packages a two-index coefficient family; witnesses must be constructed and singleton sums simplified.

[PROVEN from the defs] Nevertheless, it is a content-light interface conversion. Conversely, the two representations would recover `q_i=a_{i0}` and `r_j=a_{0j}`, so over `Fin 1` the notions are propositionally equivalent, not definitionally identical.

### Q5 — CONSUMER FIT

[PROVEN from the defs] The shapes wire correctly provided L5 supplies:

- the literal `Fin 1` residual equal to `1`;
- `q : Fin M → Fin 1 → …`;
- an actual `i₀ : Fin M`;
- equality `(F i₀ ∘ g)=b·unit` throughout the current `V`;
- continuity of `unit`, `unit 0≠0`, openness of `V`, and `0∈V`.

The resulting principal cofactor is exactly `fun i ↦ q i 0`.

[PROVEN from the defs] Setting the leaf region to `V'` composes with Theorem 2: it produces both representations on that same open neighborhood, and `V'⊆V` preserves all universally quantified identities and continuity restrictions.

[INFERENCE] Whether the actual fold retains these witnesses cannot be established without its definition. Wiring fails if it knows only `J≥1`, has merely a pivot linear combination/germ, or has a one-element residual indexed by a type not already identified with `Fin 1`.